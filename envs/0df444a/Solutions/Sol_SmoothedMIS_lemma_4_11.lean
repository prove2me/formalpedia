-- Prove2me | solution 1 for SmoothedMIS.lemma_4_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:28:54.558202+00:00
-- url     : https://prove2.me/submissions/12a4b20b-09b2-4eac-ba39-bde1382a09cf

import Mathlib
import Definitions.Def_SmoothedMIS_testSet

open SmoothedMIS in
theorem solution (n : ℕ) (β a : ℝ) (G : SimpleGraph (Fin n)) (ω : Coins n) (h v : Fin n) :
    EventE β G ω.1 → h ∈ Vhi β G ω.1 → v ∈ testSet a G ω h → RobustSuccess G ω h v →
      v ∈ helpers β G ω ∧ h ∉ activeSet β G ω := by
  intro hE hh hv hR
  set G' := addSmooth G ω.1 with hG'
  -- adjacency in the smoothed graph
  have hadj : ∀ x y, G'.Adj x y ↔ G.Adj x y ∨ Radj G ω.1 x y := by
    intro x y
    simp only [hG', addSmooth, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj,
      Set.mem_setOf_eq, Radj]
    constructor
    · rintro (h1 | ⟨h1, h2⟩)
      · exact Or.inl h1
      · by_cases hg : G.Adj x y
        · exact Or.inl hg
        · exact Or.inr ⟨h2, hg, h1⟩
    · rintro (h1 | ⟨h1, h2, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h3, h1⟩
  have hRsymm : ∀ x y, Radj G ω.1 x y → Radj G ω.1 y x := by
    rintro x y ⟨h1, h2, h3⟩
    refine ⟨Ne.symm h1, fun h4 => h2 h4.symm, ?_⟩
    rw [Sym2.eq_swap]; exact h3
  -- degree bound
  have hdeg : ∀ x, (deg G' x : ℝ) ≤ deg G x + 2 * lam n β := by
    intro x
    have hsub : G'.neighborSet x ⊆ G.neighborSet x ∪ {u | Radj G ω.1 x u} := by
      intro y hy
      rw [SimpleGraph.mem_neighborSet, hadj] at hy
      rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr hy
    have h1 : (G'.neighborSet x).ncard ≤ (G.neighborSet x).ncard + {u | Radj G ω.1 x u}.ncard :=
      (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
    have h2 := hE x
    unfold deg
    have h1' : ((G'.neighborSet x).ncard : ℝ) ≤
        ((G.neighborSet x).ncard : ℝ) + ({u | Radj G ω.1 x u}.ncard : ℝ) := by exact_mod_cast h1
    linarith
  -- high-degree vertices of the smoothed graph are high-degree in G
  have hVH : ∀ x, x ∈ Vhi β G ω.1 → x ∈ H0 G := by
    intro x hx
    simp only [Vhi, Set.mem_setOf_eq] at hx
    simp only [H0, Set.mem_setOf_eq]
    have := hdeg x
    unfold Bthr at hx
    have : (B0 n : ℝ) < deg G x := by linarith
    exact_mod_cast this
  -- unpack the hypotheses on v
  simp only [testSet, sample, pool, Set.mem_setOf_eq, Set.mem_diff, Set.mem_union] at hv
  obtain ⟨⟨hvL0, hvX0, hInd⟩, ⟨_, hvnot⟩, hiso⟩ := hv
  push_neg at hvnot
  obtain ⟨hvX0p, _⟩ := hvnot
  obtain ⟨hRhv, hω2⟩ := hInd
  obtain ⟨hR1, hR2⟩ := hR
  -- v is low in the smoothed graph
  have hvlo : v ∈ Vlo β G ω.1 := by
    simp only [Vlo, Vhi, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    have h1 := hdeg v
    simp only [L0, H0, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hvL0
    have h2 : (deg G v : ℝ) ≤ B0 n := by exact_mod_cast hvL0
    unfold Bthr
    linarith
  have hhv : G'.Adj h v := (hadj h v).mpr (Or.inr hRhv)
  have hcand : v ∈ candidates β G ω := ⟨hvlo, h, hhv, hh, hvlo, hω2⟩
  -- any smoothed neighbour w of v lies in L0 and is adjacent to v in F0
  have hnbr : ∀ w, G'.Adj v w → w ∉ Vhi β G ω.1 → w ∈ L0 G ∧ (F0 G ω.1).Adj v w := by
    intro w hvw hwhi
    have hwL0 : w ∈ L0 G := by
      intro hwH
      rcases (hadj v w).mp hvw with hg | hr
      · exact hvX0 ⟨hvL0, w, hwH, hg⟩
      · have hwh : w ≠ h := by rintro rfl; exact hwhi hh
        exact hR1 w hwH hwh (hRsymm v w hr)
    refine ⟨hwL0, ?_⟩
    simp only [F0, onL0, SimpleGraph.fromRel_adj]
    exact ⟨G'.ne_of_adj hvw, Or.inl ⟨hvw, hvL0, hwL0⟩⟩
  have hhelp : v ∈ helpers β G ω := by
    refine ⟨hcand, ?_⟩
    intro w hvw hwc
    obtain ⟨hwlo, u, huw, hu, _, hωuw⟩ := hwc
    have hwhi : w ∉ Vhi β G ω.1 := hwlo
    obtain ⟨hwL0, hF0vw⟩ := hnbr w hvw hwhi
    have huH := hVH u hu
    -- if w is G-adjacent to a high vertex, then v ∈ X0plus
    have hX0case : w ∈ X0 G → False := by
      intro hwX
      apply hvX0p
      exact Or.inr ⟨w, hwX, hF0vw⟩
    rcases (hadj u w).mp huw with hg | hr
    · exact hX0case ⟨hwL0, u, huH, hg.symm⟩
    · by_cases huh : u = h
      · subst huh
        have hws : w ∈ sample G ω u := ⟨hwL0, hX0case, hr, hωuw⟩
        have hwv : w ≠ v := fun e => G'.ne_of_adj hvw e.symm
        have := hiso w hws hwv
        rw [SimpleGraph.edist_eq_one_iff_adj.mpr hF0vw.symm] at this
        norm_num at this
      · exact hR2 w hF0vw u huH huh ⟨hr, hωuw⟩
  refine ⟨hhelp, ?_⟩
  intro hact
  simp only [activeSet, Set.mem_diff] at hact
  apply hact.2
  exact Or.inr ⟨v, hhelp, hhv⟩
