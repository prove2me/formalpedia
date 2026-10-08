-- Prove2me | solution 1 for StrongPerfectGraph.Main.complement_perfect
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T11:47:38.725166+00:00
-- url     : https://prove2.me/submissions/0f189f39-b8ae-4935-a670-6c8aa8b71101

/-
Lovász's weak perfect graph theorem (Chudnovsky–Robertson–Seymour–Thomas, 1.1):
the complement of a perfect graph is perfect.

Proof route. A perfect graph satisfies |A| ≤ α(G_A)·ω(G_A) for every induced subgraph (colour
classes are independent sets). By Lovász's first theorem (platform theorem
`ChvatalPolytopes.Perfect.exists_induced_indepNum_mul_cliqueNum_lt`) this forces
Chvátal-perfection of G, and a 0/1 clique cover of the weights 1_X yields a colouring of
the induced subgraph of Gᶜ with ω(Gᶜ[X]) colours.
-/
import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect
import Theorems.Thm_ChvatalPolytopes_Perfect_exists_induced_indepNum_mul_cliqueNum_lt

set_option autoImplicit false

namespace WPGT

/-- A graph colourable with `n` colours has at most `n * α` vertices. -/
theorem card_le_mul_indepNum {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) {n : ℕ}
    (hc : H.Colorable n) : Fintype.card W ≤ n * H.indepNum := by
  classical
  obtain ⟨C⟩ := hc
  have h1 : Fintype.card W =
      ∑ i : Fin n, (Finset.univ.filter (fun v => C v = i)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (f := C) (t := Finset.univ) (by simp)
  have h2 : ∀ i : Fin n, (Finset.univ.filter (fun v => C v = i)).card ≤ H.indepNum := by
    intro i
    apply SimpleGraph.IsIndepSet.card_le_indepNum
    intro a ha b hb hab hadj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
    exact C.valid hadj (ha.trans hb.symm)
  calc Fintype.card W = ∑ i : Fin n, (Finset.univ.filter (fun v => C v = i)).card := h1
    _ ≤ ∑ _i : Fin n, H.indepNum := Finset.sum_le_sum (fun i _ => h2 i)
    _ = n * H.indepNum := by simp


/-- In a perfect graph every induced subgraph has at most `α * ω` vertices. -/
theorem card_le_of_perfect {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : StrongPerfectGraph.Main.IsPerfect G) (A : Finset V) :
    A.card ≤ (G.induce (A : Set V)).indepNum * (G.induce (A : Set V)).cliqueNum := by
  classical
  have h := hG (A : Set V)
  have hcol : (G.induce (A : Set V)).Colorable (G.induce (A : Set V)).cliqueNum :=
    SimpleGraph.chromaticNumber_le_iff_colorable.mp h.le
  have := card_le_mul_indepNum (G.induce (A : Set V)) hcol
  rw [mul_comm] at this
  simpa using this

/-- Lovász: a perfect graph (`χ = ω` hereditarily) is Chvátal-perfect. -/
theorem chv_of_perfect {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : StrongPerfectGraph.Main.IsPerfect G) : ChvatalPolytopes.Perfect.IsPerfect G := by
  by_contra hnot
  obtain ⟨A, hA⟩ := ChvatalPolytopes.Perfect.exists_induced_indepNum_mul_cliqueNum_lt G hnot
  exact absurd (card_le_of_perfect G hG A) (not_le.mpr hA)


/-- Chvátal-perfection of `G` gives `χ = ω` on every induced subgraph of `Gᶜ`. -/
theorem perfect_compl_of_chv {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h : ChvatalPolytopes.Perfect.IsPerfect G) : StrongPerfectGraph.Main.IsPerfect Gᶜ := by
  classical
  intro X
  refine le_antisymm ?_ SimpleGraph.cliqueNum_le_chromaticNumber
  obtain ⟨m, ⟨⟨x, ⟨s, hs, rfl⟩, hxm⟩, _⟩, ⟨lam, hlam01, hcover, hsum⟩, _⟩ :=
    h (fun u => if u ∈ X then (1 : ℝ) else 0)
      (fun u => by by_cases hu : u ∈ X <;> simp [hu])
  set M := ChvatalPolytopes.Perfect.maximalCliques G with hM
  set S : Finset (Finset V) := M.filter (fun W => lam W = 1) with hS
  -- every vertex of `X` lies in a selected clique
  have hchoose : ∀ u : X, ∃ W ∈ S, (u : V) ∈ W := by
    intro u
    have hc := hcover u
    have hu : (u : V) ∈ X := u.2
    simp only [hu, if_true] at hc
    by_contra hno
    simp only [not_exists, not_and] at hno
    have hzero : ∑ W ∈ M.filter (fun W => (u : V) ∈ W), lam W = 0 := by
      apply Finset.sum_eq_zero
      intro W hW
      rw [Finset.mem_filter] at hW
      rcases hlam01 W hW.1 with h0 | h1
      · exact h0
      · exact absurd hW.2 (hno W (by simp [hS, hW.1, h1]))
    linarith
  choose f hfS hfmem using hchoose
  have hcol : (Gᶜ.induce X).Colorable (Fintype.card S) := by
    refine (SimpleGraph.Coloring.mk (fun u : X => (⟨f u, hfS u⟩ : S)) ?_).colorable
    intro u v huv hfuv
    have hfe : f u = f v := congrArg Subtype.val hfuv
    have hW : f u ∈ M := (Finset.mem_filter.mp (hfS u)).1
    have hclique := ((ChvatalPolytopes.Perfect.mem_maximalCliques G (f u)).mp hW).1
    have hu := hfmem u
    have hv : (v : V) ∈ f u := hfe ▸ hfmem v
    rw [SimpleGraph.induce_adj, SimpleGraph.compl_adj] at huv
    exact huv.2 (hclique hu hv huv.1)
  -- the number of selected cliques is `m`
  have hcard : ((S.card : ℕ) : ℝ) = m := by
    rw [← hsum, hS, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro W hW
    rcases hlam01 W hW with h0 | h1
    · simp [h0]
    · simp [h1]
  -- the maximum stable set gives a clique of the same size in the induced complement
  set t : Finset X := Finset.univ.filter (fun u : X => (u : V) ∈ s) with ht
  have htclique : (Gᶜ.induce X).IsClique (t : Set X) := by
    intro u hu v hv huv
    simp only [ht, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu hv
    rw [SimpleGraph.induce_adj, SimpleGraph.compl_adj]
    refine ⟨fun h => huv (Subtype.ext h), ?_⟩
    exact hs hu hv (fun h => huv (Subtype.ext h))
  have htcard : (t.card : ℝ) = m := by
    rw [← hxm]
    have : ∑ u : V, (if u ∈ X then (1 : ℝ) else 0) *
        ChvatalPolytopes.Perfect.incidenceVector s u =
        ((Finset.univ.filter (fun u : V => u ∈ X ∧ u ∈ s)).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      apply Finset.sum_congr rfl
      intro u _
      by_cases h1 : u ∈ X <;> by_cases h2 : u ∈ s <;>
        simp [ChvatalPolytopes.Perfect.incidenceVector, h1, h2]
    rw [this]
    congr 1
    apply Finset.card_bij (fun (u : X) _ => (u : V))
    · intro u hu
      simp only [ht, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      simp [hu, u.2]
    · intro u _ v _ h
      exact Subtype.ext h
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact ⟨⟨v, hv.1⟩, by simp [ht, hv.2], rfl⟩
  have hmω : S.card ≤ (Gᶜ.induce X).cliqueNum := by
    have h1 : S.card = t.card := by
      have : ((S.card : ℕ) : ℝ) = (t.card : ℝ) := by rw [hcard, htcard]
      exact_mod_cast this
    rw [h1]
    exact SimpleGraph.IsClique.card_le_cliqueNum (tc := htclique)
  have hle : (Gᶜ.induce X).chromaticNumber ≤ (S.card : ℕ∞) := by
    have := SimpleGraph.chromaticNumber_le_iff_colorable.mpr hcol
    simpa using this
  exact hle.trans (by exact_mod_cast hmω)


end WPGT

open StrongPerfectGraph.Main in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPerfect G) : IsPerfect Gᶜ :=
  WPGT.perfect_compl_of_chv G (WPGT.chv_of_perfect G hG)
