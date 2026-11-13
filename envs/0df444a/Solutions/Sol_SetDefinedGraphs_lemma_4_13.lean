-- Prove2me | solution 1 for SetDefinedGraphs.lemma_4_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:50.885651+00:00
-- url     : https://prove2.me/submissions/31e70f1d-cbea-47fb-97cb-a665e7174837

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_ShiftDigraph

section
set_option autoImplicit false
namespace SetDefinedGraphs.Dev.L413
open SetDefinedGraphs

theorem omega_le_two {W : Type} (G : Digraph W) (p q : W → ℕ) (h1 : ∀ w, p w < q w)
    (h2 : ∀ a b, G.Adj a b → q a = p b) : omega G ≤ 2 := by
  classical
  obtain ⟨s, hs⟩ := (SimpleGraph.fromRel G.Adj).exists_isNClique_cliqueNum
  by_contra hlt
  push_neg at hlt
  have h3 : 3 ≤ s.card := by rw [hs.card_eq]; exact hlt
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq h3
  have ht : (SimpleGraph.fromRel G.Adj).IsNClique 3 t :=
    ⟨hs.isClique.subset (by exact_mod_cast hts), htc⟩
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.1 ht
  rw [SimpleGraph.fromRel_adj] at hab hac hbc
  have pa := h1 a
  have pb := h1 b
  have pc := h1 c
  rcases hab.2 with k1 | k1 <;> rcases hac.2 with k2 | k2 <;> rcases hbc.2 with k3 | k3 <;>
    (have e1 := h2 _ _ k1; have e2 := h2 _ _ k2; have e3 := h2 _ _ k3; omega)

theorem main {d : ℕ} (P : FullClause (Fin d)) (hP : IsPathClause P) {W : Type} (G : Digraph W)
    (hG : InY (dnfFun {P}) G) : IsShiftColorable G ∧ omega G ≤ 2 := by
  classical
  obtain ⟨V, hVfin, hVinj, hVou, e, he⟩ := hG
  obtain ⟨x, y, hxy, hPxy⟩ := hP.2.2
  have harc : ∀ u w : ↥V, (realisation (dnfFun {P}) V).Adj u w → u.1 x = w.1 y := by
    intro u w h
    have h2 := h.2
    simp only [dnfFun, Finset.mem_singleton, decide_eq_true_eq] at h2
    have := congrFun (congrFun h2 x) y
    rw [hPxy] at this
    simpa [eqPattern] using this
  obtain ⟨B, hB⟩ := hVfin.bddAbove
  obtain ⟨M, hM⟩ : ∃ M, ∀ u ∈ V, ∀ i, u i < M := by
    refine ⟨Finset.univ.sup B + 1, fun u hu i => ?_⟩
    have h1 : u i ≤ B i := hB hu i
    have h2 : B i ≤ Finset.univ.sup B := Finset.le_sup (f := B) (Finset.mem_univ i)
    omega
  have hne : ∀ u ∈ V, u x ≠ u y := fun u hu h => hxy (hVinj u hu h)
  have hcase : (∀ u ∈ V, u y < u x) ∨ (∀ u ∈ V, u x < u y) := by
    by_cases h : ∀ u ∈ V, u y < u x
    · exact Or.inl h
    · right
      push_neg at h
      obtain ⟨u0, hu0, h0⟩ := h
      have h0' : u0 x < u0 y := lt_of_le_of_ne h0 (hne u0 hu0)
      intro u hu
      exact (hVou u0 hu0 u hu x y).1 h0'
  obtain ⟨p, q, hpq, hqM, hadj⟩ : ∃ p q : ↥V → ℕ, (∀ u, p u < q u) ∧ (∀ u, q u < M) ∧
      ∀ u w, (realisation (dnfFun {P}) V).Adj u w → q u = p w := by
    rcases hcase with hc | hc
    · refine ⟨fun u => u.1 y, fun u => u.1 x, fun u => hc u.1 u.2, fun u => hM u.1 u.2 x, ?_⟩
      intro u w h
      exact harc u w h
    · refine ⟨fun u => M - 1 - u.1 y, fun u => M - 1 - u.1 x, ?_, ?_, ?_⟩
      · intro u
        show M - 1 - u.1 y < M - 1 - u.1 x
        have := hc u.1 u.2
        have := hM u.1 u.2 y
        have := hM u.1 u.2 x
        omega
      · intro u
        show M - 1 - u.1 x < M
        have := hM u.1 u.2 x
        omega
      · intro u w h
        have := harc u w h
        show M - 1 - u.1 x = M - 1 - w.1 y
        rw [this]
  have hG' : ∀ a b, G.Adj a b → (e a).1 x = (e b).1 y := fun a b h => harc _ _ ((he a b).1 h)
  have hadjG : ∀ a b, G.Adj a b → q (e a) = p (e b) := fun a b h => hadj _ _ ((he a b).1 h)
  have hsm : ∀ w : W, StrictMono (![(⟨p (e w), lt_trans (hpq _) (hqM _)⟩ : Fin M),
      ⟨q (e w), hqM _⟩] : Fin 2 → Fin M) := by
    intro w
    refine Fin.strictMono_iff_lt_succ.2 (fun i => ?_)
    fin_cases i
    simpa [Fin.lt_def] using hpq (e w)
  refine ⟨⟨M, fun w => ⟨_, hsm w⟩, ?_⟩,
    omega_le_two G (fun w => p (e w)) (fun w => q (e w)) (fun w => hpq _) hadjG⟩
  intro a b h i j hij
  have := hadjG a b h
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  exact this
end SetDefinedGraphs.Dev.L413
namespace SetDefinedGraphs
open SetDefinedGraphs.Dev.L413 in
theorem chk_lemma_4_13 {d : ℕ} (P : FullClause (Fin d)) (hP : IsPathClause P) {W : Type} (G : Digraph W)
    (hG : InY (dnfFun {P}) G) : IsShiftColorable G ∧ omega G ≤ 2 :=
  main P hP G hG
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_lemma_4_13 := @SetDefinedGraphs.chk_lemma_4_13
