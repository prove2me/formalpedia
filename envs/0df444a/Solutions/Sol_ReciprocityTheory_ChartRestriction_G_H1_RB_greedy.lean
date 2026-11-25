-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.RB.greedy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:14.107898+00:00
-- url     : https://prove2.me/submissions/6d6ab96a-654c-4846-80db-3da91568f4b3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IndepOfFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SpanFlag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_RB_finite_ball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.RB
open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace ReciprocityTheory.ChartRestriction.G.H1.RB
theorem _root_.solution [FiniteDimensional ℝ E] (X : Submodule ℤ E) [DiscreteTopology X] {d : ℕ}
    (v : Fin d → E) (hv : LinearIndependent ℝ v) (hvX : ∀ i, v i ∈ X) :
    ∃ u : Fin d → E, ∀ k : Fin d, u k ∈ X ∧ u k ∉ V u k.val ∧ (∃ i, ‖u k‖ ≤ ‖v i‖) ∧
      ∀ z ∈ X, z ∉ V u k.val → ‖u k‖ ≤ ‖z‖ := by
  classical
  have hstep : ∀ (u : Fin d → E) (n : ℕ), n < d → ∃ w ∈ X, w ∉ V u n ∧ (∃ i, ‖w‖ ≤ ‖v i‖) ∧
      ∀ z ∈ X, z ∉ V u n → ‖w‖ ≤ ‖z‖ := by
    intro u n hn
    have hex : ∃ i, v i ∉ V u n := by
      by_contra h
      push_neg at h
      have hle : span ℝ (Set.range v) ≤ V u n :=
        span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
      have h1 : finrank ℝ (span ℝ (Set.range v)) = d := by
        rw [finrank_span_eq_card hv, Fintype.card_fin]
      have h2 : finrank ℝ (V u n) ≤ n := by
        have hV : V u n = span ℝ (Set.range (fun i : Fin n => u (Fin.castLE hn.le i))) := by
          unfold V
          congr 1
          ext x
          simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
          constructor
          · rintro ⟨l, hl, rfl⟩
            exact ⟨⟨l.val, hl⟩, rfl⟩
          · rintro ⟨i, rfl⟩
            exact ⟨Fin.castLE hn.le i, i.isLt, rfl⟩
        rw [hV]
        exact (finrank_range_le_card _).trans (by simp)
      have h3 := Submodule.finrank_mono hle
      omega
    obtain ⟨i0, hi0⟩ := hex
    have hAfin : {z : E | z ∈ X ∧ z ∉ V u n ∧ ‖z‖ ≤ ‖v i0‖}.Finite :=
      (finite_ball X ‖v i0‖).subset (by
        rintro z ⟨hzX, -, hz⟩
        exact ⟨mem_closedBall_zero_iff.mpr hz, hzX⟩)
    obtain ⟨w, ⟨hwX, hwV, hwle⟩, hwmin⟩ :=
      Set.exists_min_image _ (fun z => ‖z‖) hAfin ⟨v i0, hvX i0, hi0, le_rfl⟩
    refine ⟨w, hwX, hwV, ⟨i0, hwle⟩, fun z hzX hzV => ?_⟩
    by_cases hz : ‖z‖ ≤ ‖v i0‖
    · exact hwmin z ⟨hzX, hzV, hz⟩
    · exact hwle.trans (le_of_not_ge hz)
  have hVupd : ∀ (u : Fin d → E) (i : Fin d) (w : E) (n : ℕ), n ≤ i.val →
      V (Function.update u i w) n = V u n := by
    intro u i w n hn
    unfold V
    congr 1
    apply Set.image_congr
    intro l hl
    have hli : l ≠ i := by
      intro h
      subst h
      simp only [Set.mem_setOf_eq] at hl
      omega
    simp [Function.update_of_ne hli]
  have key : ∀ n ≤ d, ∃ u : Fin d → E, ∀ k : Fin d, k.val < n → (u k ∈ X ∧ u k ∉ V u k.val ∧
      (∃ i, ‖u k‖ ≤ ‖v i‖) ∧ ∀ z ∈ X, z ∉ V u k.val → ‖u k‖ ≤ ‖z‖) := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨fun _ => 0, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro hn
      obtain ⟨u, hu⟩ := ih (by omega)
      obtain ⟨w, hw⟩ := hstep u n (by omega)
      refine ⟨Function.update u ⟨n, by omega⟩ w, fun k hk => ?_⟩
      rw [hVupd u ⟨n, by omega⟩ w k.val (by show k.val ≤ n; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · have hki : k ≠ ⟨n, by omega⟩ := by
          intro h
          rw [h] at hk
          exact lt_irrefl _ hk
        rw [Function.update_of_ne hki]
        exact hu k hk
      · have hki : k = ⟨n, by omega⟩ := Fin.ext hk
        rw [hki, Function.update_self]
        exact hw
  obtain ⟨u, hu⟩ := key d le_rfl
  exact ⟨u, fun k => hu k k.isLt⟩
end ReciprocityTheory.ChartRestriction.G.H1.RB
