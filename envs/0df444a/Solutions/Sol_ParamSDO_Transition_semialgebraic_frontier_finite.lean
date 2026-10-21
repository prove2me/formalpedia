-- Prove2me | solution 1 for ParamSDO.Transition.semialgebraic_frontier_finite
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:19:36.986976+00:00
-- url     : https://prove2.me/submissions/02d7787c-aec8-40b6-9bb7-e5965409776e

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

open ParamSDO.Transition

/-- A one-variable `MvPolynomial` viewed as a `Polynomial`. -/
noncomputable def psdoToPoly1 (f : MvPolynomial (Fin 1) ℝ) : Polynomial ℝ :=
  Polynomial.map (MvPolynomial.eval (Fin.elim0 : Fin 0 → ℝ)) (MvPolynomial.finSuccEquiv ℝ 0 f)

lemma psdo_eval_toPoly1 (f : MvPolynomial (Fin 1) ℝ) (x : ℝ) :
    MvPolynomial.eval (fun _ : Fin 1 => x) f = (psdoToPoly1 f).eval x := by
  have h := MvPolynomial.eval_eq_eval_mv_eval' (Fin.elim0 : Fin 0 → ℝ) x f
  have hx : (Fin.cons x (Fin.elim0 : Fin 0 → ℝ) : Fin 1 → ℝ) = fun _ => x := by
    funext i; fin_cases i; rfl
  rw [hx] at h
  exact h

lemma psdo_ev_loc (q : Polynomial ℝ) (x : ℝ) (h : q = 0 ∨ q.eval x ≠ 0) :
    ∀ᶠ y in nhds x, (q.eval y = 0 ↔ q.eval x = 0) ∧ (q.eval y < 0 ↔ q.eval x < 0) := by
  rcases h with rfl | h
  · simp
  · have hc : Continuous fun y => q.eval y := q.continuous
    rcases lt_or_gt_of_ne h with hlt | hgt
    · filter_upwards [hc.continuousAt.eventually_lt continuousAt_const hlt] with y hy
      constructor <;> constructor <;> intro h' <;> linarith
    · filter_upwards [continuousAt_const.eventually_lt hc.continuousAt hgt] with y hy
      constructor <;> constructor <;> intro h' <;> linarith

theorem solution :
    ∀ T : Set ℝ, IsSemialgebraicReal T → (frontier T).Finite := by
  classical
  rintro T ⟨K, eqs, lts, hS⟩
  have hT : ∀ x, x ∈ T ↔ ∃ i, (∀ p ∈ eqs i, (psdoToPoly1 p).eval x = 0) ∧
      ∀ g ∈ lts i, (psdoToPoly1 g).eval x < 0 := by
    intro x
    have := congrArg (fun S => (fun _ : Fin 1 => x) ∈ S) hS
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, eq_iff_iff,
      psdo_eval_toPoly1] at this
    exact this
  let P : Finset (MvPolynomial (Fin 1) ℝ) := Finset.univ.biUnion (fun i => eqs i ∪ lts i)
  let Z : Set ℝ := ⋃ p ∈ P, {x | psdoToPoly1 p ≠ 0 ∧ (psdoToPoly1 p).IsRoot x}
  have hZ : Z.Finite := by
    refine Set.Finite.biUnion P.finite_toSet fun p _ => ?_
    by_cases hp : psdoToPoly1 p = 0
    · simp [hp]
    · exact (Polynomial.finite_setOfPred_isRoot hp).subset fun x hx => hx.2
  refine hZ.subset fun x hx => ?_
  by_contra hxZ
  have hloc : ∀ p ∈ P, ∀ᶠ y in nhds x,
      ((psdoToPoly1 p).eval y = 0 ↔ (psdoToPoly1 p).eval x = 0) ∧
        ((psdoToPoly1 p).eval y < 0 ↔ (psdoToPoly1 p).eval x < 0) := by
    intro p hp
    apply psdo_ev_loc
    by_contra hcon
    push_neg at hcon
    exact hxZ (Set.mem_biUnion (Finset.mem_coe.2 hp) ⟨hcon.1, hcon.2⟩)
  rw [← Filter.eventually_all_finset] at hloc
  have hev : ∀ᶠ y in nhds x, (y ∈ T ↔ x ∈ T) := by
    filter_upwards [hloc] with y hy
    rw [hT, hT]
    apply exists_congr; intro i
    apply and_congr
    · apply forall₂_congr; intro p hp
      exact (hy p (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_union_left _ hp⟩)).1
    · apply forall₂_congr; intro g hg
      exact (hy g (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_union_right _ hg⟩)).2
  rw [frontier, Set.mem_diff] at hx
  by_cases hxT : x ∈ T
  · apply hx.2
    rw [mem_interior_iff_mem_nhds]
    filter_upwards [hev] with y hy
    exact hy.2 hxT
  · obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 hx.1 _ hev
    exact hxT (hy1.1 hy2)
