-- Prove2me | solution 1 for SolodovSvaiterVI.Alg21.eq2_5_inner_residual_ge
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:22:10.714244+00:00
-- url     : https://prove2.me/submissions/f5ccb899-e1b2-46af-9ef8-a80513d02b05

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_residual
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
open scoped InnerProductSpace
open SolodovSvaiterVI.Alg21

private theorem projection_spec {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hne : C.Nonempty) (hc : IsClosed C) (hcv : Convex ℝ C)
    (x : EuclideanSpace ℝ (Fin n)) :
    projOnto C x ∈ C ∧ ∀ y ∈ C, ⟪x - projOnto C x, y - projOnto C x⟫_ℝ ≤ 0 := by
  letI : Nonempty C := hne.to_subtype
  have hb : BddBelow (Set.range (fun y : C => ‖x - y‖)) := ⟨0, by
    rintro _ ⟨y, rfl⟩
    exact norm_nonneg _⟩
  have he : ∃ p ∈ C, ∀ y ∈ C, ‖x - p‖ ≤ ‖x - y‖ := by
    obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hcv x
    refine ⟨p, hp, ?_⟩
    intro y hy
    rw [hmin]
    exact ciInf_le hb ⟨y, hy⟩
  have hp : projOnto C x ∈ C ∧ ∀ y ∈ C, ‖x - projOnto C x‖ ≤ ‖x - y‖ := by
    simpa only [projOnto, dif_pos he] using Classical.choose_spec he
  refine ⟨hp.1, (norm_eq_iInf_iff_real_inner_le_zero hcv hp.1).mp ?_⟩
  exact le_antisymm (le_ciInf (fun y => hp.2 y y.2))
    (ciInf_le hb ⟨_, hp.1⟩)

theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCc : IsClosed C) (hCcv : Convex ℝ C)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ C) :
    ‖residual F C x‖ ^ 2 ≤ ⟪F x, residual F C x⟫_ℝ := by
  have hp := (projection_spec C ⟨x, hx⟩ hCc hCcv (x - F x)).2 x hx
  have he : x - F x - projOnto C (x - F x) = residual F C x - F x := by
    unfold SolodovSvaiterVI.Alg21.residual
    abel
  rw [he] at hp
  change ⟪residual F C x - F x, residual F C x⟫_ℝ ≤ 0 at hp
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at hp
  linarith
