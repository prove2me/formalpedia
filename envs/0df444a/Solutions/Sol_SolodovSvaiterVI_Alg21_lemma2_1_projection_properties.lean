-- Prove2me | solution 1 for SolodovSvaiterVI.Alg21.lemma2_1_projection_properties
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:22:12.157973+00:00
-- url     : https://prove2.me/submissions/966676ab-1443-4833-b92f-1e0abac4d710

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

theorem solution {n : ℕ} (B : Set (EuclideanSpace ℝ (Fin n)))
    (hBne : B.Nonempty) (hBc : IsClosed B) (hBcv : Convex ℝ B)
    (x y z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ B) :
    ⟪x - projOnto B x, z - projOnto B x⟫_ℝ ≤ 0 ∧
      ‖projOnto B x - projOnto B y‖ ^ 2 ≤
        ‖x - y‖ ^ 2 - ‖projOnto B x - x + y - projOnto B y‖ ^ 2 := by
  obtain ⟨hpx, hix⟩ := projection_spec B hBne hBc hBcv x
  obtain ⟨hpy, hiy⟩ := projection_spec B hBne hBc hBcv y
  refine ⟨hix z hz, ?_⟩
  have h1 := hix (projOnto B y) hpy
  have h2 := hiy (projOnto B x) hpx
  simp only [inner_sub_left, inner_sub_right] at h1 h2
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right]
  simp only [real_inner_comm y x, real_inner_comm (projOnto B x) x,
    real_inner_comm (projOnto B y) x, real_inner_comm (projOnto B x) y,
    real_inner_comm (projOnto B y) y, real_inner_comm (projOnto B y) (projOnto B x)] at *
  linarith
