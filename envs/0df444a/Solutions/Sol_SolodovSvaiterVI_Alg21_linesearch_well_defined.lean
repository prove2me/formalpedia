-- Prove2me | solution 1 for SolodovSvaiterVI.Alg21.linesearch_well_defined
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:25:07.365226+00:00
-- url     : https://prove2.me/submissions/6db891ea-8e01-4a34-864a-1ef4a2628ef6

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_ArmijoHolds
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

private theorem residual_bound {n : ℕ}
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

theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCc : IsClosed C) (hCcv : Convex ℝ C)
    (hF : Continuous F) (gamma sigma : ℝ) (hγ0 : 0 < gamma) (hγ1 : gamma < 1)
    (hσ0 : 0 < sigma) (hσ1 : sigma < 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ C) (hr : residual F C x ≠ 0) :
    ∃ k : ℕ, ArmijoHolds F C gamma sigma x k := by
  have hb := residual_bound F C hCc hCcv x hx
  have hnorm : 0 < ‖residual F C x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hr)
  have hstrict : sigma * ‖residual F C x‖ ^ 2 < ⟪F x, residual F C x⟫_ℝ := by
    nlinarith
  have hz : Filter.Tendsto (fun k : ℕ => x - gamma ^ k • residual F C x)
      Filter.atTop (nhds x) := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0.le hγ1).smul_const (residual F C x)
    simpa using tendsto_const_nhds.sub ht
  have hi : Filter.Tendsto (fun k : ℕ => ⟪F (x - gamma ^ k • residual F C x), residual F C x⟫_ℝ)
      Filter.atTop (nhds ⟪F x, residual F C x⟫_ℝ) := (hF.continuousAt.tendsto.comp hz).inner
    (tendsto_const_nhds (x := residual F C x))
  exact (Filter.Tendsto.eventually_const_le hstrict hi).exists
