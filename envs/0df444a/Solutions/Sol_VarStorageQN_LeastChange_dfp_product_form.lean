-- Prove2me | solution 1 for VarStorageQN.LeastChange.dfp_product_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:32:24.573988+00:00
-- url     : https://prove2.me/submissions/b3aa4773-f1cf-4249-9041-43aa81632e81

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_Bracket

set_option autoImplicit false
open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace
open VarStorageQN.LeastChange

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem solution (B : H →L[ℝ] H) (hB : IsSelfAdjoint B) (y s : H) :
    let a := ⟪y, s⟫_ℝ
    let r := y - B s
    let Bdfp : H →L[ℝ] H :=
      B + a⁻¹ • (bracket r y + bracket y r) - (⟪r, s⟫_ℝ / a ^ 2) • bracket y y
    (a ≠ 0 →
      Bdfp = (1 - a⁻¹ • bracket y s) ∘L B ∘L (1 - a⁻¹ • bracket s y) + a⁻¹ • bracket y y) ∧
    (IsPositiveStrict B → 0 < a → IsSelfAdjoint Bdfp ∧ IsPositiveStrict Bdfp) := by
  intro a r Bdfp
  have hsym : ∀ x z : H, ⟪B x, z⟫_ℝ = ⟪x, B z⟫_ℝ :=
    fun x z => (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB) x z
  have sym2 : ∀ u v : H, ⟪B u, v⟫_ℝ = ⟪B v, u⟫_ℝ := fun u v => by
    rw [hsym, real_inner_comm]
  have key : a ≠ 0 →
      Bdfp = (1 - a⁻¹ • bracket y s) ∘L B ∘L (1 - a⁻¹ • bracket s y) + a⁻¹ • bracket y y := by
    intro ha
    ext d
    simp only [Bdfp, r, bracket, rankOne_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, one_apply_eq_self, map_sub, map_smul,
      map_add, inner_sub_left, inner_smul_right, inner_sub_right, inner_add_right, smul_sub,
      smul_add, smul_smul, sub_smul, add_smul]
    have h1 : ⟪s, B d⟫_ℝ = ⟪B s, d⟫_ℝ := (hsym s d).symm
    have e2 : ⟪s, B s⟫_ℝ = ⟪B s, s⟫_ℝ := real_inner_comm _ _
    have e3 : ⟪y, s⟫_ℝ = a := rfl
    rw [h1, e2, e3]
    match_scalars <;> field_simp <;> ring
  refine ⟨key, ?_⟩
  intro hpos ha
  have ha0 : a ≠ 0 := ha.ne'
  have hk := key ha0
  -- the quadratic form identity
  have hq : ∀ d e : H, ⟪Bdfp d, e⟫_ℝ =
      ⟪B (d - (a⁻¹ * ⟪y, d⟫_ℝ) • s), e - (a⁻¹ * ⟪y, e⟫_ℝ) • s⟫_ℝ + a⁻¹ * (⟪y, d⟫_ℝ * ⟪y, e⟫_ℝ) := by
    intro d e
    rw [hk]
    simp only [bracket, rankOne_apply, add_apply, sub_apply, smul_apply, comp_apply,
      one_apply_eq_self, map_sub, map_smul, inner_add_left, inner_sub_left, inner_smul_left,
      inner_sub_right, inner_smul_right, RCLike.conj_to_real]
    have e1 : ⟪s, B d⟫_ℝ = ⟪B s, d⟫_ℝ := (hsym s d).symm
    have e2 : ⟪B d, s⟫_ℝ = ⟪B s, d⟫_ℝ := by rw [real_inner_comm, e1]
    have e3 : ⟪s, B s⟫_ℝ = ⟪B s, s⟫_ℝ := real_inner_comm _ _
    rw [e1, e2, e3]
    ring
  have hsa : IsSelfAdjoint Bdfp := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro d e
    show ⟪Bdfp d, e⟫_ℝ = ⟪d, Bdfp e⟫_ℝ
    rw [hq d e, ← real_inner_comm d (Bdfp e), hq e d,
      sym2 (e - (a⁻¹ * ⟪y, e⟫_ℝ) • s) (d - (a⁻¹ * ⟪y, d⟫_ℝ) • s), mul_comm (⟪y, e⟫_ℝ)]
  refine ⟨hsa, ?_⟩
  intro d hd
  rw [hq d d]
  set d' := d - (a⁻¹ * ⟪y, d⟫_ℝ) • s with hd'
  have hnn : 0 ≤ a⁻¹ * (⟪y, d⟫_ℝ * ⟪y, d⟫_ℝ) := by
    have : 0 ≤ ⟪y, d⟫_ℝ * ⟪y, d⟫_ℝ := mul_self_nonneg _
    positivity
  by_cases h0 : d' = 0
  · have hyd : ⟪y, d⟫_ℝ ≠ 0 := by
      intro hz
      apply hd
      rw [hd', hz] at h0
      simpa using h0
    have : 0 < a⁻¹ * (⟪y, d⟫_ℝ * ⟪y, d⟫_ℝ) := by
      have : 0 < ⟪y, d⟫_ℝ * ⟪y, d⟫_ℝ := mul_self_pos.mpr hyd
      positivity
    rw [h0] at *
    simp only [map_zero, inner_zero_left, zero_add]
    exact this
  · have := hpos d' h0
    linarith
