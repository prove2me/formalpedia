-- Prove2me | solution 1 for ProxMethodVI.Rate.lemma3_1_a_prox_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T02:49:34.562076+00:00
-- url     : https://prove2.me/submissions/c613a1b3-3457-4443-83e4-804122c33f14

import Definitions.Def_ProxMethodVI_Rate_Setting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
open ProxMethodVI.Rate

private theorem prox_vi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z U : Set E) (hUZ : U ⊆ Z) (hUc : Convex ℝ U)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ)
    (hω : ∀ x ∈ Z, HasFDerivWithinAt ω (ω' x) Z x)
    (z v u : E) (ξ : E →L[ℝ] ℝ) (hv : IsProxPt U ω ω' z ξ v) (hu : u ∈ U) :
    0 ≤ (ω' v + (ξ - ω' z)) (u - v) := by
  have hd : HasFDerivWithinAt (fun y => ω y + (ξ - ω' z) y)
      (ω' v + (ξ - ω' z)) U v :=
    ((hω v (hUZ hv.1)).mono hUZ).add (ξ - ω' z).hasFDerivAt.hasFDerivWithinAt
  have hmin : IsMinOn (fun y => ω y + (ξ - ω' z) y) U v := hv.2
  exact hmin.localize.hasFDerivWithinAt_nonneg hd
    (sub_mem_posTangentConeAt_of_segment_subset (hUc.segment_subset hv.1 hu))

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (U : Set E) (hUZ : U ⊆ Z) (hUne : U.Nonempty) (hUc : Convex ℝ U) (hUcl : IsClosed U)
    (z : E) (hz : z ∈ Z) (ξ η : E →L[ℝ] ℝ) (γ : ℝ) (hγ : 0 < γ)
    (w : E) (hw : IsProxPt U ω ω' z (γ • ξ) w)
    (zp : E) (hzp : IsProxPt U ω ω' z (γ • η) zp) :
    ‖w - zp‖ ≤ α⁻¹ * γ * ‖ξ - η‖ := by
  have hviw := prox_vi Z U hUZ hUc ω ω' hω.2.1 z w zp (γ • ξ) hw hzp.1
  have hviz := prox_vi Z U hUZ hUc ω ω' hω.2.1 z zp w (γ • η) hzp hw.1
  have hmono := hω.2.2.2 w (hUZ hw.1) zp (hUZ hzp.1)
  have hcore : α * ‖w - zp‖ ^ 2 ≤ γ * (η - ξ) (w - zp) := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub] at *
    linarith
  have hdual : (η - ξ) (w - zp) ≤ ‖ξ - η‖ * ‖w - zp‖ := by
    calc
      (η - ξ) (w - zp) ≤ |(η - ξ) (w - zp)| := le_abs_self _
      _ = ‖(η - ξ) (w - zp)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖η - ξ‖ * ‖w - zp‖ := (η - ξ).le_opNorm _
      _ = _ := by rw [norm_sub_rev]
  have hbound := hcore.trans (mul_le_mul_of_nonneg_left hdual hγ.le)
  by_cases hn : ‖w - zp‖ = 0
  · rw [hn]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hω.1.le) hγ.le) (norm_nonneg _)
  have hnp : 0 < ‖w - zp‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  have hlin : α * ‖w - zp‖ ≤ γ * ‖ξ - η‖ := by
    by_contra! hcontr
    have hmul := mul_lt_mul_of_pos_right hcontr hnp
    nlinarith only [hbound, hmul]
  calc
    ‖w - zp‖ = α⁻¹ * (α * ‖w - zp‖) := by field_simp [hω.1.ne']
    _ ≤ α⁻¹ * (γ * ‖ξ - η‖) := mul_le_mul_of_nonneg_left hlin (inv_nonneg.mpr hω.1.le)
    _ = _ := by ring

#print axioms solution
