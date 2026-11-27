-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.sup_ratio_le_of_phase_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:27:22.662928+00:00
-- url     : https://prove2.me/submissions/ad62643b-2f8d-4c4e-bcaa-c5d4338c4cdc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_column_mem_sections
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_pointNormSq_column
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_l2_one_eq_toGT_l2_col1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_card_idx
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_firstMinimum_toTorus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_firstMinimum_pos_bis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_threshold_le_firstMinimum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_one_le_sqrt_q_th
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hS : GSupStatement)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) (h0 : P.ph = 0) (a : Vsp X.dim) :
    Real.sqrt (X.ptN2 1 s fun _ => a) / Real.sqrt (X.l2 1 s) ≤ Real.exp P.p1 := by
  have hN : Fintype.card (Idx X.dim) = X.gA := X.card_idx
  have hth := threshold_le_firstMinimum P h0
  have hsq := one_le_sqrt_q_th P
  have hla : 0 < X.la1 := firstMinimum_pos_bis P
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hsqrtq : 0 < Real.sqrt P.q := Real.sqrt_pos.mpr hq
  have hB := hS (Idx X.dim) X.toGT 1 le_rfl (X.col1 s) (X.column_mem_sections hs) a
  rw [← X.pointNormSq_column, ← X.l2_one_eq_toGT_l2_col1, X.firstMinimum_toTorus, hN] at hB
  simp only [Nat.cast_one, one_pow, one_mul, mul_one] at hB
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 1 + 6 * Real.sqrt (X.gA * P.q) := ⟨_, rfl⟩
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hspi1 : 1 ≤ Real.sqrt Real.pi := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hs2 : Real.sqrt 2 ≤ 1.5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h1 : 1 ≤ Real.sqrt P.q * X.la1 :=
    le_trans hsq (mul_le_mul_of_nonneg_left hth hsqrtq.le)
  have hsN := Real.sqrt_nonneg (X.gA : ℝ)
  have hterm : 4 * Real.sqrt (2 * X.gA) / (Real.sqrt Real.pi * X.la1) ≤
      6 * Real.sqrt (X.gA * P.q) := by
    rw [div_le_iff₀ (mul_pos hspi hla), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_mul (Nat.cast_nonneg _)]
    have e1 : 4 * (Real.sqrt 2 * Real.sqrt X.gA) ≤ Real.sqrt X.gA * (6 * Real.sqrt Real.pi) := by
      nlinarith
    have e2 : Real.sqrt X.gA * (6 * Real.sqrt Real.pi) ≤
        Real.sqrt X.gA * (6 * Real.sqrt Real.pi) * (Real.sqrt P.q * X.la1) :=
      le_mul_of_one_le_right (by positivity) h1
    nlinarith
  have hBC : 1 + 4 * Real.sqrt (2 * X.gA) / (Real.sqrt Real.pi * X.la1) ≤ C := by
    rw [hC]; linarith
  have hB0 : 0 ≤ 1 + 4 * Real.sqrt (2 * X.gA) / (Real.sqrt Real.pi * X.la1) := by positivity
  have hCpos : 0 < C := by rw [hC]; positivity
  rcases le_or_gt (X.l2 1 s) 0 with hL | hL
  · rw [Real.sqrt_eq_zero'.mpr hL, div_zero]
    exact (Real.exp_pos _).le
  · have hpow := pow_le_pow_left₀ hB0 hBC (2 * X.gA)
    have hA : X.ptN2 1 s (fun _ => a) ≤ 2 * C ^ (2 * X.gA) * X.l2 1 s := by
      refine hB.trans ?_
      gcongr
    have hexp : Real.exp P.p1 = Real.exp 1 * C ^ X.gA := by
      unfold Par.p1
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by rw [← hC]; exact hCpos), hC]
    have he2 : Real.sqrt 2 ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hL), hexp]
    have hsplit : Real.sqrt (2 * C ^ (2 * X.gA) * X.l2 1 s) =
        Real.sqrt 2 * C ^ X.gA * Real.sqrt (X.l2 1 s) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        show C ^ (2 * X.gA) = (C ^ X.gA) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    calc Real.sqrt (X.ptN2 1 s fun _ => a) ≤ Real.sqrt (2 * C ^ (2 * X.gA) * X.l2 1 s) :=
          Real.sqrt_le_sqrt hA
      _ = Real.sqrt 2 * C ^ X.gA * Real.sqrt (X.l2 1 s) := hsplit
      _ ≤ Real.exp 1 * C ^ X.gA * Real.sqrt (X.l2 1 s) := by gcongr
end ReciprocityTheory.ChartRestriction.G.I2
