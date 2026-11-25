-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.CB.coefStepC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:38:44.048326+00:00
-- url     : https://prove2.me/submissions/05b2e5e0-eea6-4b2e-adf7-331348f038f5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiIntH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TLeftH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiRNonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_hpk_K
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_gN_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_gN_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_conjH_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_fsR_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_xiR_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_norm_bd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_c_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_sum_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_s_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_hpk_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_lmul_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_rmul_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_uh_inv_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.CB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.CB
theorem _root_.solution (hB2 : InductiveHeisenbergInputs) (hT : TBoth) (hD : DET) : CoefStep := by
  intro k r Wp Wq _ _ _ _ _ _ D A s hs hA hJ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGN, -, -, -, hCG', -⟩ := hB2
  have hCG := hCG' k r
  have hk := D.k_pos
  have hμ := D.haarG
  have hHK : Hpk k r ∈ Kset k r := hpk_K
  have hHG : Hpk k r ∈ GV k r := hHK.1
  have hH2 : Hpk k r * Hpk k r = 1 := HermitianLiftIdentities.hpk_sq k r
  obtain ⟨CD, hCD⟩ := hD k r s A hk (s_nonneg hk s hs) (sum_le hk s hs A hA)
  have hgc : Continuous fun g : Mt k r => gN (Matrix.of g) := by
    unfold gN
    simp only [Matrix.of_apply]
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))
  have hΦm : Measurable fun g : Mt k r => ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) :=
    (hgc.measurable.pow_const (-A)).ennreal_ofReal
  have hΦinv : ∀ κ ∈ Kset k r, ∀ g : Mt k r,
      ENNReal.ofReal (gN (Matrix.of (lmulM κ g)) ^ (-A)) = ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∧
      ENNReal.ofReal (gN (Matrix.of (rmulF κ g)) ^ (-A)) = ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) :=
    fun κ hκ g => ⟨by rw [show Matrix.of (lmulM κ g) = κ * Matrix.of g from rfl, gN_left _ hκ.2],
      by rw [show Matrix.of (rmulF κ g) = Matrix.of g * κ from rfl, gN_right _ hκ.2]⟩
  refine ⟨CD * (JInt D.μG A s).toReal, fun F F' c c' _ _ hF hF' x hx y hy => ?_⟩
  have hc0 : 0 ≤ c := c_nonneg hGN F c A hF hCG.one_mem
  have hc0' : 0 ≤ c' := c_nonneg hGN F' c' A hF' hCG.one_mem
  have hx' : Hpk k r * x * Hpk k r ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ hHG _ hx) _ hHG
  have hy' : Hpk k r * y * Hpk k r ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ hHG _ hy) _ hHG
  have hxinv : (Hpk k r * x * Hpk k r)⁻¹ = Hpk k r * x⁻¹ * Hpk k r :=
    Matrix.inv_eq_left_inv (by rw [conjH_mul, HermitianLiftIdentities.uh_inv_mul hx, Matrix.mul_one, hH2])
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := by rw [ae_iff]; exact hμ.conc
  set K : ℝ≥0∞ := ENNReal.ofReal c * ENNReal.ofReal c' * (CD : ℝ≥0∞) with hK
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    ENNReal.coe_ne_top
  have hpt : ∀ᵐ g ∂D.μG, ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ ≤
      K * (ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r))) := by
    filter_upwards [hae] with g hg
    have hh : x⁻¹ * Matrix.of g * y ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ (hCG.inv_mem _ hx) _ hg) _ hy
    have e1 : Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r = (Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r) := by
      rw [hxinv, conjH_mul, conjH_mul]
    have hhH : Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r ∈ GV k r :=
      hCG.mul_mem _ (hCG.mul_mem _ hHG _ hh) _ hHG
    have gNe : gN (x⁻¹ * Matrix.of g * y) = gN (Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r) := by
      rw [gN_right _ hHK.2, gN_left _ hHK.2]
    have b1 := norm_bd hGN F c A hF _ hh
    have b2 : ENNReal.ofReal (gN (x⁻¹ * Matrix.of g * y) ^ (-A)) ≤ (CD : ℝ≥0∞) * FsE k r s
        ((Hpk k r * x * Hpk k r)⁻¹ * (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) := by
      rw [gNe, ← e1]; exact hCD _ hhH
    have b3 := norm_bd hGN F' c' A hF' _ hg
    calc ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ
        ≤ (ENNReal.ofReal c * ENNReal.ofReal (gN (x⁻¹ * Matrix.of g * y) ^ (-A))) *
          (ENNReal.ofReal c' * ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) := mul_le_mul' b1 b3
      _ ≤ (ENNReal.ofReal c * ((CD : ℝ≥0∞) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
            (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)))) *
          (ENNReal.ofReal c' * ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) :=
        mul_le_mul' (mul_le_mul' le_rfl b2) le_rfl
      _ = _ := by rw [hK]; ring
  have hsub : (∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) ∂D.μG) =
      ∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        Matrix.of g * (Hpk k r * y * Hpk k r)) ∂D.μG := by
    rw [← HermitianLiftIdentities.rmul_int hHG hμ (fun g => ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of g * (Hpk k r * y * Hpk k r))),
      ← HermitianLiftIdentities.lmul_int hHG hμ (fun g => ENNReal.ofReal (gN (Matrix.of (rmulF (Hpk k r) g)) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of (rmulF (Hpk k r) g) * (Hpk k r * y * Hpk k r)))]
    refine lintegral_congr fun g => ?_
    show _ = ENNReal.ofReal (gN (Matrix.of (rmulF (Hpk k r) (lmulM (Hpk k r) g))) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of (rmulF (Hpk k r) (lmulM (Hpk k r) g)) *
          (Hpk k r * y * Hpk k r))
    rw [(hΦinv _ hHK _).2, (hΦinv _ hHK _).1]
    rfl
  have hTb := hT k r s D.μG (fun g => ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) hk hμ hΦm hΦinv _ hx' _ hy'
  calc (∫⁻ g, ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ ∂D.μG)
      ≤ ∫⁻ g, K * (ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r))) ∂D.μG := lintegral_mono_ae hpt
    _ = K * ∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) ∂D.μG := lintegral_const_mul' _ _ hKt
    _ = K * (ENNReal.ofReal (fsR k r s (Hpk k r * x * Hpk k r) * fsR k r s (Hpk k r * y * Hpk k r)) *
        JInt D.μG A s) := by rw [hsub, hTb]; rfl
    _ = ENNReal.ofReal (CD * (JInt D.μG A s).toReal * c * c') * (xiN k r s x : ℝ≥0∞) *
        (xiN k r s y : ℝ≥0∞) := by
      rw [fsR_conj, fsR_conj, ENNReal.ofReal_mul (xiR_nonneg s x)]
      rw [show (xiN k r s x : ℝ≥0∞) = ENNReal.ofReal (xiR k r s x) from rfl,
        show (xiN k r s y : ℝ≥0∞) = ENNReal.ofReal (xiR k r s y) from rfl]
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (NNReal.coe_nonneg CD) ENNReal.toReal_nonneg) hc0),
        ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg CD) ENNReal.toReal_nonneg), ENNReal.ofReal_mul (NNReal.coe_nonneg CD),
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hJ.ne, hK]
      ring
end ReciprocityTheory.ChartRestriction.DS.Xi.CB
