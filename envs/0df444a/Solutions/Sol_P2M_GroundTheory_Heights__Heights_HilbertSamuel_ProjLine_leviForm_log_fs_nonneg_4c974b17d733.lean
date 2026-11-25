-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_leviForm_log_fs_nonneg_4c974b17d733
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:18.134803+00:00
-- url     : https://prove2.me/submissions/f7b02871-d548-472e-b787-f7f713ebe38f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_eL_apply_0119d81ffd10
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_reInner_apply_2cd693b9f99f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_realInner_eq_0d541cc32a5b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_hasFDerivAt_normSqE_3939e36f8ae6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_normSqE_pos_5cb9d9b38f7b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_hasFDerivAt_log_fs_56ef9b0e4263
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.y_zero
attribute [local simp] GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.y_one

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
open scoped Topology
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
theorem _root_.solution {z : J → ℂ} (hz : z ≠ 0) (w : J → ℂ) :
    0 ≤ leviForm (fun z => Real.log ((fsMetric J).ρ z)) z w := by
  set G : (J → ℂ) → ((J → ℂ) →L[ℝ] ℝ) := fun y => (normSqE y)⁻¹ • reInner y with hG
  have hev : fderiv ℝ (fun z => Real.log ((fsMetric J).ρ z)) =ᶠ[𝓝 z] G := by
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    exact (hasFDerivAt_log_fs hy).fderiv
  have hq := normSqE_pos hz
  have hc : HasFDerivAt (fun y => (normSqE y)⁻¹) ((-(normSqE z ^ 2)⁻¹) • (2 • reInner z)) z :=
    (hasDerivAt_inv hq.ne').comp_hasFDerivAt z (hasFDerivAt_normSqE z)
  have hGd : HasFDerivAt G ((normSqE z)⁻¹ • reInner + ((-(normSqE z ^ 2)⁻¹) • (2 • reInner z)).smulRight (reInner z)) z :=
    hc.smul reInner.hasFDerivAt
  have hD : ∀ v, fderiv ℝ (fderiv ℝ (fun z => Real.log ((fsMetric J).ρ z))) z v v =
      (normSqE z)⁻¹ * inner ℝ (eL v) (eL v) - 2 * (normSqE z ^ 2)⁻¹ * inner ℝ (eL z) (eL v) ^ 2 := by
    intro v
    rw [hev.fderiv_eq, hGd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, nsmul_eq_mul, reInner_apply]
    push_cast
    ring
  unfold leviForm
  rw [hD, hD]
  have hI : eL (Complex.I • w) = Complex.I • eL w := by
    rw [eL_apply, eL_apply, WithLp.toLp_smul]
  rw [hI]
  set q := normSqE z
  have hq' : q = ‖eL z‖ ^ 2 := rfl
  set c : ℂ := inner ℂ (eL z) (eL w) with hcdef
  have h1 : inner ℝ (eL w) (eL w) = ‖eL w‖ ^ 2 := real_inner_self_eq_norm_sq _
  have h2 : inner ℝ (Complex.I • eL w) (Complex.I • eL w) = ‖eL w‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
  have h3 : inner ℝ (eL z) (eL w) = RCLike.re c := realInner_eq _ _
  have h4 : inner ℝ (eL z) (Complex.I • eL w) = RCLike.re (Complex.I * c) := by
    rw [realInner_eq, inner_smul_right]
  simp only [h1, h2, h3, h4]
  have hcs : ‖c‖ ^ 2 ≤ q * ‖eL w‖ ^ 2 := by
    rw [hq', ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  have hre : RCLike.re c ^ 2 + RCLike.re (Complex.I * c) ^ 2 = ‖c‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub]
    ring
  have key : 0 ≤ q⁻¹ * ‖eL w‖ ^ 2 - 2 * (q ^ 2)⁻¹ * RCLike.re c ^ 2 +
      (q⁻¹ * ‖eL w‖ ^ 2 - 2 * (q ^ 2)⁻¹ * RCLike.re (Complex.I * c) ^ 2) := by
    have h2 : q⁻¹ * ‖eL w‖ ^ 2 - 2 * (q ^ 2)⁻¹ * RCLike.re c ^ 2 +
        (q⁻¹ * ‖eL w‖ ^ 2 - 2 * (q ^ 2)⁻¹ * RCLike.re (Complex.I * c) ^ 2) =
        2 * (q ^ 2)⁻¹ * (q * ‖eL w‖ ^ 2 - ‖c‖ ^ 2) := by
      rw [← hre]
      field_simp
      ring
    rw [h2]
    have : 0 ≤ q * ‖eL w‖ ^ 2 - ‖c‖ ^ 2 := by linarith
    positivity
  linarith
end GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
