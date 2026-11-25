-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.levi_rhF_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:49:21.117802+00:00
-- url     : https://prove2.me/submissions/c1372817-4534-4b25-9737-84db5e6edc15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_levi_logNormSq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_rhF_eq_log
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_cd_Zt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_isOpen_OmF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mem_OmF_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_rhF_contDiffAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhA_det_eq_ofReal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhA_det_mul_det_le_normSq_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhA_det_re_pos_im
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhD_contDiff_det_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhE_two_le_infty
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_const_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_re_nonpos_of_isLocalMax


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z0 : V (nd X)} (hz0 : z0 ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun y => ((rhF X x0 y : ℝ) : ℂ)) z0 ξ).re := by
  set Hf : V (nd X) → ℂ := fun y => ∏ τ, (1 - Zt X y τ * (Zt X z0 τ)ᴴ).det with hHf
  have hHcd : ContDiff ℂ ∞ Hf := by
    refine contDiff_prod fun τ _ => contDiff_det_of fun a b => ?_
    simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply]
    exact contDiff_const.sub (ContDiff.sum fun c _ => (cd_Zt X τ a c).mul contDiff_const)
  set P : V (nd X) → ℝ := fun y => ∏ τ, (Am X y τ).det.re with hP
  have hAm : ∀ y ∈ OmF X x0, ∀ τ, (Am X y τ).PosDef := fun y hy => (mem_OmF_iff X x0 ho y).1 hy
  have hPpos : ∀ y ∈ OmF X x0, 0 < P y := fun y hy =>
    Finset.prod_pos fun τ _ => (det_re_pos_im (hAm y hy τ)).1
  have hle : ∀ y ∈ OmF X x0, P y * P z0 ≤ Complex.normSq (Hf y) := by
    intro y hy
    simp only [hP, hHf]
    rw [← Finset.prod_mul_distrib, map_prod]
    exact Finset.prod_le_prod (fun τ _ => mul_nonneg (det_re_pos_im (hAm y hy τ)).1.le
      (det_re_pos_im (hAm z0 hz0 τ)).1.le)
      (fun τ _ => det_mul_det_le_normSq_det _ _ (hAm y hy τ) (hAm z0 hz0 τ))
  have hself : Complex.normSq (Hf z0) = P z0 * P z0 := by
    simp only [hP, hHf]
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have e : (1 - Zt X z0 τ * (Zt X z0 τ)ᴴ) = Am X z0 τ := rfl
    rw [e, det_eq_ofReal (hAm z0 hz0 τ), Complex.normSq_ofReal]
    simp
  set F : V (nd X) → ℝ := fun y => rhF X x0 y + Real.log (Complex.normSq (Hf y)) with hF
  have hmin : ∀ y ∈ OmF X x0, F z0 ≤ F y := by
    intro y hy
    have h2 := Real.log_le_log (mul_pos (hPpos y hy) (hPpos z0 hz0)) (hle y hy)
    rw [Real.log_mul (hPpos y hy).ne' (hPpos z0 hz0).ne'] at h2
    have h3 : F z0 = Real.log (P z0) := by
      simp only [hF]
      rw [hself, rhF_eq_log X x0 ho hz0, Real.log_mul (hPpos z0 hz0).ne' (hPpos z0 hz0).ne']
      ring
    rw [h3]
    simp only [hF]
    rw [rhF_eq_log X x0 ho hy]
    linarith
  have hmax : IsLocalMax (fun y => -F y) z0 := by
    have : IsLocalMin F z0 :=
      Filter.eventually_of_mem ((isOpen_OmF X x0).mem_nhds hz0) fun y hy => hmin y hy
    exact this.neg
  have hNpos : Complex.normSq (Hf z0) ≠ 0 := by
    rw [hself]; have := hPpos z0 hz0; positivity
  have hHne : Hf z0 ≠ 0 := fun h => hNpos (by rw [h]; simp)
  have hc1 : ContDiffAt ℝ 2 (fun y => rhF X x0 y) z0 := (rhF_contDiffAt X x0 ho hz0).of_le two_le_infty
  have hc2 : ContDiffAt ℝ 2 (fun y => Real.log (Complex.normSq (Hf y))) z0 := by
    have hn : ContDiff ℝ ∞ fun y : V (nd X) => Complex.normSq (Hf y) := by
      simp only [Complex.normSq_eq_norm_sq]
      exact (contDiff_norm_sq ℝ).comp (hHcd.restrict_scalars ℝ)
    exact ((Real.contDiffAt_log.2 hNpos).comp z0 hn.contDiffAt).of_le two_le_infty
  have hcF : ContDiffAt ℝ 2 F z0 := hc1.add hc2
  have h1 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hcF.neg hmax ξ
  have e1 : (fun y => ((-F y : ℝ) : ℂ)) = fun y => (((-1) * F y : ℝ) : ℂ) := by
    funext y; simp
  rw [e1, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hcF ξ] at h1
  have e2 : (fun y => ((F y : ℝ) : ℂ)) =
      fun y => ((rhF X x0 y + Real.log (Complex.normSq (Hf y)) : ℝ) : ℂ) := rfl
  rw [e2, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add hc1 hc2 ξ,
    levi_logNormSq_zero Hf hHcd z0 hHne ξ] at h1
  simp at h1
  linarith
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
