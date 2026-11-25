-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_dz_logAbsSq_95cbc1eb4958
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:22:29.056429+00:00
-- url     : https://prove2.me/submissions/a23dd265-d1b1-417f-b199-727231d676b5

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepRankOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepRankOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_analyticAt_eval_poly_5731e866b48a
import Theorems.Thm_ReciprocityTheory_AnForm_A_dz_cplx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TubeDeepRankOne
namespace GroundTheory.Heights₂.Heights.TubeDeepRankOne
theorem _root_.solution {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) (hP : eval y P ≠ 0)
    (j : Fin m) :
    dz j (cplx (logAbsSq P)) y = fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P := by
  have hg := analyticAt_eval_poly P y
  have hgd : HasFDerivAt (fun z => eval z P) (fderiv ℂ (fun z => eval z P) y) y :=
    hg.differentiableAt.hasFDerivAt
  have h1 := (hgd.restrictScalars ℝ).norm_sq
  have hne : ‖eval y P‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hP)
  have h2 := h1.log hne
  have hf : fderiv ℝ (logAbsSq P) y = _ := h2.fderiv
  set c := fderiv ℂ (fun z => eval z P) y (Pi.single j 1) with hc
  set p := eval y P with hp
  set w := c * (starRingEnd ℂ) p with hw
  have hI : fderiv ℂ (fun z => eval z P) y (Complex.I • Pi.single j 1) = Complex.I * c := by
    rw [map_smul, smul_eq_mul]
  have hN : Complex.normSq p ≠ 0 := (Complex.normSq_pos.2 hP).ne'
  have e1 : fderiv ℝ (logAbsSq P) y (Pi.single j 1) = 2 * w.re / Complex.normSq p := by
    rw [hf]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.coe_restrictScalars', Complex.inner, smul_eq_mul, nsmul_eq_mul,
      Complex.normSq_eq_norm_sq]
    rw [← hc, hw]
    ring
  have e2 : fderiv ℝ (logAbsSq P) y (Complex.I • Pi.single j 1) = -(2 * w.im / Complex.normSq p) := by
    rw [hf]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.coe_restrictScalars', Complex.inner, smul_eq_mul, nsmul_eq_mul,
      Complex.normSq_eq_norm_sq]
    rw [hI, hw]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hcp : c / p = w / (Complex.normSq p : ℂ) := by
    rw [← Complex.mul_conj, hw, mul_div_mul_right _ _ ((map_ne_zero _).2 hP)]
  rw [dz_cplx, e1, e2, hcp]
  conv_rhs => rw [← Complex.re_add_im w]
  have hN' : (Complex.normSq p : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast
  field_simp
  ring
end GroundTheory.Heights₂.Heights.TubeDeepRankOne
