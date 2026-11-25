-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_normSq_analytic_f5d0991fe1ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:48:19.635799+00:00
-- url     : https://prove2.me/submissions/8dc66d15-097e-4fc7-8353-ce3dba3d9d5d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PGreenMassReplaceLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_comp_real_4d15d05546d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_re_analytic_f165eb17d640
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_im_analytic_7493638fe9a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_im_analytic_5240bb34bec0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_contDiffAt_re_analytic_701086e03a5e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_contDiffAt_im_analytic_85ef43de592a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_sq_norm_eq_re_im_995b20f7781c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_hasDerivAt_sq__f72e6668d75d
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul levi_re_analytic)
noncomputable section
variable {ι : Type} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (w : ι → ℂ) :
    levi (fun z => ‖S z‖ ^ 2) y w = ‖fderiv ℂ S y w‖ ^ 2 := by
  have hre := contDiffAt_re_analytic hS
  have him := contDiffAt_im_analytic hS
  have e : (fun z => ‖S z‖ ^ 2) = fun z => (S z).re ^ 2 + 1 * (S z).im ^ 2 :=
    funext fun z => sq_norm_eq_re_im _
  have hG : ∀ (ψ : (ι → ℂ) → ℝ), ∀ᶠ z in 𝓝 y, HasDerivAt (fun x : ℝ => x ^ 2) (2 * ψ z) (ψ z) :=
    fun ψ => Eventually.of_forall fun z => hasDerivAt_sq' _
  have hG₁ : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 2 * x) 2 x := fun x => by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have l1 := levi_comp_real (G₁ := fun x => 2 * x) hre (hG _) (hG₁ _) w
  have l2 := levi_comp_real (G₁ := fun x => 2 * x) him (hG _) (hG₁ _) w
  have hsq : ∀ (ψ : (ι → ℂ) → ℝ), ContDiffAt ℝ 2 ψ y → ContDiffAt ℝ 2 (fun z => ψ z ^ 2) y :=
    fun ψ h => h.pow 2
  rw [e, levi_add_smul 1 (hsq _ hre) (hsq _ him), l1, l2, levi_re_analytic hS,
    levi_im_analytic hS, fderiv_re_analytic hS, fderiv_re_analytic hS, fderiv_im_analytic hS,
    fderiv_im_analytic hS, map_smul, sq_norm_eq_re_im]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring
end GroundTheory.Heights₂.Heights.AnalyticLimit
