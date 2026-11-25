-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_levi_comp_real_46101a89c4a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:36:24.937494+00:00
-- url     : https://prove2.me/submissions/6eee5097-6d16-46d0-9bc7-4be05b21886a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
namespace GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
theorem _root_.solution {ι : Type*} [Fintype ι] {ρ ρ' : ℝ → ℝ} {ρ'' : ℝ} {t : (ι → ℂ) → ℝ}
    {z : ι → ℂ} (hρ : ∀ u, HasDerivAt ρ (ρ' u) u) (hρ' : HasDerivAt ρ' ρ'' (t z))
    (ht : ContDiffAt ℝ 2 t z) (w : ι → ℂ) :
    levi (ρ ∘ t) z w = ρ' (t z) * levi t z w +
      ρ'' * ((fderiv ℝ t z w) ^ 2 + (fderiv ℝ t z (Complex.I • w)) ^ 2) / 4 := by
  have h1 : ∀ᶠ y in 𝓝 z, HasFDerivAt (ρ ∘ t) (ρ' (t y) • fderiv ℝ t y) y := by
    filter_upwards [ht.eventually (by simp)] with y hy
    exact (hρ (t y)).comp_hasFDerivAt y (hy.differentiableAt (by norm_num)).hasFDerivAt
  have h1' : fderiv ℝ (ρ ∘ t) =ᶠ[𝓝 z] fun y => ρ' (t y) • fderiv ℝ t y :=
    h1.mono fun y hy => hy.fderiv
  have ht' : HasFDerivAt (fderiv ℝ t) (fderiv ℝ (fderiv ℝ t) z) z :=
    ((ht.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h2 : HasFDerivAt (fun y => ρ' (t y) • fderiv ℝ t y)
      (ρ' (t z) • fderiv ℝ (fderiv ℝ t) z + (ρ'' • fderiv ℝ t z).smulRight (fderiv ℝ t z)) z :=
    (hρ'.comp_hasFDerivAt z (ht.differentiableAt (by norm_num)).hasFDerivAt).smul ht'
  have h3 : fderiv ℝ (fderiv ℝ (ρ ∘ t)) z =
      ρ' (t z) • fderiv ℝ (fderiv ℝ t) z + (ρ'' • fderiv ℝ t z).smulRight (fderiv ℝ t z) := by
    rw [h1'.fderiv_eq]
    exact h2.fderiv
  simp only [levi, h3, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
