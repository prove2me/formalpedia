-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibreMahlerForms_exists_archLin_ne_zero_ed53fe7598d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:15:04.220914+00:00
-- url     : https://prove2.me/submissions/2521a134-4aeb-4e50-a87f-5db08714c885

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_apply_eq_sum_1364e9b5a1d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_archLin_fibreVec_3b5dbbaf6e5b

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
open MvPolynomial NumberField TensorProduct ComplexAt
noncomputable section
open GroundTheory.Heights₂.Heights.FibreMahlerForms
variable {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (𝓞 F) W]
  [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W]
variable {K : Type} [Field K] [NumberField K] [Algebra F K]
namespace GroundTheory.Heights₂.Heights.FibreMahlerForms
theorem _root_.solution (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K)
    (hy : yv ≠ 0) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (FibreSpace h (τ.comp (algebraMap F K)))) :
    ∃ j, archLin h τ yv (b j) ≠ 0 := by
  obtain ⟨e, he⟩ : ∃ e, yv e ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy (LinearMap.ext hc)
  by_contra hc
  push Not at hc
  have h1 := apply_eq_sum b (archLin h τ yv) (fibreVec h _ e)
  rw [archLin_fibreVec] at h1
  simp only [hc, mul_zero, Finset.sum_const_zero] at h1
  exact (map_ne_zero τ).mpr he h1
end GroundTheory.Heights₂.Heights.FibreMahlerForms
