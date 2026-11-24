-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:44.116805+00:00
-- url     : https://prove2.me/submissions/5ece8fef-bb73-45b8-9b43-238677ca17b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_def_6cd6aa89eff0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_nonneg_e5b131e01688

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
open MvPolynomial NumberField
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*} (w : AbsoluteValue R ℝ)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (f : MvPolynomial ι R) (m : ι →₀ ℕ) : w (f.coeff m) ≤ gaussNormOf w f := by
  by_cases hm : m ∈ f.support
  · have h : (⟨w (f.coeff m), w.nonneg _⟩ : NNReal) ≤
        f.support.sup fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal) :=
      Finset.le_sup (f := fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal)) hm
    rw [gaussNormOf_def]
    exact NNReal.coe_le_coe.mpr h
  · rw [notMem_support_iff.mp hm, map_zero]
    exact gaussNormOf_nonneg w f
end GroundTheory.Heights₂.Heights
