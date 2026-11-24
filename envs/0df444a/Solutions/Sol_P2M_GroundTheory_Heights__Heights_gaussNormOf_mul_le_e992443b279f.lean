-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_le_e992443b279f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:49.221803+00:00
-- url     : https://prove2.me/submissions/aea4b754-bfb6-47f8-8833-66d4ade62605

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_nonneg_e5b131e01688
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813

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
variable {w}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hna : IsNonarchimedean w) (f g : MvPolynomial ι R) :
    gaussNormOf w (f * g) ≤ gaussNormOf w f * gaussNormOf w g := by
  classical
  refine gaussNormOf_le w (mul_nonneg (gaussNormOf_nonneg w f) (gaussNormOf_nonneg w g)) fun m => ?_
  rw [coeff_mul]
  refine (hna.apply_sum_le_sup (s := Finset.HasAntidiagonal.antidiagonal m) ⟨(0, m), by simp⟩).trans ?_
  refine Finset.sup'_le _ _ fun p _ => ?_
  rw [map_mul]
  exact mul_le_mul (le_gaussNormOf w f _) (le_gaussNormOf w g _) (w.nonneg _)
    (gaussNormOf_nonneg w f)
end GroundTheory.Heights₂.Heights
