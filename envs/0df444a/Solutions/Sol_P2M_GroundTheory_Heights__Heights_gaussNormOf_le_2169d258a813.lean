-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:43.183854+00:00
-- url     : https://prove2.me/submissions/983dee0d-2fe8-41ca-aabe-2a458825b013

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_def_6cd6aa89eff0

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
theorem _root_.solution {f : MvPolynomial ι R} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ m, w (f.coeff m) ≤ r) : gaussNormOf w f ≤ r := by
  have h' : (f.support.sup fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal)) ≤ ⟨r, hr⟩ :=
    Finset.sup_le fun m _ => h m
  rw [gaussNormOf_def]
  exact NNReal.coe_le_coe.mpr h'
end GroundTheory.Heights₂.Heights
