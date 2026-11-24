-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussNormOf_pos_f7b56068fd3a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:55.512844+00:00
-- url     : https://prove2.me/submissions/68727a6a-3018-4ad0-97ae-b8dd1b24b112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_gaussNormOf_eq_b0903c48cd28

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
theorem _root_.solution {f : MvPolynomial ι R} (hf : f ≠ 0) : 0 < gaussNormOf w f := by
  obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq w hf
  rw [h]
  exact w.pos (mem_support_iff.mp hm)
end GroundTheory.Heights₂.Heights
