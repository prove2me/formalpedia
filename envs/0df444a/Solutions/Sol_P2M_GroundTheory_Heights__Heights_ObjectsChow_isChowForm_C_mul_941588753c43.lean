-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_isChowForm_C_mul_941588753c43
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:49.55763+00:00
-- url     : https://prove2.me/submissions/97902218-7ca4-4d61-ab4a-8e1ba7e95c85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {F : Type*} [Field F] {I : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) {c : F} (hc : c ≠ 0) :
    IsChowForm I k (C c * f) := by
  have hu : IsUnit (C c : MvPolynomial (Fin k × Fin n) F) := (isUnit_iff_ne_zero.mpr hc).map C
  refine ⟨mul_ne_zero (hu.ne_zero) hf.1, fun g => (hf.2 g).trans ?_⟩
  exact (hu.mul_left_dvd).symm
end GroundTheory.Heights₂.Heights.ObjectsChow
