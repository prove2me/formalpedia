-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_colon_eq_of_not_mem_041a78df4446
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:27:10.431829+00:00
-- url     : https://prove2.me/submissions/9f473ff3-0694-496b-9585-54ff39eae2b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_mem_colon_span_iff_bab2c8fb31ff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
theorem _root_.solution {P : Ideal (MRing ι F)} [hP : P.IsPrime] {s : MRing ι F}
    (hs : s ∉ P) : P.colon (Ideal.span {s}) = P := by
  ext g
  rw [HilbExactDivide.mem_colon_span_iff]
  exact ⟨fun h => (hP.mem_or_mem h).resolve_right hs, fun h => P.mul_mem_right s h⟩
end GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
