-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_range_chartMap_599b5829d5e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:12:23.388329+00:00
-- url     : https://prove2.me/submissions/6d5b2f30-504d-478b-aeed-100737094174

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFunctionFieldFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFunctionFieldFinite

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
open GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite
theorem _root_.solution (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    (chartMap P u).range = Algebra.adjoin F (chartGens P u) :=
  aeval_range _
end GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite
