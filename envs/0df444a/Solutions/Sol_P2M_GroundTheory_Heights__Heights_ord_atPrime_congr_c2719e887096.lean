-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ord_atPrime_congr_c2719e887096
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:51.228494+00:00
-- url     : https://prove2.me/submissions/7b8990d5-00c5-4496-a7ae-26ee4851f09d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] {P₁ P₂ : Ideal R} [P₁.IsPrime] [P₂.IsPrime]
    (h : P₁ = P₂) (x : R) :
    Ring.ord (Localization.AtPrime P₁) (algebraMap R _ x) =
      Ring.ord (Localization.AtPrime P₂) (algebraMap R _ x) := by
  subst h; rfl
end GroundTheory.Heights₂.Heights
