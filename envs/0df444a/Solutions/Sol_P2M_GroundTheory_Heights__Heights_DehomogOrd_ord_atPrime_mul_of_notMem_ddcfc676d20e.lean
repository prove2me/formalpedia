-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_atPrime_mul_of_notMem_ddcfc676d20e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:52:11.731903+00:00
-- url     : https://prove2.me/submissions/4e69fce6-722e-4700-b925-d4392e4589e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd

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
noncomputable section
open GroundTheory.Heights₂.Heights.DehomogOrd
namespace GroundTheory.Heights₂.Heights.DehomogOrd
theorem _root_.solution {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime] {u : A} (hu : u ∉ P)
    (x : A) :
    Ring.ord (Localization.AtPrime P) (algebraMap A _ (u * x)) =
      Ring.ord (Localization.AtPrime P) (algebraMap A _ x) := by
  have h : IsUnit (algebraMap A (Localization.AtPrime P) u) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P u).mpr hu
  rw [map_mul]
  exact Ring.ord_mul_of_isUnit_left h _
end GroundTheory.Heights₂.Heights.DehomogOrd
