-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DehomogOrd_disjoint_powers_ad65955fa1d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:52:05.976245+00:00
-- url     : https://prove2.me/submissions/2430cd92-9333-4a25-9fab-1ab2a2300bea

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
theorem _root_.solution {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] {x : R} (hx : x ∉ P) :
    Disjoint ((Submonoid.powers x : Submonoid R) : Set R) P := by
  rw [Set.disjoint_left]
  rintro _ ⟨k, rfl⟩ hk
  exact hx (hP.mem_of_pow_mem k hk)
end GroundTheory.Heights₂.Heights.DehomogOrd
