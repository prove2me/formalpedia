-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DehomogOrd_isPrime_map_C_2b9d3db6148a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:52:08.871798+00:00
-- url     : https://prove2.me/submissions/56e78f7a-0ab3-42ca-9e58-bd37fbf0708b

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
theorem _root_.solution {R : Type*} [CommRing R] (σ : Type*) (p : Ideal R) [p.IsPrime] :
    (Ideal.map (C : R →+* MvPolynomial σ R) p).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact MulEquiv.isDomain (MvPolynomial σ (R ⧸ p))
    (quotientEquivQuotientMvPolynomial (σ := σ) p).toRingEquiv.toMulEquiv.symm
end GroundTheory.Heights₂.Heights.DehomogOrd
