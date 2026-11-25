-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIncOrd_isPrime_map_C_94303c3811a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:36:09.448082+00:00
-- url     : https://prove2.me/submissions/1be171c5-81e8-4190-ba3a-3cd36c6ca290

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncOrd

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
open GroundTheory.Heights₂.Heights.ChartIncOrd
namespace GroundTheory.Heights₂.Heights.ChartIncOrd
theorem _root_.solution {R : Type*} [CommRing R] (σ : Type*) (p : Ideal R) [p.IsPrime] :
    (p.map (C : R →+* MvPolynomial σ R)).IsPrime := by
  have h := MvPolynomial.ker_map (σ := σ) (Ideal.Quotient.mk p)
  rw [Ideal.mk_ker] at h
  rw [← h]
  exact RingHom.ker_isPrime _
end GroundTheory.Heights₂.Heights.ChartIncOrd
