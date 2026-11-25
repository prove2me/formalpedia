-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_flagIntegral_sum_7c1da116bb5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:58:56.800469+00:00
-- url     : https://prove2.me/submissions/0648f9c6-f8da-494d-81a2-4dec3653045e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutFlagKillsIdeal

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
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι : Type*} (f N : ℕ) (s : Finset ι)
    (P : ι → RestTerms.RootRing f N) :
    RestTerms.flagIntegral f N (∑ i ∈ s, P i) = ∑ i ∈ s, RestTerms.flagIntegral f N (P i) := by
  unfold RestTerms.flagIntegral
  simp only [coeff_sum, Finset.sum_mul]
  exact Finset.sum_comm
end GroundTheory.Heights₂.Heights
