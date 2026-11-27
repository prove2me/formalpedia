-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_of_mem_fundCycle_support_ac08cec74a0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:11:33.197613+00:00
-- url     : https://prove2.me/submissions/da6bfceb-9876-4b61-89fa-cb47f890c8ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ComplexFibreIdealBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemMinimalPrimesOfMemFundCycleSupport

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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar ptsIntegral pot)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)}
    (hW : W ∈ (fundCycle J).support) : W ∈ J.minimalPrimes := by
  have h := Finsupp.support_onFinset_subset hW
  rwa [Set.Finite.mem_toFinset] at h
end GroundTheory.Heights₂.Heights
