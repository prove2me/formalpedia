-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveGermComponents_exists_minimalPrime_mem_zeroSet_87cadad79225
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:09:19.065585+00:00
-- url     : https://prove2.me/submissions/595b2d7f-d60d-439f-bd88-280384b29149

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveGermComponents
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveGermComponents_mem_zeroSet_iff_le_ker_1b3406fd666e

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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.CurveGermComponents
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.CurveGermComponents
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) ℂ)} {x : Fin n → ℂ}
    (hx : x ∈ zeroSet I) : ∃ W ∈ I.minimalPrimes, x ∈ zeroSet W := by
  rw [mem_zeroSet_iff_le_ker] at hx
  obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le hx
  exact ⟨W, hW, (mem_zeroSet_iff_le_ker W x).2 hle⟩
end GroundTheory.Heights₂.Heights.CurveGermComponents
