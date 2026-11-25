-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchAltPartitionExpansion_strictAnti_partition_add_stair_3c373b306f9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:52:42.495293+00:00
-- url     : https://prove2.me/submissions/a9a5b7da-5065-4032-a82d-7c0e04ee81fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchAltPartitionExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchAltPartitionExpansion
theorem _root_.solution {r n : ℕ} {lam : Fin r → ℕ} (hlam : lam ∈ partitionsOf r n) :
    StrictAnti (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) := by
  unfold partitionsOf at hlam
  rw [Finset.mem_filter] at hlam
  intro i j hij
  have h1 := hlam.2 i j hij.le
  have hj := j.isLt
  have hij' : (i : ℕ) < j := hij
  simp only
  omega
end SchAltPartitionExpansion
end GroundTheory.Heights₂.Heights.RestTerms
