-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagRestrictDecomposition_proof_64301a331b7e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:08:28.859064+00:00
-- url     : https://prove2.me/submissions/c0b4c905-12d4-4e0c-9998-330f78a6bd60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagRestrictDecomposition

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagRestrictDecomposition
theorem _root_.solution (h1 : FlagRestrictPowerSum.Statement) :
    FlagRestrictDecomposition.Statement := by
  intro f N τ R
  rw [map_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
  rw [map_sum]
  simp only [map_mul, h1 f N l τ _ hl1, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ τ, if_pos (Finset.mem_univ τ)]
end FlagRestrictDecomposition
end GroundTheory.Heights₂.Heights.RestTerms
