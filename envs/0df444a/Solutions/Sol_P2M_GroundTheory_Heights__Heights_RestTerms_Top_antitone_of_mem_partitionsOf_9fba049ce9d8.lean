-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_antitone_of_mem_partitionsOf_9fba049ce9d8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:46.95412+00:00
-- url     : https://prove2.me/submissions/102eb240-0e7a-42c2-aefd-bc1183ad2fcd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand

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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution {m n : ℕ} {lam : Fin m → ℕ} (h : lam ∈ partitionsOf m n) :
    Antitone lam := by
  intro i j hij
  exact (Finset.mem_filter.mp h).2 i j hij
end GroundTheory.Heights₂.Heights.RestTerms.Top
