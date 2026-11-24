-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_mem_partitionsOf_iff_9f8ef15178d9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:41.709256+00:00
-- url     : https://prove2.me/submissions/3f373042-820d-40eb-89e8-6e6448f12007

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue

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
theorem _root_.solution {m n : ℕ} (lam : Fin m → ℕ) :
    lam ∈ partitionsOf m n ↔ ∑ i, lam i = n ∧ Antitone lam := by
  simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  exact Iff.rfl
end GroundTheory.Heights₂.Heights.RestTerms.Top
