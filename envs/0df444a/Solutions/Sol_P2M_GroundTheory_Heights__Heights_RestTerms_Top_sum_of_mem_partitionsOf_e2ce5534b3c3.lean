-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_of_mem_partitionsOf_e2ce5534b3c3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:43.188819+00:00
-- url     : https://prove2.me/submissions/fe38207a-a1fa-4e32-8981-04865db5ed1f

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
    ∑ i, lam i = n := by
  have := (Finset.mem_filter.mp h).1
  rw [Finset.Nat.mem_antidiagonalTuple] at this
  exact this
end GroundTheory.Heights₂.Heights.RestTerms.Top
