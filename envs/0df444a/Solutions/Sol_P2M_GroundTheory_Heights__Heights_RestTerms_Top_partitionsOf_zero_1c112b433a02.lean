-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_partitionsOf_zero_1c112b433a02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:48.010818+00:00
-- url     : https://prove2.me/submissions/b18043f5-eb46-45d1-8e2a-e283627679fd

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
theorem _root_.solution (r : ℕ) : partitionsOf r 0 = {0} := by
  ext lam
  simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    funext i
    have := Finset.sum_eq_zero_iff.mp h i (Finset.mem_univ i)
    simpa using this
  · rintro rfl
    simp
end GroundTheory.Heights₂.Heights.RestTerms.Top
