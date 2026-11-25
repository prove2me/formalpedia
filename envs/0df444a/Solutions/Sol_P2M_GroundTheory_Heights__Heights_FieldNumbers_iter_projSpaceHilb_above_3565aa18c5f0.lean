-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_above_3565aa18c5f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:59.065581+00:00
-- url     : https://prove2.me/submissions/a63be48c-d5ea-4565-a373-8a305603f81b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_high_a19cf9cbcbe6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (N j : ℕ) (hj : N < j) (t : ℤ) (ht : (j : ℤ) ≤ t) :
    diff1^[j] (projSpaceHilb N) t = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = N + 1 + i := ⟨j - (N + 1), by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = s + ((N + 1 + i : ℕ) : ℤ) :=
    ⟨(t - ((N + 1 + i : ℕ) : ℤ)).toNat, by omega⟩
  exact iter_projSpaceHilb_high N i s
end GroundTheory.Heights₂.Heights.FieldNumbers
