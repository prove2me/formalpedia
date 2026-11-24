-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_primeWeight_eq_zero_of_lt_0f940253db51
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:48.762139+00:00
-- url     : https://prove2.me/submissions/9ad40ca8-ecfb-4dcc-87e8-9cefe2999168

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt

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
open Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.Elem
namespace GroundTheory.Heights₂.Heights.RestTerms.Elem
theorem _root_.solution (B : ℝ) (hB : 0 ≤ B) {i : ℕ} (hi : i < ⌊B⌋₊ + 1) :
    primeWeight B i = 0 := by
  unfold primeWeight
  rw [if_neg]
  rintro ⟨_, h⟩
  have : (i : ℝ) ≤ B := by
    have := Nat.le_floor_iff hB |>.mp (Nat.lt_succ_iff.mp hi)
    exact this
  linarith
end GroundTheory.Heights₂.Heights.RestTerms.Elem
