-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.propagate_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:43:20.632343+00:00
-- url     : https://prove2.me/submissions/17f15aea-e881-498f-813d-4f940c10478a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (b : Nat) (hb : b ≤ n)
    (A : Finset (Coordinates S n ⟨b,Nat.lt_succ_of_le hb⟩)) :
    propagate S n b hb ⟨b,Nat.lt_succ_of_le hb⟩ (Nat.le_refl _) A = A := by
  cases b with
  | zero => rw [propagate] <;> rfl
  | succ b =>
      rw [propagate]
      exact dif_pos rfl
end QEC.Coding.BDL26HistorySyndromeSensitivity
