-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.errorDown_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:56:56.828433+00:00
-- url     : https://prove2.me/submissions/fdf45eb9-906c-4b1a-82ce-94870736e0ab

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (b : Nat) (hb : b ≤ n)
    (e : (SuffixData S n).family.Cochain1 ⟨b,Nat.lt_succ_of_le hb⟩) :
    errorDown S n b hb e ⟨b,Nat.lt_succ_of_le hb⟩ (Nat.le_refl _) = e := by
  cases b with
  | zero => rw [errorDown] <;> rfl
  | succ b =>
      rw [errorDown]
      exact dif_pos rfl
end QEC.Coding.BDL26HistorySyndromeSensitivity
