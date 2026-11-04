-- Prove2me | solution 1 for ThreeSum.TernaryWantedRadix.codeLimit_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:22:07.539251+00:00
-- url     : https://prove2.me/submissions/d4bb72a1-cf21-4608-8363-929a193072ed

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset
namespace ThreeSum.TernaryWantedRadix
theorem _root_.solution {N code scale j : ℕ} (hN : 1 ≤ N) :
    code+scale ≤ codeLimit N code scale j := by
  unfold codeLimit
  exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
end ThreeSum.TernaryWantedRadix
