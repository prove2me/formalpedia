-- Prove2me | solution 1 for Sqrt6KissingBound.kissingNumber_universal_base_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:43:09.056481+00:00
-- url     : https://prove2.me/submissions/89d74a6c-b197-487d-88d9-d67f07fe83e6

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
import Theorems.Thm_Sqrt6KissingBound_isUniversalKissingBase_iff_kissingNumber
import Theorems.Thm_Sqrt6KissingBound_isUniversalKissingBase_iff


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution (α : ℝ) :
    (0 ≤ α ∧ ∀ n : ℕ, 1 ≤ n → (kissingNumber n : ℝ) ≤ α ^ n) ↔
      Real.sqrt 6 ≤ α :=
  (isUniversalKissingBase_iff_kissingNumber α).symm.trans (isUniversalKissingBase_iff α)
end Sqrt6KissingBound
