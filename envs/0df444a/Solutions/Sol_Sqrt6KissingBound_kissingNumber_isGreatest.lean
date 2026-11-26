-- Prove2me | solution 1 for Sqrt6KissingBound.kissingNumber_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:39:29.732604+00:00
-- url     : https://prove2.me/submissions/7a5a2ed6-59b8-47dd-919e-d28f089594b5

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_realized
import Theorems.Thm_Sqrt6KissingBound_realizableKissingCard_le_kissingNumber

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) :
    IsGreatest {m : ℕ | RealizableKissingCard n m} (kissingNumber n) := by
  refine ⟨kissingNumber_realized n, ?_⟩
  intro m hm
  exact realizableKissingCard_le_kissingNumber hn hm
end Sqrt6KissingBound
