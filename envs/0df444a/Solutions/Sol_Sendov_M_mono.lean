-- Prove2me | solution 1 for Sendov.M_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:32.29491+00:00
-- url     : https://prove2.me/submissions/a061f048-e922-4b87-962b-21bdccf92303

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_Batch

set_option autoImplicit false
open Sendov
variable {α t : ℝ}
namespace Sendov
theorem _root_.solution {m n : ℕ} (h : m ≤ n) : M m ≤ M n := by
  simp only [M]
  have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  linarith
end Sendov
