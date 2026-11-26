-- Prove2me | solution 1 for Sendov.unpackN_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:14.270123+00:00
-- url     : https://prove2.me/submissions/e5ab532e-761e-4a96-9881-ccdac89fbf11

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (b x : ℕ) : unpackN b 0 x = [] := rfl
end Sendov
