-- Prove2me | solution 1 for Sendov.unpackZ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:54:35.509818+00:00
-- url     : https://prove2.me/submissions/bf843e00-020b-4653-8b10-41d91e21d184

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (b : ℤ) (m : ℕ) (x : ℤ) :
    unpackZ b (m + 1) x = bdig b x :: unpackZ b m ((x - bdig b x) / b) := rfl
end Sendov
