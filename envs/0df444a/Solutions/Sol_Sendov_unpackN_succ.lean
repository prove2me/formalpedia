-- Prove2me | solution 1 for Sendov.unpackN_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:22.857085+00:00
-- url     : https://prove2.me/submissions/94ba8fce-9713-4441-94c7-2150d15e65ae

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (b m x : ℕ) :
    unpackN b (m + 1) x = (x % b) :: unpackN b m (x / b) := rfl
end Sendov
