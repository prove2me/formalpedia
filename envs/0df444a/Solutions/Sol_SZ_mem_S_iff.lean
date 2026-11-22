-- Prove2me | solution 1 for SZ.mem_S_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:34.74129+00:00
-- url     : https://prove2.me/submissions/5e37af8b-ad19-4392-9190-16d12fac74c4

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Defs

set_option autoImplicit false
open SZ
open Int
namespace SZ
theorem _root_.solution {α : ℝ} : α ∈ S ↔ 1 < α ∧ α ∉ MahlerZ := Iff.rfl
end SZ
