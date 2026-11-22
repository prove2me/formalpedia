-- Prove2me | solution 1 for SZ.twoStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:42:11.994563+00:00
-- url     : https://prove2.me/submissions/1525f2ce-f2b8-4bf1-847f-ba1c2fb7f1c1

import Definitions.Def_SZ_Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Trace

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution {P : ℕ → Prop} (h0 : P 0) (h1 : P 1)
    (hs : ∀ n, P n → P (n + 1) → P (n + 2)) (n : ℕ) : P n :=
  Nat.twoStepInduction h0 h1 hs n
end SZ
