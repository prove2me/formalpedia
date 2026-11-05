-- Prove2me | solution 1 for PaddedDescent.F.Arith.clauses_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:23.648185+00:00
-- url     : https://prove2.me/submissions/413f9b12-db22-4bee-b657-4c54a90ff61b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {Δ s : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) (n : ℕ) : Δ * n ≤ 2 ^ betaOf s * (n + 1) :=
  Nat.mul_le_mul hΔ (Nat.le_succ n)
end PaddedDescent.F.Arith
