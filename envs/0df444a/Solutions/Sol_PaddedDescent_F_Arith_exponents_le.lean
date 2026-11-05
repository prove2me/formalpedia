-- Prove2me | solution 1 for PaddedDescent.F.Arith.exponents_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:30.223012+00:00
-- url     : https://prove2.me/submissions/17c259a1-371f-4a9d-81b2-4a0f484624ce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_small

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) :
    4 * (Xof s n + Zof s) + (Lof s n * (2 * Kseq (depthOf s) ^ 2) + (Xof s n + Zof s) + 2 * Lof s n + 1) + Kseq (depthOf s)
      ≤ 8 * Xof s n := by
  have h : 5 * Zof s + Lof s n * (2 * Kseq (depthOf s) ^ 2 + 2) + 1 + Kseq (depthOf s) ≤ n / 2 ^ s := small hY
  have e : Lof s n * (2 * Kseq (depthOf s) ^ 2 + 2) = Lof s n * (2 * Kseq (depthOf s) ^ 2) + 2 * Lof s n := by ring
  rw [e] at h
  unfold Xof
  omega
end PaddedDescent.F.Arith
