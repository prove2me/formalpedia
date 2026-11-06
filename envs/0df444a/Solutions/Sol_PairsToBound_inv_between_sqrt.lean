-- Prove2me | solution 1 for PairsToBound.inv_between_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:57:26.226428+00:00
-- url     : https://prove2.me/submissions/8d05e5db-ade7-445c-a93b-fb12da6044bd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_GeneralPieces_Rec_Seq
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_GeneralPieces_Rec_PartB
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_PairsToBound_Pairs

set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen GeneralPieces MainTheoremForms
namespace PairsToBound
theorem _root_.solution {a b L t p : ℝ} (ha : 0 < a) (ht : 0 < t) (htp : t ^ 2 = p) (h1 : a * p ≤ L) (h2 : L ≤ b * p) :
    Real.sqrt a / Real.sqrt L ≤ 1 / t ∧ 1 / t ≤ Real.sqrt b / Real.sqrt L := by
  have hp : 0 < p := htp ▸ pow_pos ht 2
  have hL : 0 < L := lt_of_lt_of_le (mul_pos ha hp) h1
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hb : 0 ≤ b := by
    by_contra h
    have : b * p < 0 := mul_neg_of_neg_of_pos (not_le.1 h) hp
    linarith
  constructor
  · rw [div_le_div_iff₀ hsL ht, one_mul]
    refine Real.le_sqrt_of_sq_le ?_
    rw [mul_pow, Real.sq_sqrt ha.le, htp]
    exact h1
  · rw [div_le_div_iff₀ ht hsL, one_mul]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hb, htp]
    exact h2
end PairsToBound
