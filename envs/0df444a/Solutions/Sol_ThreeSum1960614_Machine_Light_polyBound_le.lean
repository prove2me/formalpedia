-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.polyBound_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:46.931207+00:00
-- url     : https://prove2.me/submissions/8f42e846-93c2-4ac9-aaf8-b701308efb92

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Light
end Light
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

namespace ThreeSum1960614.Machine

/-!
# A polynomial bound in the parameters fits in a word

The running-time claims hold at every word size W ≥ b (log₂ p₁ + ⋯ + log₂ p_r + 1), where p₁, …, p_r
are the parameters of the instance and the slope b is chosen with the program (`Admissible`).  A
light program states its limits as a polynomial in the parameters,
`polyBound s k params` = 2^s ((p₁ + 1) ⋯ (p_r + 1))^k.

The main fact is `polyBound_le`: this bound is at most 2^W as soon as b ≥ s + k r + k.  Each factor
p + 1 is at most 2^(log₂ p + 1) (`prod_succ_le`), so with S the sum of the logarithms the bound is
at most 2^(s + k (S + r)), and s + k (S + r) ≤ (s + k r + k) (S + 1) ≤ W.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam



section

private theorem private_6026acc201_prod_succ_le (params : List ℕ) :
    (params.map (· + 1)).prod ≤ 2 ^ ((params.map Nat.log2).sum + params.length) := by
  induction params with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons]
    calc (p + 1) * (ps.map (· + 1)).prod
        ≤ 2 ^ (p.log2 + 1) * 2 ^ ((ps.map Nat.log2).sum + ps.length) :=
          Nat.mul_le_mul Nat.lt_log2_self ih
      _ = 2 ^ (p.log2 + (ps.map Nat.log2).sum + (ps.length + 1)) := by
          rw [← pow_add]
          congr 1
          omega
end


















end Light

end

end ThreeSum1960614.Machine

section
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
section

/-- At an admissible word size, words have room for a polynomial bound in the parameters, if the
slope is large enough. -/
theorem ThreeSum1960614.Machine.Light.polyBound_le__implementation_29eecfb5c3 {b W s k r : ℕ} {params : List ℕ} (h : _root_.ThreeSumApsp.WordRam.Admissible b params W)
    (hr : params.length ≤ r) (hb : s + k * r + k ≤ b) : _root_.Light.polyBound s k params ≤ 2 ^ W := by
  set S := (params.map Nat.log2).sum
  have hexp : s + (S + params.length) * k ≤ W :=
    calc s + (S + params.length) * k ≤ s + (S + r) * k := by gcongr
      -- the difference is s S + k r S + k
      _ ≤ (s + k * r + k) * (S + 1) := Nat.le.intro (k := s * S + k * r * S + k) (by ring)
      _ ≤ b * (S + 1) := Nat.mul_le_mul_right _ hb
      _ ≤ W := h
  calc _root_.Light.polyBound s k params ≤ 2 ^ s * (2 ^ (S + params.length)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (_root_.ThreeSum1960614.Machine.Light.private_6026acc201_prod_succ_le params) k)
    _ = 2 ^ (s + (S + params.length) * k) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hexp
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.polyBound_le__implementation_29eecfb5c3) := (@ThreeSum1960614.Machine.Light.polyBound_le__implementation_29eecfb5c3)

#print axioms solution
