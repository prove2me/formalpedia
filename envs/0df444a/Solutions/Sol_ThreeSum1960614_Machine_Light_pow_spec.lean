-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.pow_spec
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:11:14.669548+00:00
-- url     : https://prove2.me/submissions/7cf3861e-cc39-447b-9a32-76c9f04fe8ad

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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

local instance platformRadixNonzero_133dd517f7 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Light
end Light
namespace Light.Wrap
end Light.Wrap
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Wrap
end ThreeSum1960614.Machine.Light.Wrap
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

section
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

/-- The loop that is written out κ times turns U = 1 into U = n^κ. -/
theorem ThreeSum1960614.Machine.Light.pow_spec__implementation_d1cc9bc2b7 {n : ℕ} (hn : 1 ≤ n) (a : ℤ) (μ : ℕ → ℤ) : ∀ κ : ℕ, ((n ^ κ : ℕ) : ℤ) ≤ lim.word →
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.powStmt κ) ⟨_root_.Light.frame [a, n, 1], μ⟩ (4 * κ) (· = ⟨_root_.Light.frame [a, n, ((n ^ κ : ℕ) : ℤ)], μ⟩)
  | 0, _ => _root_.ThreeSum1960614.Machine.Light.Ends.skip (by simp)
  | κ + 1, hw => by
    have hle : ((n ^ κ : ℕ) : ℤ) ≤ ((n ^ (κ + 1) : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_right hn (by omega)
    have hval : ((n ^ κ : ℕ) : ℤ) * n = ((n ^ (κ + 1) : ℕ) : ℤ) := by
      push_cast
      ring
    unfold _root_.ThreeSum1960614.Machine.Light.powStmt
    refine _root_.ThreeSum1960614.Machine.Light.Ends.next (4 * κ) ((pow_spec__implementation_d1cc9bc2b7 hn a μ κ (hle.trans hw)).mono le_rfl ?_)
    rintro _ rfl
    -- U := U * n
    refine _root_.ThreeSum1960614.Machine.Light.Ends.setTo ((n ^ (κ + 1) : ℕ) : ℤ) rfl ⟨?_, ?_⟩
    · (simp only [_root_.ThreeSum1960614.Machine.Light.Expr.Safe, _root_.ThreeSum1960614.Machine.Light.Expr.val, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.Light.Op.eval, _root_.ThreeSum1960614.Machine.Light.Cond.Holds, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Cond.Safe, _root_.Function.update_apply, _root_.reduceIte, _root_.true_and, _root_.and_true, _root_.Nat.reduceEqDiff, _root_.Nat.cast_ofNat, _root_.Nat.cast_zero, _root_.Nat.cast_one, ])
      change |((n ^ κ : ℕ) : ℤ) * n| ≤ lim.word
      rw [hval, abs_of_nonneg (Int.natCast_nonneg _)]
      exact hw
    · exact hval
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.pow_spec__implementation_d1cc9bc2b7) := (@ThreeSum1960614.Machine.Light.pow_spec__implementation_d1cc9bc2b7)

#print axioms solution
