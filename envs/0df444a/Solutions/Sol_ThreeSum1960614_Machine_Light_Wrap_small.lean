-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.Wrap.small
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:10:20.090985+00:00
-- url     : https://prove2.me/submissions/2c59c065-3590-49c5-8878-6b574dd75a3a

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

local instance platformRadixNonzero_e89cc4a1b6 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
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

namespace ThreeSum1960614.Machine

/-!
# From a solver of a task to a program for the layout of the end statement

A solver gets its size, the bound on the numbers and its addresses as arguments.  A problem of the
end statement has a fixed layout: cell 0 holds the size n, then comes the input, then the output;
the bound U = n^κ is not in the memory.  For every κ one more procedure, `topBody`, is appended to
the program of the solver.  It reads n.  At size 0 it answers at once.  Otherwise it forms U = n^κ
by κ multiplications and n², computes the addresses, calls the solver, and returns the result of
the solver (for a decision problem) or 1.

`Wrap` collects what has to be said about a problem and a task for this to work.  `Wrap.body_ends`
and `Wrap.body_ends_zero` follow the procedure through its text, `Wrap.small` bounds the word size,
the memory and the depth that the run needs by a polynomial in n, and `Wrap.realized` is the
conclusion: if the task is solved in time T, then the problem is solved on the word RAM within a
constant times T.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











/-! ## The problems of `EndStatement` -/

section OfEnd

variable {Q : _root_.EndStatement.Problem} (x : _root_.ThreeSumApsp.WordRam.Bounded Q)







end OfEnd

/-! ## Polynomials in the size -/

section

/-- A polynomial in `n` and `U = n^κ` is a polynomial in `n`. -/
private theorem private_8c12ab8a9b_polyBound_pow_le (s k κ n : ℕ) {r : ℕ} (hr : (κ + 1) * k ≤ r) :
    _root_.Light.polyBound s k [n, n ^ κ] ≤ 2 ^ (s + k) * (n + 1) ^ r := by
  have hpos : 1 ≤ n + 1 := by omega
  have hU : n ^ κ + 1 ≤ 2 * (n + 1) ^ κ := by
    have h1 : n ^ κ ≤ (n + 1) ^ κ := Nat.pow_le_pow_left (by omega) κ
    have h2 : 1 ≤ (n + 1) ^ κ := Nat.one_le_pow _ _ hpos
    omega
  unfold _root_.Light.polyBound
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  calc 2 ^ s * ((n + 1) * (n ^ κ + 1)) ^ k
      ≤ 2 ^ s * ((n + 1) * (2 * (n + 1) ^ κ)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hU) k)
    _ = 2 ^ (s + k) * (n + 1) ^ ((κ + 1) * k) := by
        rw [show (n + 1) * (2 * (n + 1) ^ κ) = 2 * (n + 1) ^ (κ + 1) by ring, mul_pow, ← pow_mul,
          pow_add]
        ring
    _ ≤ 2 ^ (s + k) * (n + 1) ^ r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos hr)
end




namespace Wrap
open _root_.Light.Wrap


variable {Q : _root_.EndStatement.Problem} {task : _root_.Light.Task} {dec : Bool}

























end Wrap

end Light

end

end ThreeSum1960614.Machine

section
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
open _root_.ThreeSum1960614.Machine.Light.Wrap

variable {Q : _root_.EndStatement.Problem} {task : _root_.Light.Task} {dec : Bool}
section

/-- The limits are polynomial in the size. -/
theorem ThreeSum1960614.Machine.Light.Wrap.small__implementation_b13e428d34 (w : _root_.ThreeSum1960614.Machine.Light.Wrap Q task dec) {need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need} (hpoly : _root_.ThreeSum1960614.Machine.Light.PolyNeed need) (κ : ℕ) :
    ∃ s k : ℕ, ∀ x : _root_.ThreeSumApsp.WordRam.Bounded Q, x.U = x.n ^ κ → _root_.ThreeSum1960614.Machine.Light.Small s k [x.n] (w.limits need x) := by
  obtain ⟨s, k, hpoly⟩ := hpoly
  obtain ⟨r, hr⟩ : ∃ r, r = (κ + 1) * k + κ + 2 := ⟨_, rfl⟩
  refine ⟨s + k + 5 + Nat.size w.cst, r, fun x hU => ?_⟩
  obtain ⟨hword, hcells, hdepth⟩ := hpoly x.n x.U
  have hpos : 1 ≤ x.n + 1 := by omega
  have hneed := _root_.ThreeSum1960614.Machine.Light.private_8c12ab8a9b_polyBound_pow_le s k κ x.n (r := r) (by omega)
  have hsquare : x.n * x.n + 1 ≤ (x.n + 1) ^ r :=
    (by nlinarith : x.n * x.n + 1 ≤ (x.n + 1) ^ 2).trans (Nat.pow_le_pow_right hpos (by omega))
  have hbound : x.n ^ κ ≤ (x.n + 1) ^ r :=
    (Nat.pow_le_pow_left (by omega) κ).trans (Nat.pow_le_pow_right hpos (by omega))
  have hsize : x.n + 1 ≤ (x.n + 1) ^ r := Nat.le_self_pow (by omega) _
  have hfr := w.fr_le x
  rw [← hU] at hneed hbound
  -- `X` bounds the parts that do not come from the solver, `Z ≥ X` those that do
  have hXZ : (x.n + 1) ^ r ≤ 2 ^ (s + k) * (x.n + 1) ^ r := Nat.le_mul_of_pos_left _ (by positivity)
  have hgoal : _root_.Light.polyBound (s + k + 5 + Nat.size w.cst) r [x.n] =
      32 * (2 ^ Nat.size w.cst * (2 ^ (s + k) * (x.n + 1) ^ r)) := by
    unfold _root_.Light.polyBound
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [pow_add 2 (s + k + 5) (Nat.size w.cst), pow_add 2 (s + k) 5]
    ring
  generalize 2 ^ (s + k) * (x.n + 1) ^ r = Z at *
  generalize (x.n + 1) ^ r = X at *
  -- `Y ≥ Z` takes in the constant of the layout
  have hcst : w.cst * (x.n * x.n + 1) ≤ 2 ^ Nat.size w.cst * Z :=
    Nat.mul_le_mul (Nat.lt_size_self w.cst).le (hsquare.trans hXZ)
  have hZY : Z ≤ 2 ^ Nat.size w.cst * Z := Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  generalize 2 ^ Nat.size w.cst * Z = Y at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [_root_.ThreeSum1960614.Machine.Light.Wrap.limits, hgoal] <;> omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.Wrap.small__implementation_b13e428d34) := (@ThreeSum1960614.Machine.Light.Wrap.small__implementation_b13e428d34)

#print axioms solution
