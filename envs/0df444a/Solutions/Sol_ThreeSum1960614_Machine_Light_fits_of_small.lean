-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.fits_of_small
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:15:17.331556+00:00
-- url     : https://prove2.me/submissions/5b554c88-84a2-40fa-aab8-c14e645888e9

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
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
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Matrix.Notation
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_polyBound_le

local instance platformRadixNonzero_3e8819aea1 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Light
end Light
namespace Light.Compiler
end Light.Compiler
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Compiler
end ThreeSum1960614.Machine.Light.Compiler
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







/-- The bound is positive. -/
theorem one_le_polyBound (s k : ℕ) (params : List ℕ) : 1 ≤ _root_.Light.polyBound s k params := by
  have : 0 < (params.map (· + 1)).prod := List.prod_pos (by simp)
  exact Nat.mul_pos (by positivity) (by positivity)









/-- A power of two times the bound is a bound of the same form. -/
theorem polyBound_mul (s s' k : ℕ) (params : List ℕ) :
    2 ^ s' * _root_.Light.polyBound s k params = _root_.Light.polyBound (s' + s) k params := by
  simp only [_root_.Light.polyBound, pow_add, mul_assoc]



end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# From runs of light programs to the running-time notions of the word RAM

`Solves` says what it means that a program of the word RAM solves a problem within a time bound, and
`IsDataStructure` that two programs form a data structure.  This file gives the corresponding
notions for light programs (`ProgramSolves`, `ProgramIsDataStructure`; what they ask on one instance
are the structures `ProgramSolvesAt` and `ProgramIsDataStructureAt`), which speak only about `Exec`,
and proves that the compiled programs satisfy the notions of the word RAM with time C · T + C, where
C depends on the compiled program only (`solves_of_programSolves`, `isDataStructure_of_program`).

1. **Word size.**  The limits of the run are polynomial in the parameters of the instance (`Small`),
   so they fit every admissible word size of slope `slopeOf` (`fits_of_small`).
2. **Time and space.**  c steps become at most C · c + C steps (`ramSteps_le`); calls nested d deep
   reach at most C · d + C cells below 0 (`lowCell_le`).
3. **Runs.**  Each run is one use of `compileProgram_correct`.  A solver is one run from the initial
   memory (`input_loadWords`).  A data structure is one such run for the preprocessing and then an
   induction on the list of queries, each of them one run (`serves_of_program`).
4. **From specifications.**  The runs that the two notions ask for come from specifications of the
   procedures (`Meets.main`, `AnswersQueries.of_meets`).
5. **The additive constant.**  If T ≥ 1, the bound C · (A · T) + C is at most C (A + 1) · T
   (`solves_of_programSolves_scaled`, `isDataStructure_of_program_scaled`).
-/

@[expose] public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.Light.Compiler
open _root_.ThreeSum1960614.Machine.Light.Compiler
open _root_.EndStatement renaming exec -> exec
open _root_.EndStatement renaming loadWords -> loadWords

/-! ## The notion for light programs -/









/-! ## The word size -/







section

/-- The word size fits the limits if the limits, the largest number N of the pool and the number Q
of cells of the stack, with the factors of `Fits`, are below a number B ≤ 2^W. -/
private theorem private_aa99180050_fits_of_lt {W : ℕ} {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {N Q B : ℕ} (hB : B ≤ 2 ^ W)
    (hword : 2 * (2 * lim.word + 2) < (B : ℤ)) (hspace : 2 * lim.space < B) (hstack : 4 * Q < B)
    (hpool : 2 * N < B) : _root_.ThreeSum1960614.Machine.Light.Compiler.Fits W lim N Q := by
  have hB' : (B : ℤ) ≤ (2 : ℤ) ^ W := by exact_mod_cast hB
  constructor <;> omega
end




/-! ## Time and space -/













/-! ## Runs from the initial memory -/

section run

variable {W : ℕ} {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ → ℤ}





end run

/-! ## Solvers -/



/-! ## The two-stage data structure -/















/-! ## Absorbing the additive constant -/







end Light

end

end ThreeSum1960614.Machine

section
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.Light.Compiler
open _root_.ThreeSum1960614.Machine.Light.Compiler
open _root_.EndStatement renaming exec -> exec
open _root_.EndStatement renaming loadWords -> loadWords
section

/-- Limits that are polynomial in the parameters fit every admissible word size. -/
theorem ThreeSum1960614.Machine.Light.fits_of_small__implementation_707914a4b2 {W s k r b : ℕ} {params : List ℕ} {lim : _root_.ThreeSum1960614.Machine.Light.Limits} (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool)
    (h : _root_.ThreeSum1960614.Machine.Light.Small s k params lim) (hadm : _root_.ThreeSumApsp.WordRam.Admissible b params W) (hr : params.length ≤ r)
    (hb : _root_.ThreeSum1960614.Machine.Light.slopeOf P dec s k r ≤ b) : _root_.ThreeSum1960614.Machine.Light.Compiler.Fits W lim (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) (_root_.ThreeSum1960614.Machine.Light.Compiler.stackCells P lim) := by
  have hword := h.word
  have hspace := h.space
  have hdepth := h.depth
  set pb := _root_.Light.polyBound s k params with hpb
  have hpb_pos : 1 ≤ pb := _root_.ThreeSum1960614.Machine.Light.one_le_polyBound s k params
  -- the text's constant times the polynomial is below 2^W
  have hB : 2 ^ _root_.ThreeSum1960614.Machine.Light.textBoundBits P dec * pb ≤ 2 ^ W := by
    rw [hpb, _root_.ThreeSum1960614.Machine.Light.polyBound_mul]
    exact _root_.ThreeSum1960614.Machine.Light.polyBound_le hadm hr (by unfold _root_.ThreeSum1960614.Machine.Light.slopeOf at hb; omega)
  have hlt : _root_.ThreeSum1960614.Machine.Light.textBound P dec * pb < 2 ^ _root_.ThreeSum1960614.Machine.Light.textBoundBits P dec * pb :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) hpb_pos
  have htext : _root_.ThreeSum1960614.Machine.Light.textBound P dec * pb
      = 32 * pb + 8 * ((_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P + 1) * pb) + 2 * (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec * pb) := by
    unfold _root_.ThreeSum1960614.Machine.Light.textBound; ring
  -- and each of the four numbers is below the text's constant times the polynomial
  have hstack : (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P + 1) * (lim.depth + 1) ≤ 2 * ((_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P + 1) * pb) :=
    (Nat.mul_le_mul_left _ (by omega : lim.depth + 1 ≤ 2 * pb)).trans_eq (by ring)
  have hpool : _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec ≤ _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec * pb := Nat.le_mul_of_pos_right _ hpb_pos
  refine _root_.ThreeSum1960614.Machine.Light.private_aa99180050_fits_of_lt hB ?_ ?_ ?_ ?_
  · -- 2 (2 word + 2) ≤ 4 pb + 4 ≤ 8 pb
    have : ((8 * pb : ℕ) : ℤ) < ((2 ^ _root_.ThreeSum1960614.Machine.Light.textBoundBits P dec * pb : ℕ) : ℤ) := by
      exact_mod_cast (by omega : 8 * pb < 2 ^ textBoundBits P dec * pb)
    omega
  · -- 2 space ≤ 2 pb
    omega
  · -- 4 (4 + (F + 1) (depth + 1)) ≤ 16 pb + 8 (F + 1) pb
    unfold _root_.ThreeSum1960614.Machine.Light.Compiler.stackCells _root_.Light.Compiler.mainFrame
    omega
  · -- 2 N ≤ 2 N pb
    omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.fits_of_small__implementation_707914a4b2) := (@ThreeSum1960614.Machine.Light.fits_of_small__implementation_707914a4b2)

#print axioms solution
