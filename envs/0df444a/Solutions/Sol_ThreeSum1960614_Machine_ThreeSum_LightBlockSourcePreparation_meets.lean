-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:28:42.522136+00:00
-- url     : https://prove2.me/submissions/7d7fb41a-f4a4-40bc-b0c2-b6db6a61fc16

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BlockIndex_maskHash_left
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BlockIndex_maskHash_right
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverSchedule_indices_lt
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverSchedule_indices_map
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourcePreparation_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LocalMaskHashes_indexed_bucket_count
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_maskOf
import Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
namespace ThreeSum.BlockSourceRows
end ThreeSum.BlockSourceRows
namespace ThreeSum.BooleanGreedy
end ThreeSum.BooleanGreedy
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightBlockSourcePreparation
end ThreeSum.LightBlockSourcePreparation
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightMaskBits
end ThreeSum.LightMaskBits
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceFlagTest
end ThreeSum.LightSourceFlagTest
namespace ThreeSum.LightSourceRowFlag
end ThreeSum.LightSourceRowFlag
namespace ThreeSum.LightSourceRowScan
end ThreeSum.LightSourceRowScan
namespace ThreeSum.LightSourceTrim
end ThreeSum.LightSourceTrim
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.LocalMaskHashes
end ThreeSum.LocalMaskHashes
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
end ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceRows
end ThreeSum1960614.Machine.ThreeSum.BlockSourceRows
namespace ThreeSum1960614.Machine.ThreeSum.BooleanGreedy
end ThreeSum1960614.Machine.ThreeSum.BooleanGreedy
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.LayerCounts
end ThreeSum1960614.Machine.ThreeSum.LayerCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskBits
end ThreeSum1960614.Machine.ThreeSum.LightMaskBits
namespace ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
end ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest
end ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag
end ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan
end ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceTrim
end ThreeSum1960614.Machine.ThreeSum.LightSourceTrim
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
end ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
end ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.OneHotMask
end ThreeSum1960614.Machine.ThreeSum.OneHotMask
namespace ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
end ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# The concrete local subset graph and its binary words

A left vertex has ones exactly on its `h`-subset.  A right vertex has zeros
exactly on its `h`-subset.  The endpoint maps, their separation, and the
equality mask are proved directly from finite-set membership.
-/

namespace ThreeSum.LocalGraph
open _root_.ThreeSum.LocalGraph


variable {α : Type*} [DecidableEq α]





theorem leftWord_injective : Function.Injective (@_root_.ThreeSum.LocalGraph.leftWord α _) := by
  intro s t he
  ext i
  simpa only [_root_.ThreeSum.LocalGraph.leftWord, decide_eq_decide] using congrFun he i

theorem rightWord_injective : Function.Injective (@_root_.ThreeSum.LocalGraph.rightWord α _) := by
  intro s t he
  ext i
  have hi := congrFun he i
  simpa only [_root_.ThreeSum.LocalGraph.rightWord, decide_eq_decide, not_iff_not] using hi









section ConcreteGraph

open _root_.ThreeSum.LayerCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.LayerCounts



variable {L h : ℕ}

















































end ConcreteGraph

end ThreeSum.LocalGraph

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Deleting one coordinate from an integer subset mask

The routine inspects the highest remaining power of two at each recursive
step. It uses no division or scan proportional to the mask's numeric value.
-/

namespace ThreeSum.MaskErase
open _root_.ThreeSum.MaskErase


open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress









theorem natPositions_erase {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.SubsetAddress.natPositions (s.erase a) = (_root_.ThreeSum.SubsetAddress.natPositions s).erase a.val := by
  exact Finset.map_erase Fin.valEmbedding s a

theorem eraseMask_subsetMask {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask s) = _root_.ThreeSum.SubsetAddress.subsetMask (s.erase a) := by
  rw [_root_.ThreeSum.SubsetAddress.subsetMask, _root_.ThreeSum.MaskErase.eraseMask_maskOf _ (_root_.ThreeSum.SubsetAddress.natPositions_subset s),
    ← _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.natPositions_erase, ← _root_.ThreeSum.SubsetAddress.subsetMask]

theorem eraseMask_ne_iff {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask s) ≠ _root_.ThreeSum.SubsetAddress.subsetMask s ↔ a ∈ s := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_subsetMask, (_root_.ThreeSum.SubsetAddress.subsetMask_injective L).ne_iff, Finset.erase_ne_self]





end ThreeSum.MaskErase

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Conjunction represented by the product of independently computed flags -/

namespace ThreeSum.SourceFlagProduct
open _root_.ThreeSum.SourceFlagProduct


open _root_.Finset
open scoped _root_.BigOperators



@[simp] theorem product_zero (flag : ℕ → ℕ) : _root_.ThreeSum.SourceFlagProduct.product flag 0=1 := by simp [_root_.ThreeSum.SourceFlagProduct.product]

theorem product_succ (flag : ℕ → ℕ) (n : ℕ) :
    _root_.ThreeSum.SourceFlagProduct.product flag (n+1)=_root_.ThreeSum.SourceFlagProduct.product flag n*flag n := Finset.prod_range_succ _ _

theorem product_le {n j : ℕ} (flag : ℕ → ℕ)
    (hflag : ∀ i < n, flag i ≤ 1) (hj : j ≤ n) : _root_.ThreeSum.SourceFlagProduct.product flag j ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct.product_succ]
    exact (Nat.mul_le_mul (ih (by omega)) (hflag j (by omega))).trans (by decide)

theorem product_eq_one_iff (flag : ℕ → ℕ) (n : ℕ) :
    _root_.ThreeSum.SourceFlagProduct.product flag n=1 ↔ ∀ i < n, flag i=1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct.product_succ,mul_eq_one,ih]
    constructor
    · rintro ⟨hprev,hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hprev i hi
      · exact hn
    · intro hall
      exact ⟨fun i hi => hall i (by omega),hall n (by omega)⟩

theorem product_eq_indicator (flag : ℕ → ℕ) (n : ℕ) (p : Prop) [Decidable p]
    (hflag : ∀ i < n, flag i ≤ 1) (hp : (∀ i < n, flag i=1) ↔ p) :
    _root_.ThreeSum.SourceFlagProduct.product flag n = if p then 1 else 0 := by
  have he := (_root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct.product_eq_one_iff flag n).trans hp
  have hle := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct.product_le flag hflag le_rfl
  by_cases hh : p
  · simp only [hh,ite_true]
    exact he.mpr hh
  · simp only [hh,ite_false]
    have hn : _root_.ThreeSum.SourceFlagProduct.product flag n≠1 := fun h => hh (he.mp h)
    omega

end ThreeSum.SourceFlagProduct

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Specifications of procedures -/



section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}



/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩







end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} {s : _root_.ThreeSum1960614.Machine.Light.Stmt}









end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy
open _root_.ThreeSum.BooleanGreedy


open _root_.Finset
open scoped _root_.BigOperators



























theorem choices_length (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    (_root_.ThreeSum.BooleanGreedy.choices matrix rows cols t).length = t := _root_.ThreeSum.Cover.greedyChoices_length ..



end ThreeSum.BooleanGreedy

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalEncoding


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments


























theorem rawHash_cast {h L : ℕ} (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (s : Fin L → Bool) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w s : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) = _root_.ThreeSum.HashFamily.hashValue w s := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash, _root_.ThreeSum.HashFamily.hashValue]

































































end ThreeSum.GlobalEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram
open _root_.ThreeSum.LightHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





theorem count_le (key : ℕ → ℕ) (r i : ℕ) : _root_.ThreeSum.LightHistogram.count key r i ≤ i := by
  exact (Finset.card_filter_le _ _).trans (by simp)















end ThreeSum.LightHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits
open _root_.ThreeSum.LightMaskBits


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase





theorem bit_subsetMask {L : ℕ} (s : Finset (Fin L)) (j : Fin L) :
    _root_.ThreeSum.LightMaskBits.bit L (_root_.ThreeSum.SubsetAddress.subsetMask s) j.val = if j ∈ s then 1 else 0 := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_ne_iff s j
  unfold _root_.ThreeSum.LightMaskBits.bit
  split <;> split <;> simp_all











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightMaskBits

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues
open _root_.ThreeSum.LightResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (_root_.ThreeSum.LightResidues.residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

theorem residue_lt {p : ℕ} (hp : 0 < p) (c x : ℤ) : _root_.ThreeSum.LightResidues.residue p c x < p := by
  have h := Int.emod_lt_of_pos (c * x) (by exact_mod_cast hp : (0 : ℤ) < p)
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hp] at h
  exact_mod_cast h















end ThreeSum.LightResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Independent cardinality-and-bucket trimming test -/

namespace ThreeSum.LightSourceFlagTest
open _root_.ThreeSum.LightSourceFlagTest


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light



theorem flag_le (card required count cap : ℕ) : _root_.ThreeSum.LightSourceFlagTest.flag card required count cap ≤ 1 := by
  unfold _root_.ThreeSum.LightSourceFlagTest.flag
  split <;> omega

theorem flag_eq_one (card required count cap : ℕ) :
    _root_.ThreeSum.LightSourceFlagTest.flag card required count cap=1 ↔ card=required ∧ count≤cap := by
  unfold _root_.ThreeSum.LightSourceFlagTest.flag
  split <;> simp_all





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightSourceFlagTest

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original integers to a padded signed histogram

The executable procedure first computes canonical residues of the signed
original integers and then fills the entire requested histogram capacity.
Its postcondition is the precise padded polynomial vector consumed by the
verified cyclic-convolution routine. Repeated input values remain distinct
incidences and contribute their full multiplicity.
-/

namespace ThreeSum.LightResidueHistogram
open _root_.ThreeSum.LightResidueHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem residue_zmod {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (_root_.ThreeSum.LightResidues.residue p c x : ZMod p) = ((c * x : ℤ) : ZMod p) := by
  unfold _root_.ThreeSum.LightResidues.residue
  rw [ZMod.natCast_toNat p (Int.emod_nonneg _ (by exact_mod_cast hp.ne')),
    ZMod.intCast_mod]

























end ThreeSum.LightResidueHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing both independent trimming flags for one block row

The program counts and hashes the actual Boolean row, reduces both local
hashes, reads the selected map's retained bucket tables, and independently
tests the two endpoint buckets. The cardinality test is performed for both
orientations, with no disjoint-pair or shared trimming assumption.
-/

namespace ThreeSum.LightSourceRowFlag
open _root_.ThreeSum.LightSourceRowFlag


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000



theorem flag_le (L h p cap : ℕ) (bits w0 w1 hist : ℕ → ℕ) :
    _root_.ThreeSum.LightSourceRowFlag.flag L h p cap bits w0 w1 hist ≤ 1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.flag_le ..









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightSourceRowFlag

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete integer indices for the local disjoint-subset graph

The finite list is the already checked layer-mask enumeration. Its Boolean
coordinate rows make disjointness an ordinary zero Boolean inner product.
-/

namespace ThreeSum.LocalMaskGraph
open _root_.ThreeSum.LocalMaskGraph


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskDecode
open scoped _root_.BigOperators







theorem maskAt_spec {L h i : ℕ} (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L h) :
    _root_.ThreeSum.SubsetAddress.IsMask L h (_root_.ThreeSum.LocalMaskGraph.maskAt L h i) := (_root_.ThreeSum.SubsetAddress.mem_enumerateLayer L h _).mp (_root_.ThreeSum.LocalMaskGraph.maskAt_mem hi)



theorem subsetMask_setAt {L h i : ℕ} (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L h) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.LocalMaskGraph.setAt L h i) = _root_.ThreeSum.LocalMaskGraph.maskAt L h i := _root_.ThreeSum.MaskDecode.subsetMask_decode (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.maskAt_spec hi).1















end ThreeSum.LocalMaskGraph

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask
open _root_.ThreeSum.OneHotMask


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false











@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    _root_.ThreeSum.OneHotMask.extend f i.val = f i := by simp [_root_.ThreeSum.OneHotMask.extend, i.isLt]

@[simp] theorem mem_natPositions {L : ℕ} (s : Finset (Fin L)) (i : Fin L) :
    i.val ∈ _root_.ThreeSum.SubsetAddress.natPositions s ↔ i ∈ s := by
  simp only [_root_.ThreeSum.SubsetAddress.natPositions, mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    have hai : a = i := Fin.ext he
    simpa only [hai] using ha
  · intro hi
    exact ⟨i,hi,rfl⟩

theorem eval_subsetMask {L : ℕ} (s : Finset (Fin L)) (w0 w1 : Fin L → ℕ) :
    _root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.OneHotMask.extend w0) (_root_.ThreeSum.OneHotMask.extend w1) L (_root_.ThreeSum.SubsetAddress.subsetMask s) =
      ∑ i : Fin L, if i ∈ s then w1 i else w0 i := by
  rw [_root_.ThreeSum.SubsetAddress.subsetMask, _root_.ThreeSum.OneHotMask.eval_maskOf _ (_root_.ThreeSum.SubsetAddress.natPositions_subset s), Finset.sum_range]
  apply sum_congr rfl
  intro i _
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.extend_fin, _root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.mem_natPositions]

theorem eval_rawLeft {h L : ℕ}
    (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (s : Finset (Fin L)) :
    (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,false)).val) (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,true)).val)
      L (_root_.ThreeSum.SubsetAddress.subsetMask s) : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w (_root_.ThreeSum.LocalGraph.leftWord s) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.eval_subsetMask]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash
  push_cast
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [_root_.ThreeSum.LocalGraph.leftWord, hi]

theorem eval_rawRight {h L : ℕ}
    (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (s : Finset (Fin L)) :
    (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,true)).val) (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,false)).val)
      L (_root_.ThreeSum.SubsetAddress.subsetMask s) : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w (_root_.ThreeSum.LocalGraph.rightWord s) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.eval_subsetMask]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash
  push_cast
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [_root_.ThreeSum.LocalGraph.rightWord, hi]

end ThreeSum.OneHotMask

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Explicit row-major encoding of the block ground set

Block coordinates are numbered by `block * width + coordinate`. The
equivalence connects compact machine-mask tables on `Fin (J*L)` with the
sigma-typed block sets in the reporting proof. Flattened one-hot coefficients
already include their positional radix factors.
-/

namespace ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndex


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false



@[simp] theorem coordEquiv_val {J L : ℕ} (i : Fin J) (x : Fin L) :
    (_root_.ThreeSum.BlockIndex.coordEquiv J L ⟨i,x⟩).val = i.val*L+x.val := by
  simp [_root_.ThreeSum.BlockIndex.coordEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]





@[simp] theorem mem_indexSet {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) (c : _root_.ThreeSum.BlockRows.Coord J L) :
    _root_.ThreeSum.BlockIndex.coordEquiv J L c ∈ _root_.ThreeSum.BlockIndex.indexSet S ↔ c ∈ S := by
  simp [_root_.ThreeSum.BlockIndex.indexSet]

























end ThreeSum.BlockIndex

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Independent endpoint trimming across all selected blocks

The loop reads each occurrence index and its exact selected-candidate index,
then calls the concrete row flag constructor on the corresponding map and
retained bucket tables. The product of the independent Boolean flags is
written in each orientation. Input Boolean rows and tables are preserved.
-/

namespace ThreeSum.LightSourceTrim
open _root_.ThreeSum.LightSourceTrim


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000



theorem rowFlag_le (L h p cap : ℕ) (sel candidate bits : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (j : ℕ) :
    _root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w0 w1 counts j ≤ 1 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.flag_le ..











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightSourceTrim

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact hash codes and bucket counts for enumerated local vertices

The finite graph used in the moment proof is identified with the literal
mask list consumed by the machine.  In particular, the machine histogram
counts exactly the graph's endpoint buckets, including multiplicities.
-/

namespace ThreeSum.LocalMaskHashes
open _root_.ThreeSum.LocalMaskHashes


open _root_.Finset
open _root_.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

variable {h L k : ℕ}









theorem leftCode_lt (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (k i : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k i < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode _root_.ThreeSum.LightHashHistogram.code
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) 1 _

theorem rightCode_lt (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (k i : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k i < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode _root_.ThreeSum.LightHashHistogram.code
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) 1 _

theorem leftCode_cast (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) {i : ℕ}
    (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L k) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k i : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) =
      _root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.leftWord (_root_.ThreeSum.LocalMaskGraph.setAt L k i)) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode _root_.ThreeSum.LightHashHistogram.code _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.coeff
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.residue_zmod (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h),one_mul,
    ← _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.subsetMask_setAt hi,_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.eval_rawLeft,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash_cast]

theorem rightCode_cast (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) {i : ℕ}
    (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L k) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k i : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) =
      _root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.rightWord (_root_.ThreeSum.LocalMaskGraph.setAt L k i)) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode _root_.ThreeSum.LightHashHistogram.code _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.coeff
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.residue_zmod (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h),one_mul,
    ← _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.subsetMask_setAt hi,_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.eval_rawRight,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash_cast]







theorem left_count (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) {r : ℕ} (hr : r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) :
    _root_.ThreeSum.LightHistogram.count (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k) r (_root_.ThreeSum.LocalMaskGraph.vertexCount L k) =
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.leftVertices L k) w (r : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.indexed_bucket_count w _root_.ThreeSum.LocalGraph.leftWord _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph.leftWord_injective
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k) (fun i _ => _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode_lt w k i) (fun _ hi => _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode_cast w hi) hr

theorem right_count (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) {r : ℕ} (hr : r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) :
    _root_.ThreeSum.LightHistogram.count (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k) r (_root_.ThreeSum.LocalMaskGraph.vertexCount L k) =
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.rightVertices L k) w (r : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.indexed_bucket_count w _root_.ThreeSum.LocalGraph.rightWord _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph.rightWord_injective
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k) (fun i _ => _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode_lt w k i) (fun _ hi => _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode_cast w hi) hr

end ThreeSum.LocalMaskHashes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Reading constructed block coefficients in the flat mask order

The imperative coefficient constructor writes rows. The mask evaluator reads
one flat array. These lemmas identify the two layouts, including empty ground
sets, and specialize them to the unchanged schedule-occurrence encoding.
-/

namespace ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.BlockCoefficientRows


open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds









@[simp] theorem occurrenceIndices_fin {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (i : Fin J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o i.val = (o i).val := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.extend_fin _ i



@[simp] theorem mapRow_fin {h : ℕ} (b : Bool) (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) (i : Fin (464*h)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h b s.val i.val = (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h s (i,b)).val := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow,s.isLt,dite_true,_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.extend_fin]

theorem occurrenceIndices_lt {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) {j : ℕ} (hj : j < J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o j < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h := by
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices_fin o ⟨j,hj⟩).trans_lt (o ⟨j,hj⟩).isLt

theorem mapRow_le {h : ℕ} (b : Bool) {s i : ℕ}
    (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (hi : i < 464*h) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h b s i ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow_fin b ⟨s,hs⟩ ⟨i,hi⟩]
  exact Nat.le_of_lt (ZMod.val_lt _)

theorem flat_coefficient {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (b : Bool) :
    _root_.ThreeSum.BlockCoefficientRows.flat J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h b) =
      _root_.ThreeSum.OneHotMask.extend (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.coefficient o b ∘ (_root_.ThreeSum.BlockIndex.coordEquiv J (464*h)).symm) := by
  unfold _root_.ThreeSum.BlockCoefficientRows.flat
  apply congrArg _root_.ThreeSum.OneHotMask.extend
  funext i
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices_fin,_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow_fin,Function.comp_apply,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.coefficient]

theorem eval_left {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J)
    (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :
    (_root_.ThreeSum.OneHotMask.eval
      (_root_.ThreeSum.BlockCoefficientRows.flat J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false))
      (_root_.ThreeSum.BlockCoefficientRows.flat J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true))
      (J*(464*h)) (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet S)) : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft o S := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.flat_coefficient,_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.flat_coefficient]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.maskHash_left o S

theorem eval_right {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J)
    (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :
    (_root_.ThreeSum.OneHotMask.eval
      (_root_.ThreeSum.BlockCoefficientRows.flat J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true))
      (_root_.ThreeSum.BlockCoefficientRows.flat J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false))
      (J*(464*h)) (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet S)) : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o S := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.flat_coefficient,_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.flat_coefficient]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.maskHash_right o S

end ThreeSum.BlockCoefficientRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact local schedule occurrence indices

The machine's Boolean matrix uses radix-indexed candidate rows and ordered
residue-pair columns. These changes of representation preserve the entire
original local schedule, including ties and repeated selected maps.
-/

namespace ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum.LightLocalCoverSchedule


open _root_.Finset
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding




















theorem indices_length (h : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).length = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BooleanGreedy.choices_length ..





theorem candidateAt_lt (h : ℕ) (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h := by
  have hs : s.val < (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).length := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_length]; exact s.isLt
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt
  rw [List.getD_eq_getElem _ _ hs]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_lt h (List.getElem_mem hs)

theorem candidateAt_mapAt (h : ℕ) (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h s := by
  have hs : s.val < (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).length := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_length]; exact s.isLt
  have hs' : s.val < (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule h).length := by
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize_eq_length]
    exact s.isLt
  have he := congrArg (fun xs : List (_root_.ThreeSum.LocalHashMoments.Weight (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) => xs.getD s.val default) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_map h)
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hs),List.getElem_map,
    List.getD_eq_getElem _ _ hs'] at he
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt
  rw [List.getD_eq_getElem _ _ hs]
  exact he

theorem leftCount_candidateAt (h : ℕ) (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) {r : ℕ} (hr : r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.leftCount (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s)) h r =
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.leftVertices (464*h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h s) (r : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.leftCount
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.left_count _ hr,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt_mapAt]

theorem rightCount_candidateAt (h : ℕ) (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) {r : ℕ} (hr : r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.rightCount (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s)) h r =
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.rightVertices (464*h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h s) (r : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.rightCount
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.right_count _ hr,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt_mapAt]



end ThreeSum.LightLocalCoverSchedule

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Global mask bits are the exact local block rows

The physical row scan's cardinality and two raw hashes agree with the local
subsets and one-hot words in `BlockEncoding`. This bridge allows independent
trimming to use the selected map's exact retained bucket-count table.
-/

namespace ThreeSum.BlockSourceRows
open _root_.ThreeSum.BlockSourceRows


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.LightSourceRowScan
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000



theorem bits_fin {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) (j : Fin J) (i : Fin L) :
    _root_.ThreeSum.BlockSourceRows.bits S j i.val = if i ∈ _root_.ThreeSum.BlockRows.row S j then 1 else 0 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.bit_subsetMask (_root_.ThreeSum.BlockIndex.indexSet S) (_root_.ThreeSum.BlockIndex.coordEquiv J L ⟨j,i⟩)
  simpa only [_root_.ThreeSum.BlockSourceRows.bits,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.coordEquiv_val,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.mem_indexSet,_root_.ThreeSum.BlockRows.mem_row] using hh

theorem count_eq_card {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) (j : Fin J) :
    _root_.ThreeSum.LightSourceRowScan.count (_root_.ThreeSum.BlockSourceRows.bits S j) L = (_root_.ThreeSum.BlockRows.row S j).card := by
  rw [_root_.ThreeSum.LightSourceRowScan.count,← Fin.sum_univ_eq_sum_range]
  have he : _root_.ThreeSum.BlockRows.row S j = (univ : Finset (Fin L)).filter (fun i => i ∈ _root_.ThreeSum.BlockRows.row S j) := by
    ext i
    simp
  conv_rhs => rw [he,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceRows.bits_fin S j i

theorem hash_eq_eval {L : ℕ} (s : Finset (Fin L)) (b : ℕ → ℕ)
    (w0 w1 : Fin L → ℕ) (hb : ∀ i : Fin L, b i.val = if i ∈ s then 1 else 0) :
    _root_.ThreeSum.LightSourceRowScan.hash b (_root_.ThreeSum.OneHotMask.extend w0) (_root_.ThreeSum.OneHotMask.extend w1) L =
      _root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.OneHotMask.extend w0) (_root_.ThreeSum.OneHotMask.extend w1)
        L (_root_.ThreeSum.SubsetAddress.subsetMask s) := by
  unfold _root_.ThreeSum.LightSourceRowScan.hash
  rw [← Fin.sum_univ_eq_sum_range,_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.eval_subsetMask]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hb i,_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.extend_fin,_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.extend_fin]
  by_cases hmem : i ∈ s <;> simp [hmem]

theorem left_hash {h J : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) (j : Fin J)
    (w : _root_.ThreeSum.LocalHashMoments.Weight (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) :
    (_root_.ThreeSum.LightSourceRowScan.hash (_root_.ThreeSum.BlockSourceRows.bits S j) (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,false)).val)
      (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,true)).val) (464*h) : ℤ) =
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w (_root_.ThreeSum.LocalGraph.leftWord (_root_.ThreeSum.BlockRows.row S j)) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceRows.hash_eq_eval (_root_.ThreeSum.BlockRows.row S j) (_root_.ThreeSum.BlockSourceRows.bits S j) _ _ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceRows.bits_fin S j),_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.eval_rawLeft]

theorem right_hash {h J : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) (j : Fin J)
    (w : _root_.ThreeSum.LocalHashMoments.Weight (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) :
    (_root_.ThreeSum.LightSourceRowScan.hash (_root_.ThreeSum.BlockSourceRows.bits S j) (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,true)).val)
      (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,false)).val) (464*h) : ℤ) =
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w (_root_.ThreeSum.LocalGraph.rightWord (_root_.ThreeSum.BlockRows.row S j)) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceRows.hash_eq_eval (_root_.ThreeSum.BlockRows.row S j) (_root_.ThreeSum.BlockSourceRows.bits S j) _ _ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceRows.bits_fin S j),_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.eval_rawRight]

end ThreeSum.BlockSourceRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete trimming flags equal the original independent endpoint conditions

The exact greedy occurrence-to-candidate bridge connects retained candidate
bucket tables to the unchanged `mapAt` schedule. A product of row flags is
therefore exactly the original `LeftAllowed` or `RightAllowed` condition.
-/

namespace ThreeSum.BlockSourceFlags
open _root_.ThreeSum.BlockSourceFlags


open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding

set_option maxHeartbeats 1200000



@[simp] theorem candidateIndices_fin (h : ℕ) (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.candidateIndices h s.val = _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s := rfl

theorem candidateIndices_lt {h s : ℕ} (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.candidateIndices h s < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt_lt h ⟨s,hs⟩







theorem mapRow_extend {h : ℕ} (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) (b : Bool) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h b s.val = _root_.ThreeSum.OneHotMask.extend (fun i => (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h s (i,b)).val) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow,s.isLt,dite_true]

theorem left_row_iff {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J)
    (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) (j : Fin J) :
    _root_.ThreeSum.LightSourceTrim.rowFlag (464*h) h (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.candidateIndices h) (_root_.ThreeSum.BlockSourceFlags.bits S)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.leftCount h) j.val = 1 ↔
        (_root_.ThreeSum.BlockRows.row S j).card=h ∧
        _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.leftVertices (464*h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (o j))
          (_root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (o j)) (_root_.ThreeSum.LocalGraph.leftWord (_root_.ThreeSum.BlockRows.row S j))) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h := by
  unfold _root_.ThreeSum.LightSourceTrim.rowFlag _root_.ThreeSum.LightSourceRowFlag.flag
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices_fin,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.candidateIndices_fin]
  change _root_.ThreeSum.LightSourceFlagTest.flag (_root_.ThreeSum.LightSourceRowScan.count (_root_.ThreeSum.BlockSourceRows.bits S j) (464*h)) h
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.leftCount h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h (o j))
      (_root_.ThreeSum.LightResidues.residue (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) 1
        (_root_.ThreeSum.LightSourceRowScan.hash (_root_.ThreeSum.BlockSourceRows.bits S j) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false (o j).val)
          (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true (o j).val) (464*h) : ℤ))) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) = 1 ↔ _
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.flag_eq_one,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceRows.count_eq_card]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.leftCount
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.leftCount_candidateAt h (o j)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) 1 _)]
  have he : ((_root_.ThreeSum.LightResidues.residue (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) 1
      (_root_.ThreeSum.LightSourceRowScan.hash (_root_.ThreeSum.BlockSourceRows.bits S j) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false (o j).val)
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true (o j).val) (464*h) : ℤ) : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) =
      _root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (o j)) (_root_.ThreeSum.LocalGraph.leftWord (_root_.ThreeSum.BlockRows.row S j)) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.residue_zmod (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h),one_mul,
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.mapRow_extend,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.mapRow_extend,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceRows.left_hash,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash_cast]
  rw [he]

theorem right_row_iff {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J)
    (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) (j : Fin J) :
    _root_.ThreeSum.LightSourceTrim.rowFlag (464*h) h (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.candidateIndices h) (_root_.ThreeSum.BlockSourceFlags.bits S)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.rightCount h) j.val = 1 ↔
        (_root_.ThreeSum.BlockRows.row S j).card=h ∧
        _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.rightVertices (464*h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (o j))
          (_root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (o j)) (_root_.ThreeSum.LocalGraph.rightWord (_root_.ThreeSum.BlockRows.row S j))) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h := by
  unfold _root_.ThreeSum.LightSourceTrim.rowFlag _root_.ThreeSum.LightSourceRowFlag.flag
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices_fin,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.candidateIndices_fin]
  change _root_.ThreeSum.LightSourceFlagTest.flag (_root_.ThreeSum.LightSourceRowScan.count (_root_.ThreeSum.BlockSourceRows.bits S j) (464*h)) h
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.rightCount h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h (o j))
      (_root_.ThreeSum.LightResidues.residue (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) 1
        (_root_.ThreeSum.LightSourceRowScan.hash (_root_.ThreeSum.BlockSourceRows.bits S j) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true (o j).val)
          (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false (o j).val) (464*h) : ℤ))) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) = 1 ↔ _
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.flag_eq_one,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceRows.count_eq_card]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.rightCount
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rightCount_candidateAt h (o j)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) 1 _)]
  have he : ((_root_.ThreeSum.LightResidues.residue (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) 1
      (_root_.ThreeSum.LightSourceRowScan.hash (_root_.ThreeSum.BlockSourceRows.bits S j) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true (o j).val)
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false (o j).val) (464*h) : ℤ) : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) =
      _root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (o j)) (_root_.ThreeSum.LocalGraph.rightWord (_root_.ThreeSum.BlockRows.row S j)) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.residue_zmod (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h),one_mul,
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.mapRow_extend,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.mapRow_extend,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceRows.right_hash,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash_cast]
  rw [he]

theorem left_product {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :
    _root_.ThreeSum.SourceFlagProduct.product
      (_root_.ThreeSum.LightSourceTrim.rowFlag (464*h) h (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h)
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.candidateIndices h) (_root_.ThreeSum.BlockSourceFlags.bits S)
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.leftCount h)) J =
      if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed o S then 1 else 0 := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct.product_eq_indicator
  · exact fun _ _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.rowFlag_le ..
  · constructor
    · intro hall j
      exact (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.left_row_iff o S j).mp (hall j.val j.isLt)
    · intro hall j hj
      exact (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.left_row_iff o S ⟨j,hj⟩).mpr (hall ⟨j,hj⟩)

theorem right_product {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :
    _root_.ThreeSum.SourceFlagProduct.product
      (_root_.ThreeSum.LightSourceTrim.rowFlag (464*h) h (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h)
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.candidateIndices h) (_root_.ThreeSum.BlockSourceFlags.bits S)
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.rightCount h)) J =
      if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o S then 1 else 0 := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct.product_eq_indicator
  · exact fun _ _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.rowFlag_le ..
  · constructor
    · intro hall j
      exact (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.right_row_iff o S j).mp (hall j.val j.isLt)
    · intro hall j hj
      exact (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.right_row_iff o S ⟨j,hj⟩).mpr (hall ⟨j,hj⟩)

end ThreeSum.BlockSourceFlags

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.BlockSourceFlags
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
set_option maxHeartbeats 1700000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation.meets__implementation_1076fe8788 {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.Procs P pMain)
    {μ : ℕ → ℤ} {h J occ maps candidates histL histR masks n coeff0 coeff1 rawLeft rawRight flags
      bitBase rowOut work : ℕ}
    (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (sets : ℕ → Finset (_root_.ThreeSum.BlockRows.Coord J (464*h)))
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(464*h)+5 ≤ lim.depth)
    (hocc : occ+J ≤ coeff0) (hmaps : maps+2*(464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ coeff0)
    (hcandidates : candidates+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ coeff0)
    (hleft : histL+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ coeff0)
    (hright : histR+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*(464*h) ≤ coeff1)
    (hc1 : coeff1+J*(464*h) ≤ rawLeft) (hrawLeft : rawLeft+n ≤ rawRight)
    (hrawRight : rawRight+n ≤ flags) (hflags : flags+2*n+2 ≤ bitBase)
    (hbits : bitBase+J*(464*h) ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : _root_.ThreeSum.LightSourcePreparation.space work J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourcePreparation.word J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
      ((464*h).choose h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) : ℤ) ≤ lim.word)
    (hoccRead : ∀ j < J, μ (occ+j) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o j : ℤ))
    (hcandidateRead : ∀ s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h,
      μ (candidates+s.val) = (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s : ℤ))
    (hread0 : ∀ s < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, ∀ a < 464*h,
      μ (maps+2*(464*h)*s+a) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false s a : ℤ))
    (hread1 : ∀ s < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, ∀ a < 464*h,
      μ (maps+2*(464*h)*s+464*h+a) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true s a : ℤ))
    (hcountL : ∀ k < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h, ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,
      μ (histL+k*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+r) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.leftCount h k r : ℤ))
    (hcountR : ∀ k < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h, ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,
      μ (histR+k*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+r) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.rightCount h k r : ℤ))
    (hmaskRead : ∀ i < n,
      μ (masks+i) = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (sets i)) : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [J,464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,occ,maps,candidates,histL,histR,masks,n,
        coeff0,coeff1,rawLeft,rawRight,flags,bitBase,rowOut,work]
      μ (_root_.ThreeSum.LightSourcePreparation.time n J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft o (sets i)) ∧
        (∀ i < n, ν (rawRight+i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o (sets i)) ∧
        (∀ i < n, ν (flags+i) = (if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed o (sets i) then 1 else 0 : ℕ)) ∧
        (∀ i < n, ν (flags+n+i) = (if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o (sets i) then 1 else 0 : ℕ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν coeff0) := by
  have hcandidates' : ∀ s < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, μ (candidates+s) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.candidateIndices h s : ℤ) := by
    intro s hs
    exact hcandidateRead ⟨s,hs⟩
  have hboundL : ∀ k < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h, ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.leftCount h k r ≤ (464*h).choose h := by
    intro k hk r hr
    exact _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_le _ _ _
  have hboundR : ∀ k < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h, ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.rightCount h k r ≤ (464*h).choose h := by
    intro k hk r hr
    exact _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_le _ _ _
  have run := C.meets (d := d) (μ := μ) (J := J) (L := 464*h) (h := h)
    (p := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (cap := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) (occ := occ) (maps := maps)
    (candidates := candidates) (histL := histL) (histR := histR) (masks := masks) (n := n)
    (coeff0 := coeff0) (coeff1 := coeff1) (rawLeft := rawLeft) (rawRight := rawRight)
    (flags := flags) (bitBase := bitBase) (rowOut := rowOut) (work := work)
    (U := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (V := (464*h).choose h) (M := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)
    (K := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h)
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.candidateIndices h) (fun i => _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (sets i)))
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.leftCount h) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.rightCount h)
    hw hd (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) (by omega) hocc hmaps hcandidates hleft hright hmasks hc0 hc1 hrawLeft
    hrawRight hflags hbits hrowOut hspace hword (fun _ hj => _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices_lt o hj)
    (fun _ hs => _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.candidateIndices_lt hs) hoccRead hcandidates' hread0 hread1
    (fun _ hs _ ha => _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow_le false hs ha) (fun _ hs _ ha => _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow_le true hs ha)
    hcountL hcountR hboundL hboundR hmaskRead
    (fun i _ => (_root_.ThreeSum.SubsetAddress.subsetMask_isMask (_root_.ThreeSum.BlockIndex.indexSet (sets i))).1)
  refine run.mono le_rfl ?_
  rintro r ν ⟨rawL,rawR,left,right,kept⟩
  exact ⟨fun i hi => (rawL i hi).trans (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.eval_left o (sets i)),
    fun i hi => (rawR i hi).trans (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.eval_right o (sets i)),
    fun i hi => (left i hi).trans (congrArg (fun n : ℕ => (n : ℤ)) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.left_product o (sets i))),
    fun i hi => (right i hi).trans (congrArg (fun n : ℕ => (n : ℤ)) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags.right_product o (sets i))),kept⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation.meets__implementation_1076fe8788) := (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation.meets__implementation_1076fe8788)

#print axioms solution
