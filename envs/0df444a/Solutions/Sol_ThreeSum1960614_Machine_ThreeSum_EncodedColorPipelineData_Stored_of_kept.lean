-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:50:35.117854+00:00
-- url     : https://prove2.me/submissions/943dcb67-46c3-40bb-9fd3-c4681d6efa51

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
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
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorPipelineData_ordered
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorPrimeData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCoverKeyData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandBankData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandPairData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceFiniteData_Normalized_keep

local instance platformRadixNonzero_c4dd8f60a7 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorPipelineData
end ThreeSum.EncodedColorPipelineData
namespace ThreeSum.EncodedColorWantedData
end ThreeSum.EncodedColorWantedData
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawAKeyLists
end ThreeSum.RawAKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceFiniteData
end ThreeSum.SourceFiniteData
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
end ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteData
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteData
namespace ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys
end ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp





variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}

























/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]









/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : _root_.ThreeSum1960614.Machine.Light.Seg μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)











































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.BlockSourceEncoding


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000









theorem modulus_pos (h J : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J := pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) J



section OriginalSources

variable {β : Type*} [DecidableEq β]





end OriginalSources

end ThreeSum.BlockSourceEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter
open _root_.ThreeSum.LightClassFilter


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000







theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (_root_.ThreeSum.LightClassFilter.items x color want scale n).length ≤ n := by
  simpa only [_root_.ThreeSum.LightClassFilter.items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightClassFilter

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original A positions and all three guarded lifts

The physical key order is lift-major, preserving every original position.
The selected-offset count is transported to the unchanged guarded wanted
labels used by raw reporting, including repeated input values.
-/

namespace ThreeSum.RawAKeyLists
open _root_.ThreeSum.RawAKeyLists


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open scoped _root_.BigOperators

set_option maxHeartbeats 900000















theorem keys_length (P : ℤ) (xs : List ℤ) : (_root_.ThreeSum.RawAKeyLists.keys P xs).length=3*xs.length := by
  rw [_root_.ThreeSum.RawAKeyLists.keys,List.length_map,_root_.ThreeSum.RawAKeyLists.records_length]

































end ThreeSum.RawAKeyLists

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

/-! ## Limits -/









/-! ## Specifications of single routines -/

/-- A list below fr stays where it is if nothing below fr changes. -/
theorem Seg.of_kept {μ μ' : ℕ → ℤ} {a fr : ℕ} {l : List ℤ} (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (hk : _root_.ThreeSum1960614.Machine.Light.Kept μ μ' fr)
    (hle : a + l.length ≤ fr) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  h.of_sameOn hk fun i hi => show a + i < fr by omega

/-! ## Tasks and solvers -/





















/-! ## Hosts -/





/-! ## Tasks with a list of parameters -/











end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists
open _root_.ThreeSum.ColorClassLists


open _root_.ThreeSum.LightClassFilter
open _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter













theorem length_classList_le {n W : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (_root_.ThreeSum.ColorClassLists.classList p x c scale).length ≤ n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.items_length_le ..













end ThreeSum.ColorClassLists

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData
open _root_.ThreeSum.SourceBandPairData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition






theorem work_ge (base n g m : ℕ) : base ≤ _root_.ThreeSum.SourceBandLayout.work base n g m := by
  unfold _root_.ThreeSum.SourceBandLayout.work _root_.ThreeSum.SourceBandLayout.hist _root_.ThreeSum.SourceBandLayout.data
  omega

theorem ordered (base NL NR g m : ℕ) :
    _root_.ThreeSum.SourceBandPairData.leftBase base ≤ _root_.ThreeSum.SourceBandPairData.rightBase base NL g m ∧
    _root_.ThreeSum.SourceBandPairData.rightBase base NL g m ≤ _root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m ∧
    _root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m < _root_.ThreeSum.SourceBandPairData.next base NL NR g m := by
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.work_ge _ _ _ _,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.work_ge _ _ _ _,by unfold _root_.ThreeSum.SourceBandPairData.next; omega⟩















end ThreeSum.SourceBandPairData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # One compact retained layout for a selected color -/

namespace ThreeSum.EncodedColorLayout
open _root_.ThreeSum.EncodedColorLayout





















theorem normalized_ends_before_count (free n g : ℕ) :
    _root_.ThreeSum.EncodedColorLayout.av free n+n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧ _root_.ThreeSum.EncodedColorLayout.ae free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.bv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧ _root_.ThreeSum.EncodedColorLayout.be free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.cv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧ _root_.ThreeSum.EncodedColorLayout.ce free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.tables free n+_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.rec free n g+4*_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g := by
  unfold _root_.ThreeSum.EncodedColorLayout.normalizedEnd _root_.ThreeSum.LightBandRawA.space _root_.ThreeSum.LightBandRawA.positionBase _root_.ThreeSum.LightBandRawA.ownerBase
    _root_.ThreeSum.LightBandRawA.capacity _root_.ThreeSum.EncodedColorLayout.vals _root_.ThreeSum.EncodedColorLayout.rec _root_.ThreeSum.EncodedColorLayout.tables _root_.ThreeSum.EncodedColorLayout.ce _root_.ThreeSum.EncodedColorLayout.cv _root_.ThreeSum.EncodedColorLayout.be _root_.ThreeSum.EncodedColorLayout.bv _root_.ThreeSum.EncodedColorLayout.ae _root_.ThreeSum.EncodedColorLayout.av
  omega







theorem prime_le_cover (free n g M y : ℕ) : _root_.ThreeSum.EncodedColorLayout.prime free n g+6 ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y := by
  unfold _root_.ThreeSum.EncodedColorLayout.cover _root_.ThreeSum.EncodedColorPrimeData.nextFree _root_.ThreeSum.EncodedColorPrimeData.prefixBase _root_.ThreeSum.EncodedColorPrimeData.poolBase
  omega

theorem normalized_ends_cover (free n g M y : ℕ) :
    _root_.ThreeSum.EncodedColorLayout.av free n+n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧ _root_.ThreeSum.EncodedColorLayout.ae free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.bv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧ _root_.ThreeSum.EncodedColorLayout.be free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.cv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧ _root_.ThreeSum.EncodedColorLayout.ce free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.tables free n+_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.rec free n g+4*_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.LightBandRawA.space (_root_.ThreeSum.EncodedColorLayout.vals free n g) (_root_.ThreeSum.ColorBandBounds.count n g) g ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.normalized_ends_before_count free n g
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.prime_le_cover free n g M y
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ≤ _
  unfold _root_.ThreeSum.EncodedColorLayout.prime at h
  omega

end ThreeSum.EncodedColorLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Keep the complete finite source catalog below its exact returned end -/

namespace ThreeSum.SourceFiniteData
open _root_.ThreeSum.SourceFiniteData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

theorem source_ends (base NL NR g h J cut : ℕ) :
    base+3 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR g h J cut ∧
    _root_.ThreeSum.SourceBandPairData.next (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) NL NR g
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR g h J cut ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) NL NR g h J+5 ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR g h J cut := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.ordered (_root_.ThreeSum.LightSourceControlsHost.sourceBase base)
    NL NR g (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.finish _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt _root_.ThreeSum.SourceBandBankData.first _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.occurrenceBase _root_.ThreeSum.LightSourceControlsHost.sourceBase
  unfold _root_.ThreeSum.SourceBandPairData.leftBase _root_.ThreeSum.LightSourceControlsHost.sourceBase at ho
  omega

theorem Stored.of_kept {μ ν : ℕ → ℤ} {base g p h J cut bound : ℕ} {B C : List ℤ} {shift r : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Stored μ base g p h J cut B C shift r)
    (K : _root_.ThreeSum1960614.Machine.Light.Kept μ ν bound)
    (hb : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base B.length C.length g h J cut ≤ bound) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Stored ν base g p h J cut B C shift r := by
  obtain ⟨hcontrol,hpair,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.source_ends base B.length C.length g h J cut
  refine ⟨H.returned,?_,?_,?_⟩
  · exact H.controls.of_kept K (by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.values] using hcontrol.trans hb)
  · exact H.buckets.of_kept (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_pos h J) K (hpair.trans hb)
  · exact H.banks.of_kept K le_rfl hb

end ThreeSum.SourceFiniteData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact reusable memory boundary after the actual wanted-pair output -/

namespace ThreeSum.EncodedColorWantedData
open _root_.ThreeSum.EncodedColorWantedData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WantedResidueKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys



theorem header_le_nextFree (out M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) :
    out+4 ≤ _root_.ThreeSum.EncodedColorWantedData.nextFree out M left right NL NR shift := by
  unfold _root_.ThreeSum.EncodedColorWantedData.nextFree _root_.ThreeSum.LightWantedSetup.pairBase _root_.ThreeSum.LightSourceBucketSetup.next _root_.ThreeSum.LightWantedSetup.bucketBase
    _root_.ThreeSum.LightWantedSetup.rightCodes _root_.ThreeSum.LightWantedSetup.leftCodes
  omega



theorem of_kept {μ ν : ℕ → ℤ} {out M NL NR bound : ℕ} {left right : ℕ → ℤ} {shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ out M left right NL NR shift)
    (K : _root_.ThreeSum1960614.Machine.Light.Kept μ ν bound) (hb : _root_.ThreeSum.EncodedColorWantedData.nextFree out M left right NL NR shift ≤ bound) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output ν out M left right NL NR shift := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData.header_le_nextFree out M left right NL NR shift).trans hb
  obtain ⟨hcount,hpair,hnext,hshift,ps,hlen,hnodup,hmem,hrows⟩ := H
  refine ⟨(K _ (by omega)).trans hcount,(K _ (by omega)).trans hpair,
    (K _ (by omega)).trans hnext,(K _ (by omega)).trans hshift,ps,hlen,hnodup,hmem,?_⟩
  apply hrows.of_kept K
  rw [_root_.ThreeSum.WantedPairs.cells_length,hlen]
  exact hb

end ThreeSum.EncodedColorWantedData

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
section


theorem ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored.of_kept__implementation_dd76380c8c {μ ν : ℕ → ℤ} {free n stop : ℕ} {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)}
    {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) (K : _root_.ThreeSum1960614.Machine.Light.Kept μ ν stop)
    (hstop : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC+8 ≤ stop) :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC := by
  obtain ⟨hprime,hfree,hcover,hwanted,hcontrol,hbank⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  have hcoverStop : _root_.ThreeSum.EncodedColorLayout.cover free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n) ≤ stop := by
    change _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n ≤ stop
    omega
  obtain ⟨hav,hae,hbv,hbe,hcv,hce,htables,hrecords,hcatalog⟩ :=
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.normalized_ends_cover free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n)
  have hkey : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ stop := by
    have hh : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length=
        _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))+
          3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length := rfl
    omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact H.heads.of_kept K (by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using hstop)
  · exact H.normalizedHeads.of_kept K (by
      simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using (show free+8 ≤ stop by omega))
  · rw [K _ (by unfold _root_.ThreeSum.EncodedColorLayout.prime at hprime; omega)]
    exact H.countCell
  · exact H.normalized.keep K (_root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 0 1) (_root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 1 1)
      (_root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 2 (-1)) (hav.trans hcoverStop) (hae.trans hcoverStop)
      (hbv.trans hcoverStop) (hbe.trans hcoverStop) (hcv.trans hcoverStop) (hce.trans hcoverStop)
      (htables.trans hcoverStop) (hrecords.trans hcoverStop) (hcatalog.trans hcoverStop)
  · exact H.primes.of_kept K (by change _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n ≤ stop; omega)
  · exact H.cover.of_kept (fun i hi => K i (hi.trans_le hkey))
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData.of_kept H.wanted K (by change _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC ≤ stop; omega)
  · exact H.sources.of_kept K (by change _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC ≤ stop; omega)
  · rw [K _ (by omega)]
    exact H.countBound
  · apply H.lifts.of_kept K
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.keys_length]
    change _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length ≤ stop
    omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored.of_kept__implementation_dd76380c8c) := (@ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored.of_kept__implementation_dd76380c8c)

#print axioms solution
