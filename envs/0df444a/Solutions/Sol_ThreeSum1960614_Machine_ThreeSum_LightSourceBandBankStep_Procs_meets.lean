-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:36:18.355139+00:00
-- url     : https://prove2.me/submissions/b27a8218-ee5f-483c-b0dc-a99552741552

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
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
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
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BlockSourceCoverInput_Input_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockSourceBatch_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceBandHistSelect_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandPairData_Stored_of_kept

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockSourceCatalogCosts
end ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceBandBankStep
end ThreeSum.LightSourceBandBankStep
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LightZetaStages
end ThreeSum.LightZetaStages
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SourceBandData
end ThreeSum.SourceBandData
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceBandPairSlices
end ThreeSum.SourceBandPairSlices
namespace ThreeSum.SourceBandPartition
end ThreeSum.SourceBandPartition
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaStages
end ThreeSum1960614.Machine.ThreeSum.LightZetaStages
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandData
end ThreeSum1960614.Machine.ThreeSum.SourceBandData
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPartition
end ThreeSum1960614.Machine.ThreeSum.SourceBandPartition
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

namespace ThreeSum1960614.Machine

/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition
open _root_.ThreeSum.BandPartition






theorem size_le (n g : ℕ) : _root_.ThreeSum.BandPartition.size n g ≤ n := by
  unfold _root_.ThreeSum.BandPartition.size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega













theorem length_le (n g i : ℕ) : _root_.ThreeSum.BandPartition.stop n g i-_root_.ThreeSum.BandPartition.start g i ≤ g := by
  have hle : _root_.ThreeSum.BandPartition.stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold _root_.ThreeSum.BandPartition.start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega











end ThreeSum.BandPartition

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

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : _root_.ThreeSum1960614.Machine.Light.Stmt}
    (hp : P[p]? = some body)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨_root_.Light.frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩









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

/-!
# Packed retained source banks indexed by occurrence vectors

Each bank retains its compact masks, coefficients, endpoints, flags, and
both complete source-stage families. Shared temporary transform workspace
follows all banks. Two header cells per occurrence contain the stage bases.
This layout lets the next actual source call preserve every earlier bank.
-/

namespace ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum.LightBlockSourceBatchLayout


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaStages
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages

















theorem banks_le_slot (base count W cut i : ℕ) : _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut i :=
  Nat.le_add_right _ _













theorem banks_le_work (base count W cut : ℕ) : _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_slot base count W cut count
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase
  omega





theorem masks_le_work (base count W cut : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base count W cut ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase
  omega

















end ThreeSum.LightBlockSourceBatchLayout

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



@[simp] theorem count_zero (key : ℕ → ℕ) (r : ℕ) : _root_.ThreeSum.LightHistogram.count key r 0 = 0 := by
  simp [_root_.ThreeSum.LightHistogram.count]

















end ThreeSum.LightHistogram

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

@[simp] theorem modulus_cast (h J : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]





end OriginalSources

end ThreeSum.BlockSourceEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Packed original-band histograms and exact physical residue fibers -/

namespace ThreeSum.SourceBandLayout
open _root_.ThreeSum.SourceBandLayout


open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets












theorem len_le_cap (n g i : ℕ) : _root_.ThreeSum.SourceBandLayout.len n g i ≤ _root_.ThreeSum.SourceBandLayout.cap n g := by
  have hn := _root_.ThreeSum.BandPartition.stop_le n g i
  have hg := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.length_le n g i
  unfold _root_.ThreeSum.SourceBandLayout.len _root_.ThreeSum.SourceBandLayout.cap
  exact le_min (by omega) hg







theorem hist_mono (base n g m : ℕ) : Monotone (_root_.ThreeSum.SourceBandLayout.hist base n g m) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _



theorem flat_end (base n g m i : ℕ) :
    _root_.ThreeSum.SourceBandLayout.flat base n g m i+_root_.ThreeSum.SourceBandLayout.cap n g = _root_.ThreeSum.SourceBandLayout.hist base n g m (i+1) := by
  unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes _root_.ThreeSum.SourceBandLayout.hist _root_.ThreeSum.SourceBandLayout.stride
  ring



theorem flat_end_le_work {base n g m i : ℕ} (hi : i < _root_.ThreeSum.BandPartition.size n g) :
    _root_.ThreeSum.SourceBandLayout.flat base n g m i+_root_.ThreeSum.SourceBandLayout.cap n g ≤ _root_.ThreeSum.SourceBandLayout.work base n g m := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.flat_end]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.hist_mono base n g m (by omega)

















end ThreeSum.SourceBandLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact shared-bank dimensions and charge of the actual catalog

There are two stage families for each original band and occurrence vector.
The decoder and bank-loop overhead are included. Neither the number of
complete output subsets nor the three-valued query lift multiplies this
construction.
-/

namespace ThreeSum.BlockSourceCatalogCosts
open _root_.ThreeSum.BlockSourceCatalogCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout



theorem work_address (base count W cut : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut =
      base+count*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride W cut+2)+_root_.ThreeSum.SubsetAddress.downsetCap W cut+W+2 := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase _root_.ThreeSum.LightBlockSourceBatchLayout.slot _root_.ThreeSum.LightBlockSourceBatchLayout.banks
  ring





















end ThreeSum.BlockSourceCatalogCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained original-band headers, histograms, and physical position fibers -/

namespace ThreeSum.SourceBandData
open _root_.ThreeSum.SourceBandData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout









theorem At.histogram_for_host {μ : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i : ℕ} {shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandData.At μ f base n g p m shift i) (r : ℕ) (hr : r < m) :
    μ (_root_.ThreeSum.SourceBandLayout.hist base n g m i+r) =
      (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p m shift (fun j => f (_root_.ThreeSum.BandPartition.start g i+j)) (_root_.ThreeSum.SourceBandLayout.len n g i) r : ℤ) :=
  H.histRead r hr







end ThreeSum.SourceBandData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact finite original-position sources for real and padded bands -/

namespace ThreeSum.SourceBandPartition
open _root_.ThreeSum.SourceBandPartition


open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout













theorem len_eq_zero {n g i : ℕ} (hg : 0 < g) (hi : _root_.ThreeSum.BandPartition.size n g ≤ i) : _root_.ThreeSum.SourceBandLayout.len n g i=0 := by
  by_cases hn : n=0
  · simp [_root_.ThreeSum.SourceBandLayout.len,_root_.ThreeSum.BandPartition.stop,hn]
  · have hdiv : (n-1)/g < i := by
      simpa only [_root_.ThreeSum.BandPartition.size,if_neg hn,Nat.add_one_le_iff] using hi
    have hmul : n-1 < i*g := (Nat.div_lt_iff_lt_mul hg).mp hdiv
    have hs := _root_.ThreeSum.BandPartition.stop_le n g i
    unfold _root_.ThreeSum.SourceBandLayout.len _root_.ThreeSum.BandPartition.start
    omega







end ThreeSum.SourceBandPartition

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













theorem Data.empty_histogram {μ : ℕ → ℤ} {fL fR v : ℕ → ℤ}
    {base NL NR g p m : ℕ} {shift d : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Data μ fL fR base NL NR g p m shift) (r : ℕ) (hr : r < m) :
    μ (_root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m+r)=
      (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p m d v 0 r : ℤ) := by
  simpa only [_root_.ThreeSum.LightBlockSourceRetainedStages.histogram,_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_zero,Nat.cast_zero]
    using H.zero r hr.le

end ThreeSum.SourceBandPairData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Padded histogram selection for independently chosen original bands -/

namespace ThreeSum.SourceBandPairSlices
open _root_.ThreeSum.SourceBandPairSlices


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
open _root_.ThreeSum.SourceBandPairData
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData









theorem histogram_end {base n g m zero i bound : ℕ}
    (hb : _root_.ThreeSum.SourceBandLayout.work base n g m ≤ bound) (hz : zero+m ≤ bound) :
    _root_.ThreeSum.SourceBandPairSlices.histogramPtr base n g m zero i+m ≤ bound := by
  unfold _root_.ThreeSum.SourceBandPairSlices.histogramPtr
  split_ifs with hi
  · have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.flat_end_le_work (base := base) (m := m) hi
    unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes at hh
    omega
  · exact hz

theorem left_end (base NL NR g m i : ℕ) :
    _root_.ThreeSum.SourceBandPairSlices.histLeft base NL NR g m i+m ≤ _root_.ThreeSum.SourceBandPairData.next base NL NR g m := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.ordered base NL NR g m
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.histogram_end (by change _root_.ThreeSum.SourceBandPairData.rightBase base NL g m ≤ _root_.ThreeSum.SourceBandPairData.next base NL NR g m; omega)
    (by unfold _root_.ThreeSum.SourceBandPairData.next; omega)

theorem right_end (base NL NR g m i : ℕ) :
    _root_.ThreeSum.SourceBandPairSlices.histRight base NL NR g m i+m ≤ _root_.ThreeSum.SourceBandPairData.next base NL NR g m := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.histogram_end (by change _root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m ≤ _root_.ThreeSum.SourceBandPairData.next base NL NR g m; unfold _root_.ThreeSum.SourceBandPairData.next; omega)
    (by unfold _root_.ThreeSum.SourceBandPairData.next; omega)

theorem left_histogram {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m i : ℕ} {shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Data μ fL fR base NL NR g p m shift) (hg : 0 < g) (r : ℕ) (hr : r < m) :
    μ (_root_.ThreeSum.SourceBandPairSlices.histLeft base NL NR g m i+r)=
      (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p m 0
        (fun j => fL (_root_.ThreeSum.BandPartition.start g i+j)) (_root_.ThreeSum.SourceBandLayout.len NL g i) r : ℤ) := by
  by_cases hi : i < _root_.ThreeSum.BandPartition.size NL g
  · simpa only [_root_.ThreeSum.SourceBandPairSlices.histLeft,_root_.ThreeSum.SourceBandPairSlices.histogramPtr,if_pos hi] using (H.left i hi).histogram_for_host r hr
  · rw [_root_.ThreeSum.SourceBandPairSlices.histLeft,_root_.ThreeSum.SourceBandPairSlices.histogramPtr,if_neg hi,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPartition.len_eq_zero hg (by omega)]
    exact H.empty_histogram r hr

theorem right_histogram {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m i : ℕ} {shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Data μ fL fR base NL NR g p m shift) (hg : 0 < g) (r : ℕ) (hr : r < m) :
    μ (_root_.ThreeSum.SourceBandPairSlices.histRight base NL NR g m i+r)=
      (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p m shift
        (fun j => fR (_root_.ThreeSum.BandPartition.start g i+j)) (_root_.ThreeSum.SourceBandLayout.len NR g i) r : ℤ) := by
  by_cases hi : i < _root_.ThreeSum.BandPartition.size NR g
  · simpa only [_root_.ThreeSum.SourceBandPairSlices.histRight,_root_.ThreeSum.SourceBandPairSlices.histogramPtr,if_pos hi] using (H.right i hi).histogram_for_host r hr
  · rw [_root_.ThreeSum.SourceBandPairSlices.histRight,_root_.ThreeSum.SourceBandPairSlices.histogramPtr,if_neg hi,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPartition.len_eq_zero hg (by omega)]
    exact H.empty_histogram r hr



end ThreeSum.SourceBandPairSlices

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Complete source banks per common band with preserved earlier banks -/

namespace ThreeSum.SourceBandBankLayout
open _root_.ThreeSum.SourceBandBankLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder















theorem word_mono {NL NR NL' NR' h J : ℕ} (hl : NL ≤ NL') (hr : NR ≤ NR') :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.word NL NR h J ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.word NL' NR' h J := by
  have hpl := Nat.mul_le_mul_left (2^(J*(464*h))) hl
  have hpr := Nat.mul_le_mul_left (2^(J*(464*h))) hr
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.word _root_.ThreeSum.LightSourceRetainedStages.word
  omega









end ThreeSum.SourceBandBankLayout

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.Procs.meets__implementation_5521f19ecf {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.Procs P pMain)
    {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p h J cut occ maps candidates histL histR base i : ℕ}
    {shift : ℤ} (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fL fR pair NL NR g p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(464*h)+12 ≤ lim.depth)
    (hg : 0 < g) (hi : i < _root_.ThreeSum.SourceBandPairSlices.count NL NR g) (hcut : cut ≤ J*(464*h))
    (hpair : _root_.ThreeSum.SourceBandPairData.next pair NL NR g (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) ≤ base)
    (hocc : occ+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J*J ≤ base)
    (hmaps : maps+2*(464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ base)
    (hcandidates : candidates+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ base)
    (hleft : histL+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ base)
    (hright : histR+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ base)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space
      (_root_.ThreeSum.LightBlockSourceBatchLayout.work base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut) h J ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.word NL NR h J : ℤ) ≤ lim.word)
    (hoccRead : ∀ k < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J, ∀ j < J,
      μ (occ+k*J+j)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J k)) j : ℤ))
    (hcover : _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [J,464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,cut,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,occ,maps,candidates,histL,histR,
        pair,base,_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J,i]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.time h J cut) (fun _ ν =>
        _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.Stored ν h J base cut (p : ℤ) shift
          (_root_.ThreeSum.SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
          (_root_.ThreeSum.SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν base) := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_pos h J
  have hc : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J := pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.schedule_pos h) J
  have hs : _root_.ThreeSum.LightBlockSourceBatchLayout.work base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut+(J*(464*h)+1) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hwork : _root_.ThreeSum.LightBlockSourceBatchLayout.work base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut ≤ lim.space := by omega
  have hbanks := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_work base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut
  have hbanksAddr : (base : ℤ)+2*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J : ℤ) ≤ lim.word :=
    (by exact_mod_cast hbanks.trans hwork :
      (base : ℤ)+2*(LightBlockSourceCatalog.count h J : ℤ) ≤ lim.space).trans hw
  have hbase2 : base+2 ≤ lim.space := by unfold _root_.ThreeSum.LightBlockSourceBatchLayout.banks at hbanks; omega
  have hNL := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le NL g
  have hNR := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le NR g
  have hiN : i ≤ NL+NR := by unfold _root_.ThreeSum.SourceBandPairSlices.count at hi; omega
  have hselWord : ((NL+NR+i+6 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.word; omega)).trans hword
  have hsWord : (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.word NL NR h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.word; omega)).trans hword
  have h32 : (32 : ℤ) ≤ lim.word := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.word at hword; omega
  have hwidth : (J : ℤ)*(464*(h : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show J*(464*h) ≤ lim.space by omega) :
      (J : ℤ)*(464*(h : ℤ)) ≤ lim.space).trans hw
  have hwidthNonneg : (0 : ℤ) ≤ (J : ℤ)*(464*(h : ℤ)) := by positivity
  have hwidthPlus : (J*(464*h) : ℤ)+1 ≤ lim.word := by
    exact (by exact_mod_cast (show J*(464*h)+1 ≤ lim.space by omega) :
      (J*(464*h) : ℤ)+1 ≤ lim.space).trans hw
  have hstrideN : _root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut ≤ lim.space := by
    have hp := Nat.le_mul_of_pos_left (_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut) hc
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.work_address] at hwork
    nlinarith
  have hstrideExpr : 5*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+2*(J*(464*h))+2+
      2*(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ lim.space := by
    simpa only [_root_.ThreeSum.LightBlockSourceBatchLayout.stride,_root_.ThreeSum.LightBlockSourceBatchLayout.family,Nat.mul_assoc] using hstrideN
  have hstrideZ : (5 : ℤ)*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut : ℤ)+2*(J*(464*h) : ℤ)+2+
      2*((J*(464*h) : ℤ)+1)*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hstrideExpr :
      (5 : ℤ)*(downsetCap (J*(464*h)) cut : ℤ)+2*(J*(464*h) : ℤ)+2+
        2*((J*(464*h) : ℤ)+1)*(downsetCap (J*(464*h)) cut : ℤ) ≤ lim.space).trans hw
  have hcapNonneg : (0 : ℤ) ≤ (_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut : ℤ) := Int.natCast_nonneg _
  have hfamNonneg : (0 : ℤ) ≤ 2*((J*(464*h) : ℤ)+1)*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut : ℤ) := by positivity
  have hfamilyNonneg : (0 : ℤ) ≤ ((J*(464*h) : ℤ)+1)*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut : ℤ) := by positivity
  have hstrideAssoc : (5 : ℤ)*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut : ℤ)+2*(J*(464*h) : ℤ)+2+
      2*(((J*(464*h) : ℤ)+1)*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut : ℤ)) ≤ lim.word := by
    simpa only [mul_assoc] using hstrideZ
  have hmask := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.masks_le_work base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut
  have hmaskAddr : (_root_.ThreeSum.LightBlockSourceBatchLayout.banks base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) : ℤ)+
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J : ℤ)*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hmask.trans hwork :
      (banks base (LightBlockSourceCatalog.count h J) : ℤ)+
        (LightBlockSourceCatalog.count h J : ℤ)*(stride (J*(464*h)) cut : ℤ) ≤ lim.space).trans hw
  have hmaskProdNonneg : (0 : ℤ) ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J : ℤ)*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut : ℤ) := by positivity
  have hbits : _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut+
      _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ lim.space := by unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase at hwork; omega
  have hrow : _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut+J*(464*h) ≤ lim.space := by
    unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut at hwork
    omega
  have hrowZ : (_root_.ThreeSum.LightBlockSourceBatchLayout.bitBase base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut : ℤ)+
      (J*(464*h) : ℤ) ≤ lim.word := (by exact_mod_cast hrow :
        (bitBase base (LightBlockSourceCatalog.count h J) (J*(464*h)) cut : ℤ)+(J*(464*h) : ℤ) ≤ lim.space).trans hw
  have hworkN : _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut+2 ≤ lim.space := hwork
  have hsrcL := (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.left_end pair NL NR g (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) i).trans hpair
  have hsrcR := (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.right_end pair NL NR g (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) i).trans hpair
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.body _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.meets (d := d + 1) C.select H hw hm hpair hbase2 hselWord) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.meets (d := d + 1) C.select H hw hm hpair hbase2 hselWord) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     on_goal -1 => (rintro unused ν ⟨headL, headR, kept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (J * (464 * h) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J * (464 * h)) cut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.stride, _root_.ThreeSum.LightBlockSourceBatchLayout.family, mul_assoc]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.stride, _root_.ThreeSum.LightBlockSourceBatchLayout.family, mul_assoc] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.stride, _root_.ThreeSum.LightBlockSourceBatchLayout.family, mul_assoc] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.banks base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.banks]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.banks] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.banks] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J * (464 * h)) cut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase, _root_.ThreeSum.LightBlockSourceBatchLayout.slot]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.maskBase, _root_.ThreeSum.LightBlockSourceBatchLayout.slot] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase, _root_.ThreeSum.LightBlockSourceBatchLayout.slot] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.bitBase base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J * (464 * h)) cut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.bitBase] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.rowOut base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J * (464 * h)) cut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.rowOut] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.work base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J * (464 * h)) cut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.work]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.work] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.work] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have H' := H.of_kept hm kept hpair
  have hcover' := hcover.of_kept kept hmaps hcandidates hleft hright
  have hrows : ∀ k < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J, ∀ j < J,
      ν (occ+k*J+j)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J k)) j : ℤ) := by
    intro k hk j hj
    have hp := Nat.mul_le_mul_right J (show k+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J by omega)
    exact (kept _ (by nlinarith)).trans (hoccRead k hk j hj)
  have hlenL := (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.len_le_cap NL g i).trans (min_le_left _ _)
  have hlenR := (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.len_le_cap NR g i).trans (min_le_left _ _)
  have hword' := (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.word_mono (h := h) (J := J) hlenL hlenR)).trans hsWord
  have hrun := C.batch.meets (d := d+1) (μ := ν) (cut := cut) (p := p) (shift := shift)
    (occ := occ) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
    (sourceHistL := _root_.ThreeSum.SourceBandPairSlices.histLeft pair NL NR g (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) i)
    (sourceHistR := _root_.ThreeSum.SourceBandPairSlices.histRight pair NL NR g (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) i)
    (base := base) (count := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J)
    (_root_.ThreeSum.SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
    (_root_.ThreeSum.SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J)
    (fun j => fL (_root_.ThreeSum.BandPartition.start g i+j)) (fun j => fR (_root_.ThreeSum.BandPartition.start g i+j))
    (_root_.ThreeSum.SourceBandPartition.equiv NL g i) (_root_.ThreeSum.SourceBandPartition.equiv NR g i)
    hw (by omega) hcut hocc hmaps hcandidates hleft hright hsrcL hsrcR hspace hword'
    (fun _ => rfl) (fun _ => rfl)
    (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.left_histogram H'.toData hg)
    (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.right_histogram H'.toData hg) hrows hcover'
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hrun ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, headL, headR]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [headL, headR] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, headL, headR] <;> omega)
     on_goal -1 => (rintro result ν' ⟨stored, kept'⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  exact ⟨stored,fun a ha => (kept' a ha).trans (kept a ha)⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.Procs.meets__implementation_5521f19ecf) := (@ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.Procs.meets__implementation_5521f19ecf)

#print axioms solution
