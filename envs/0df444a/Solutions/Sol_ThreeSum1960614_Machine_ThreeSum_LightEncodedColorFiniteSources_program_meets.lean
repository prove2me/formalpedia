-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:52:22.55589+00:00
-- url     : https://prove2.me/submissions/57234e01-d07f-4681-b83d-81700054f3aa

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightEncodedColorSources_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandBanksCosts_time_le_encoderCount
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandCosts_time_le_encoderCount
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceControlCosts_space_le_encoderCount
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceFiniteData_Normalized_keep
import Theorems.Thm_ThreeSum_LocalCoverBounds_pow_le_choose_mul

namespace Filter
end Filter
namespace Light
end Light
namespace Real
end Real
namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceCatalogCosts
end ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorCoverData
end ThreeSum.EncodedColorCoverData
namespace ThreeSum.EncodedColorSourcesCosts
end ThreeSum.EncodedColorSourcesCosts
namespace ThreeSum.EncodedColorWantedData
end ThreeSum.EncodedColorWantedData
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightCoverKeyData
end ThreeSum.LightCoverKeyData
namespace ThreeSum.LightDownsetSize
end ThreeSum.LightDownsetSize
namespace ThreeSum.LightEncodedColorFiniteSources
end ThreeSum.LightEncodedColorFiniteSources
namespace ThreeSum.LightLocalCoverRetention
end ThreeSum.LightLocalCoverRetention
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetSetup
end ThreeSum.LightSubsetSetup
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SourceBandCosts
end ThreeSum.SourceBandCosts
namespace ThreeSum.SourceBandHostCosts
end ThreeSum.SourceBandHostCosts
namespace ThreeSum.SourceBandPairCosts
end ThreeSum.SourceBandPairCosts
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceControlCosts
end ThreeSum.SourceControlCosts
namespace ThreeSum.SourceFiniteCosts
end ThreeSum.SourceFiniteCosts
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorCoverData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorCoverData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
end ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
namespace ThreeSum1960614.Machine.ThreeSum.LightDownsetSize
end ThreeSum1960614.Machine.ThreeSum.LightDownsetSize
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup
end ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandHostCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandHostCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
namespace ThreeSum1960614.Machine.ThreeSum.SourceControlCosts
end ThreeSum1960614.Machine.ThreeSum.SourceControlCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys
end ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys

namespace ThreeSum1960614.Machine

/-!
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalCoverBounds


open scoped _root_.BigOperators








theorem concrete_output_gt_pow {h : ℕ} (hh : 0 < h) :
    2 ^ (2 * h) < _root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h := by
  have hlo : 232 ^ (2 * h) ≤ _root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h := by
    simpa [_root_.ThreeSum.LocalCoverBounds.outputCount, show 232 * (2 * h) = 464 * h by omega] using
      _root_.ThreeSum.LocalCoverBounds.pow_le_choose_mul 232 (2 * h)
  exact ((Nat.pow_lt_pow_iff_left (by omega : 2 * h ≠ 0)).mpr (by decide)).trans_le hlo

























/-! ## A deterministic selected prime -/































/-! ## Exact integer rounding of the separable bucket cap -/













/-! ## The actual local parameters at `L=464*h` -/



































end ThreeSum.LocalCoverBounds

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

/-!
# A rectangular Pascal table in the benchmark language

Every coefficient is built once by addition from the preceding row.
The row-major representation supports one multiplication and two additions
per later lookup. No recursive binomial-coefficient evaluation is used.
-/

namespace ThreeSum.LightPascal
open _root_.ThreeSum.LightPascal


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



















theorem buildTime_bound (L : ℕ) : _root_.ThreeSum.LightPascal.buildTime L ≤ 1000*(L+1)^2 := by
  unfold _root_.ThreeSum.LightPascal.buildTime _root_.ThreeSum.LightPascal.rowTime _root_.ThreeSum.LightArray.linearTime
  simp only [_root_.Light.fillTime]
  nlinarith

end ThreeSum.LightPascal

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual vertex and trimmed-bucket scales

The local prime and bucket cap are the computable finite selections from
`LocalCoverBounds`.  Their logarithmic rates are derived from those exact
definitions and the exact integer schedule in `Scales`.
-/

namespace ThreeSum.TrimScales
open _root_.ThreeSum.TrimScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology

















noncomputable section





























theorem localLength_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength h := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength, _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule_length]
  positivity



























end

end ThreeSum.TrimScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The executable band size and its exact exponent

The band numerator is the integer ceiling of the square root of the actual
typed output count. The denominator is `2^floor(-bandShift*mu)`.
Euclidean division computes the rational exponent with bounded error.
-/

namespace ThreeSum.BandScales
open _root_.ThreeSum.BandScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology










theorem typedOutputs_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs
  exact Nat.pow_pos (Nat.choose_pos (by omega))









noncomputable section























end

end ThreeSum.BandScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete subset-rank program, including table construction

This fixed program constructs both lookup tables in scratch and then ranks
one valid mask. Its cost is quadratic in the bit width. The faster cached
rank contract remains available separately, but no supplied table correctness
assumption appears in the fixed-program result below.
-/

namespace ThreeSum.LightSubsetSetup
open _root_.ThreeSum.LightSubsetSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}















theorem time_bound (L : ℕ) : _root_.ThreeSum.LightSubsetSetup.time L ≤ 1200*(L+1)^2 := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.buildTime_bound L
  unfold _root_.ThreeSum.LightSubsetSetup.time _root_.Light.powTableTime _root_.ThreeSum.LightSubsetAddress.rankTime
  nlinarith

end ThreeSum.LightSubsetSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger
open _root_.ThreeSum.CostLedger


open _root_.Filter
open _root_.Set
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open scoped _root_.Topology
open scoped _root_.BigOperators

set_option maxHeartbeats 400000



















theorem bandCount_mul_bounds (n : ℕ) :
    n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n < n + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (b := n)
      (c := _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (n + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n - 1) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)]
    have hpos := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n
    omega











noncomputable section















end
end ThreeSum.CostLedger

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Computing the compact downset size

The program builds a Pascal table, scans all preceding layers, and adds
the final binomial coefficient. The table stride used by the transform
is therefore computed by an actual fixed program.
-/

namespace ThreeSum.LightDownsetSize
open _root_.ThreeSum.LightDownsetSize


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}















theorem time_bound (L : ℕ) : _root_.ThreeSum.LightDownsetSize.time L ≤ 1400*(L+1)^2 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold _root_.ThreeSum.LightDownsetSize.time _root_.ThreeSum.LightSubsetOffset.time
  nlinarith

end ThreeSum.LightDownsetSize

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention
open _root_.ThreeSum.LightLocalCoverRetention


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata

set_option maxHeartbeats 1000000

theorem base_le_nextFree (base h : ℕ) : base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr
    _root_.ThreeSum.LightCoverGreedy.total
  omega













end ThreeSum.LightLocalCoverRetention

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact sharing of source transforms and the encoder ledger

Source stages are indexed by a source band and an occurrence vector. The
output subset and the three-valued A lift do not enter the source function.
Compact table and zeta charges below match the existing `encoderCount`
without introducing a factor for all complete global outputs.
-/

namespace ThreeSum.BlockSourceSharing
open _root_.ThreeSum.BlockSourceSharing


open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds









theorem occurrence_card (h J : ℕ) : Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h^J := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence,Fintype.card_fun,Fintype.card_fin]

theorem occurrence_card_eq_scheduleCount (n : ℕ) :
    Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) = _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.occurrence_card,_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount,_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf,_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize_eq_length]

theorem width_eq (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) = 232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize _root_.ThreeSum.Scales.microSize _root_.ThreeSum.Scales.microHalf
  ring

theorem cutoff_eq (n : ℕ) :
    2*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize _root_.ThreeSum.Scales.microSize _root_.ThreeSum.Scales.microHalf
  ring

















end ThreeSum.BlockSourceSharing

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData
open _root_.ThreeSum.LightCoverKeyData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000





theorem layer_end_le_header (free h J : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h+_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.keyHeader free h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.keyHeader _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch
  omega

theorem afterCover_le_keyEnd (free h J : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd free h J := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.layer_end_le_header free h J
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd
  omega











end ThreeSum.LightCoverKeyData

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

theorem count_eq_scheduleCount (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) =
      _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.occurrence_card,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.occurrence_card_eq_scheduleCount]























end ThreeSum.BlockSourceCatalogCosts

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

namespace ThreeSum1960614.Machine

/-! # Finite charge of the actual original-band histogram and bucket catalog -/

namespace ThreeSum.SourceBandCosts
open _root_.ThreeSum.SourceBandCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

theorem choose_mul_le (L K N M : ℕ) : L.choose K*N.choose M ≤ (L+N).choose (K+M) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ×ℕ => L.choose ij.1*N.choose ij.2)
    (fun _ _ => Nat.zero_le _) (by simp : (K,M) ∈ Finset.HasAntidiagonal.antidiagonal (K+M))

theorem choose_pow_le (L K J : ℕ) : (L.choose K)^J ≤ (J*L).choose (J*K) := by
  induction J with
  | zero => simp
  | succ J ih =>
    calc
      _ = (L.choose K)^J*L.choose K := pow_succ _ _
      _ ≤ (J*L).choose (J*K)*L.choose K := Nat.mul_le_mul_right _ ih
      _ ≤ (J*L+L).choose (J*K+K) := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.choose_mul_le _ _ _ _
      _ = _ := by simp only [Nat.succ_mul]

theorem typedOutputs_le_fullOutputs (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.choose_pow_le (232*_root_.ThreeSum.Scales.muZero n) (_root_.ThreeSum.Scales.muZero n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  have hwidth : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(232*_root_.ThreeSum.Scales.muZero n)=232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum.Scales.muZero _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize
    ring
  have hcut : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*_root_.ThreeSum.Scales.muZero n=_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := rfl
  rw [hwidth,hcut] at h
  exact h

theorem four_le_scheduleSize (h : ℕ) : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize _root_.ThreeSum.LocalHashMoments.scheduleLength
  calc
    4 ≤ 320 := by decide
    _ ≤ 320*(2*h+1) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)

theorem localPrime_le_four_outputs (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ 4*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h := by
  have ho : 2^(2*h) ≤ _root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h := by
    by_cases hz : h=0
    · simp [hz,_root_.ThreeSum.LocalCoverBounds.outputCount]
    · exact (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.concrete_output_gt_pow (by omega)).le
  have hu := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_sq_upper h
  have hm := Nat.mul_le_mul_left (16*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h) ho
  nlinarith

theorem modulus_le_global_outputs (h J : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h^J*
      (J*(464*h)).choose (J*(2*h)) := by
  have hl : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.localPrime_le_four_outputs h).trans (Nat.mul_le_mul_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.four_le_scheduleSize h))
  have hp := Nat.pow_le_pow_left hl J
  rw [mul_pow] at hp
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus
  exact hp.trans (Nat.mul_le_mul_left _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.choose_pow_le (464*h) (2*h) J))

theorem modulus_le_tableCount (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.modulus_le_global_outputs (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  have hc : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(2*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))=_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
    rw [Nat.mul_comm,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.cutoff_eq]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.width_eq,hc] at hm
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n ≥ _ at hm
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.count_eq_scheduleCount] at hm
  exact hm

theorem bandSize_le_fullOutputs (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n := by
  have hb : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n := by
    apply (ceilDiv_le_iff_le_mul (a := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_pos n)).mpr
    exact Nat.le_mul_of_pos_left _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_pos n)
  have hr : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n := by
    have hs := Nat.sqrt_le_self (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n-1)
    have hp := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.typedOutputs_pos n
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot _root_.ThreeSum.LocalCoverBounds.rootCeiling
    omega
  exact hb.trans (hr.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.typedOutputs_le_fullOutputs n))

theorem scheduleCount_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf
  exact pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength_pos _) _

theorem bands_outputs_le_encoderCount (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  have hs : 1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.scheduleCount_pos n
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_right (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n) (Nat.mul_le_mul_left (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n) hs)
    _ ≤ 2*(_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount; ring

theorem input_le_encoderCount (n : ℕ) : n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n := (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount_mul_bounds n).1
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n := Nat.mul_le_mul_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bandSize_le_fullOutputs n)
    _ = _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n := Nat.mul_comm _ _
    _ ≤ _ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bands_outputs_le_encoderCount n











end ThreeSum.SourceBandCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Read source controls from the actually constructed local-cover header -/

namespace ThreeSum.EncodedColorCoverData
open _root_.ThreeSum.EncodedColorCoverData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs

theorem header_end (free h J : ℕ) : free+20 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd free h J :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.base_le_nextFree (_root_.ThreeSum.LightLocalCoverInit.base free) h).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.afterCover_le_keyEnd free h J)



end ThreeSum.EncodedColorCoverData

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





end ThreeSum.EncodedColorWantedData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite cost of both actual original-band catalogs and empty padding -/

namespace ThreeSum.SourceBandPairCosts
open _root_.ThreeSum.SourceBandPairCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.SourceBandPairData
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData





theorem tableCount_le_encoderCount {n : ℕ} (hn : 0 < n) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  have hb : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n := by
    have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount_mul_bounds n).1
    by_contra h
    have hz : _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n=0 := by omega
    rw [hz,Nat.mul_zero] at hp
    omega
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n := Nat.le_mul_of_pos_left _ hb
    _ ≤ 2*(_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount; ring

theorem modulus_le_encoderCount {n : ℕ} (hn : 0 < n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.modulus_le_tableCount n).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairCosts.tableCount_le_encoderCount hn)

theorem time_le_encoderCount {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum.LightSourceBandPair.time NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) U D ≤
      (2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+3905)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n+3139 := by
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.time_le_encoderCount (p := p) (U := U) (D := D) hNL
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.time_le_encoderCount (p := p) (U := U) (D := D) hNR
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairCosts.modulus_le_encoderCount hn
  unfold _root_.ThreeSum.LightSourceBandPair.time _root_.Light.fillTime
  nlinarith



end ThreeSum.SourceBandPairCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite resource charge of the actual original-array source host -/

namespace ThreeSum.SourceBandHostCosts
open _root_.ThreeSum.SourceBandHostCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales

theorem time_le_encoderCount {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.time NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) U D ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram.factor (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2)+
        2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+5205)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n+4859 := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairCosts.time_le_encoderCount (p := p) (U := U) (D := D) hn hNL hNR
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.time_le_encoderCount hn hNL hNR
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.time
  nlinarith











end ThreeSum.SourceBandHostCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite cost of computed source controls and their full host -/

namespace ThreeSum.SourceControlCosts
open _root_.ThreeSum.SourceControlCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales



theorem time_bound (h J : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.time h J ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.factor h J := by
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.time_bound (J*(464*h))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.time _root_.ThreeSum.LightNatPower.time _root_.Light.log2Time _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.factor
  omega



theorem time_le_encoderCount {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.time NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) U D ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram.factor (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2)+
        2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
        _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.factor (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))+5705)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n+4859 := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandHostCosts.time_le_encoderCount (p := p) (U := U) (D := D) hn hNL hNR
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.time_bound (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  have he : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := hn.trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.input_le_encoderCount n)
  have hm := Nat.le_mul_of_pos_right
    (_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.factor (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))+500) he
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.time
  nlinarith





end ThreeSum.SourceControlCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Uniform original-size budgets for the finite normalized source host -/

namespace ThreeSum.SourceFiniteCosts
open _root_.ThreeSum.SourceFiniteCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales









theorem word_mono {NL NR NL' NR' g p h J cut U D : ℕ} (hl : NL ≤ NL') (hr : NR ≤ NR') :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.word NL NR g p h J cut U D ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.word NL' NR' g p h J cut U D := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.word_mono (h := h) (J := J) hl hr
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.word _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.word _root_.ThreeSum.LightSourceBandPair.word
    _root_.ThreeSum.LightSourceBandStep.word _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanks.word _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.word
  omega

theorem time_le {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.time NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) U D ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.time n p U D :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.time_le_encoderCount hn hNL hNR

theorem space_le {base NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.space base NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) U D ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.space base n p U D :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.space_le_encoderCount hn hNL hNR



theorem word_le {NL NR n p U D : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.word NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) U D ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.word n p U D :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.word_mono hNL hNR

end ThreeSum.SourceFiniteCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Original-size resource envelope for the actual source-header adapter -/

namespace ThreeSum.EncodedColorSourcesCosts
open _root_.ThreeSum.EncodedColorSourcesCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales



theorem time_le {NL NR n p U M : ℕ} (hn : 0 < n) (hL : NL ≤ n) (hR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorSources.time NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) U M ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time n p U M := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.time_le (p := p) (U := U) (D := M) hn hL hR
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorSources.time _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time
  omega



end ThreeSum.EncodedColorSourcesCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained finite normalization and actual source controls in one contract -/

namespace ThreeSum.LightEncodedColorFiniteSources
open _root_.ThreeSum.LightEncodedColorFiniteSources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales





theorem free_le_base (free n p M : ℕ) [NeZero M] (xs : List ℤ) : free ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.base free n p M xs := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData.header_le_nextFree
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree free (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) xs.length)
    M (_root_.ThreeSum.LightGuardedWanted.left p xs)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.selected M p xs (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) : ℤ)
  have hk := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorCoverData.header_end free (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  change _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.base free n p M xs at h
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree at h
  omega

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}



end ThreeSum.LightEncodedColorFiniteSources

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.program_meets__implementation_f1d4a190fe {μ : ℕ → ℤ} {free av ae bv be cv ce tables rec vals n p U M : ℕ} [NeZero M]
    {originalA originalB originalC A B C xs : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {rA : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+17 ≤ lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hA : originalA.length ≤ n) (hB : originalB.length ≤ n) (hC : originalC.length ≤ n)
    (hav : av+n ≤ free) (hae : ae+2+2*n ≤ free)
    (hbv : bv+n ≤ free) (hbe : be+2+2*n ≤ free)
    (hcv : cv+n ≤ free) (hce : ce+2+2*n ≤ free)
    (htables : tables+_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ free)
    (hrecords : rec+4*_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ free)
    (hcatalog : _root_.ThreeSum.LightBandRawA.space vals (_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ free)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.base free n p M xs) n p U M ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.word n p U M : ℤ) ≤ lim.word)
    (hboundB : ∀ z ∈ originalB, |z| ≤ (U : ℤ)) (hboundC : ∀ z ∈ originalC, |z| ≤ (U : ℤ))
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Normalized μ av ae bv be cv ce tables rec vals (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)
      originalA originalB originalC A B C hsA hsB hsC rA)
    (hcover : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ free (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (hwanted : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree free (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) xs.length) M
      (_root_.ThreeSum.LightGuardedWanted.left p xs) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
      (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
      (_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.selected M p xs (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorSources.program 80 d (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.args free bv be cv ce n p xs.length) μ
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time n p U M)
      (fun r ν =>
        _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Normalized ν av ae bv be cv ce tables rec vals (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)
          originalA originalB originalC A B C hsA hsB hsC rA ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Stored ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.base free n p M xs) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p
          (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) B C
          (_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.selected M p xs (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) : ℤ) r ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored ν free (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output ν
          (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree free (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) xs.length) M
          (_root_.ThreeSum.LightGuardedWanted.left p xs) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
          (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
          (_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.selected M p xs (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.base free n p M xs)) := by
  have repB := H.2.2.1
  have repC := H.2.2.2.1
  have hnB : B.length ≤ n := repB.2.1.trans hB
  have hnC : C.length ≤ n := repC.2.1.trans hC
  have hbase := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.free_le_base free n p M xs
  have hdepth : d+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))+17 ≤ lim.depth := by
    rwa [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.width_eq]
  have hcut : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.width_eq]
    omega
  have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.space_le (base := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.base free n p M xs) (p := p) (U := U) (D := M)
    hn hnB hnC).trans hspace
  have hw' : (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.word B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) U M : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.word_le hnB hnC)).trans hword
  have run := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorSources.program_meets (μ := μ) (free := free)
    (p := p) (h := _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (J := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (cut := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (U := U) (M := M)
    (xs := xs) hw hdepth hp hcut (by omega) (by omega) (by omega) (by omega) hs hw'
    repB repC hboundB hboundC hcover hwanted
  apply run.mono (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time_le hn hnB hnC)
  intro r ν ⟨sources,cover,wanted,kept⟩
  exact ⟨H.keep kept hA hB hC (hav.trans hbase) (hae.trans hbase) (hbv.trans hbase) (hbe.trans hbase)
    (hcv.trans hbase) (hce.trans hbase) (htables.trans hbase) (hrecords.trans hbase) (hcatalog.trans hbase),
    sources,cover,wanted,kept⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.program_meets__implementation_f1d4a190fe) := (@ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.program_meets__implementation_f1d4a190fe)

#print axioms solution
