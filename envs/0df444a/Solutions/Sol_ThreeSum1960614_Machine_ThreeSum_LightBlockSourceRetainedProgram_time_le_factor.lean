-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram.time_le_factor
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:48:25.742708+00:00
-- url     : https://prove2.me/submissions/001e6bf5-b2cb-4bfe-9277-0bfa22838060

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
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
import Mathlib.Data.Fintype.Fin
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
import Theorems.Thm_ThreeSum_LightDownsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaStages_time_bound

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.LightBlockCoefficients
end ThreeSum.LightBlockCoefficients
namespace ThreeSum.LightBlockSourceHashes
end ThreeSum.LightBlockSourceHashes
namespace ThreeSum.LightBlockSourceRetainedProgram
end ThreeSum.LightBlockSourceRetainedProgram
namespace ThreeSum.LightMaskBits
end ThreeSum.LightMaskBits
namespace ThreeSum.LightMaskHashes
end ThreeSum.LightMaskHashes
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSourceFlagArray
end ThreeSum.LightSourceFlagArray
namespace ThreeSum.LightSourceGather
end ThreeSum.LightSourceGather
namespace ThreeSum.LightSourceMaskFlags
end ThreeSum.LightSourceMaskFlags
namespace ThreeSum.LightSourcePreparation
end ThreeSum.LightSourcePreparation
namespace ThreeSum.LightSourceRetainedStages
end ThreeSum.LightSourceRetainedStages
namespace ThreeSum.LightSourceRowFlag
end ThreeSum.LightSourceRowFlag
namespace ThreeSum.LightSourceTrim
end ThreeSum.LightSourceTrim
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients
end ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskBits
end ThreeSum1960614.Machine.ThreeSum.LightMaskBits
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskHashes
end ThreeSum1960614.Machine.ThreeSum.LightMaskHashes
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray
end ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceGather
end ThreeSum1960614.Machine.ThreeSum.LightSourceGather
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags
end ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags
namespace ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation
end ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages
end ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag
end ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceTrim
end ThreeSum1960614.Machine.ThreeSum.LightSourceTrim
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
end ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Constructing the positional one-hot coefficient arrays

The program reads one map occurrence per block. It copies both symbol rows
of that map and multiplies them by the block's radix power. The powers are
built internally. All original map and occurrence data are preserved.
-/

namespace ThreeSum.LightBlockCoefficients
open _root_.ThreeSum.LightBlockCoefficients


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

























theorem time_bound (J L : ℕ) : _root_.ThreeSum.LightBlockCoefficients.time J L ≤ 300*(J+1)*(L+1) := by
  unfold _root_.ThreeSum.LightBlockCoefficients.time _root_.ThreeSum.LightBlockCoefficients.roundTime _root_.ThreeSum.LightScaleArray.time _root_.Light.powTableTime
  nlinarith

end ThreeSum.LightBlockCoefficients

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

















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (L : ℕ) : _root_.ThreeSum.LightMaskBits.time L ≤ 300*(L+1)^2 := by
  unfold _root_.ThreeSum.LightMaskBits.time _root_.Light.powTableTime _root_.ThreeSum.LightMaskErase.time
  nlinarith

end ThreeSum.LightMaskBits

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Evaluating a whole list of one-hot mask hashes

This wrapper builds the powers table itself, hashes each stored mask, and
writes the raw nonnegative values. It is shared by the local-cover matrix
construction and input-source encoding. The cost is linear in the number
of masks times their width; no evaluation oracle is assumed.
-/

namespace ThreeSum.LightMaskHashes
open _root_.ThreeSum.LightMaskHashes


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

set_option maxHeartbeats 1000000









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (L n : ℕ) : _root_.ThreeSum.LightMaskHashes.time L n ≤ 300*(L+1)*(n+1) := by
  unfold _root_.ThreeSum.LightMaskHashes.time _root_.Light.powTableTime _root_.ThreeSum.LightOneHot.time
  nlinarith

end ThreeSum.LightMaskHashes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Residue-indexed source lookup and independent trimming

Each endpoint is reduced by the global modulus and its original-input
histogram count is gathered. The already constructed independent endpoint
flag selects that count or zero. No search through the original inputs is
performed for individual subset masks.
-/

namespace ThreeSum.LightSourceGather
open _root_.ThreeSum.LightSourceGather


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (n U : ℕ) : _root_.ThreeSum.LightSourceGather.time n U ≤ 157*n*(Nat.log 2 (U+1)+1)+6 := by
  unfold _root_.ThreeSum.LightSourceGather.time _root_.ThreeSum.LightResidues.residueBudget
  nlinarith

end ThreeSum.LightSourceGather

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing both raw endpoint arrays from selected block maps

The program constructs radix-weighted coefficient rows itself, then hashes
each stored subset in both orientations. Both endpoint arrays and the
coefficient rows are retained. The final specialization identifies the
results with the original block encoding, preserving occurrence indices.
-/

namespace ThreeSum.LightBlockSourceHashes
open _root_.ThreeSum.LightBlockSourceHashes


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









theorem time_bound (J L n : ℕ) :
    _root_.ThreeSum.LightBlockSourceHashes.time J L n ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+200 := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.time_bound J L
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskHashes.time_bound (J*L) n
  unfold _root_.ThreeSum.LightBlockSourceHashes.time
  nlinarith

end ThreeSum.LightBlockSourceHashes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Source stages gathered from a retained original-input histogram

The histogram is built once for a source band and fixed modulus/offset by
`LightSourceHistogram`. This program then gathers the independently trimmed
source for each occurrence vector and runs the actual suffix transforms.
Neither the original array nor the full histogram is rescanned in this loop.
-/

namespace ThreeSum.LightSourceRetainedStages
open _root_.ThreeSum.LightSourceRetainedStages


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









theorem time_bound {L cut E : ℕ} (hcut : cut ≤ L) :
    _root_.ThreeSum.LightSourceRetainedStages.time L cut E ≤ 157*_root_.ThreeSum.SubsetAddress.downsetCap L cut*(Nat.log 2 (E+1)+1)+
      6000*(L+1)^4*(_root_.ThreeSum.SubsetAddress.downsetCap L cut+1)+106 := by
  have hg := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceGather.time_bound (_root_.ThreeSum.SubsetAddress.downsetCap L cut) E
  have hz := _root_.ThreeSum.LightZetaStages.time_bound hcut
  unfold _root_.ThreeSum.LightSourceRetainedStages.time
  omega

end ThreeSum.LightSourceRetainedStages

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













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





theorem time_bound (L U : ℕ) :
    _root_.ThreeSum.LightSourceRowFlag.time L U ≤ 150*L+464*(Nat.log 2 (L*U+1)+1) := by
  unfold _root_.ThreeSum.LightSourceRowFlag.time _root_.ThreeSum.LightSourceRowScan.time _root_.ThreeSum.LightResidues.residueBudget _root_.ThreeSum.LightSourceFlagTest.time
  nlinarith

end ThreeSum.LightSourceRowFlag

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















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (J L U : ℕ) :
    _root_.ThreeSum.LightSourceTrim.time J L U ≤ J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+100 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.time_bound L U
  unfold _root_.ThreeSum.LightSourceTrim.time
  exact Nat.add_le_add_right (Nat.mul_le_mul_left J (Nat.add_le_add_right hh 250)) 100

end ThreeSum.LightSourceTrim

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing independent endpoint flags directly from a global mask

The fixed program creates its own powers and Boolean coordinate row, then
performs the actual selected-block trimming scan. There is no Boolean-bit or
trim-flag oracle in the contract.
-/

namespace ThreeSum.LightSourceMaskFlags
open _root_.ThreeSum.LightSourceMaskFlags


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (J L U : ℕ) :
    _root_.ThreeSum.LightSourceMaskFlags.time J L U ≤ 300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+200 := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.time_bound (J*L)
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.time_bound J L U
  unfold _root_.ThreeSum.LightSourceMaskFlags.time
  omega

end ThreeSum.LightSourceMaskFlags

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing contiguous arrays of independent source flags

The actual loop reads the already enumerated global masks. For each one it
constructs both independent flags from selected maps and retained bucket
counts, then writes the two orientations in separate adjacent arrays. Powers,
Boolean coordinates and local arithmetic scratch are reused across masks.
-/

namespace ThreeSum.LightSourceFlagArray
open _root_.ThreeSum.LightSourceFlagArray


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (n J L U : ℕ) :
    _root_.ThreeSum.LightSourceFlagArray.time n J L U ≤ n*(300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+10 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags.time_bound J L U
  unfold _root_.ThreeSum.LightSourceFlagArray.time
  exact Nat.add_le_add_right (Nat.mul_le_mul_left n (by omega)) 10

end ThreeSum.LightSourceFlagArray

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual endpoint and independent-flag preparation from stored selected maps

The host constructs radix coefficient rows, both raw endpoint arrays, and
both independent trim-flag arrays. All four arrays are retained for the
original-input histogram/source-stage constructors.
-/

namespace ThreeSum.LightSourcePreparation
open _root_.ThreeSum.LightSourcePreparation


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (n J L U : ℕ) :
    _root_.ThreeSum.LightSourcePreparation.time n J L U ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+
      n*(300*(J*L+1)^2+J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+410 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.time_bound J L n
  have hf := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.time_bound n J L U
  unfold _root_.ThreeSum.LightSourcePreparation.time
  omega

end ThreeSum.LightSourcePreparation

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Literal efficient program for original source-stage construction

The 41 procedures construct all occurrence-dependent data and reuse the
original band histograms. The cost has no factor proportional to the number
of original input incidences or the dense global modulus in this inner loop.
-/

namespace ThreeSum.LightBlockSourceRetainedProgram
open _root_.ThreeSum.LightBlockSourceRetainedProgram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000







theorem time_bound {h J cut : ℕ} (hcut : cut ≤ J*(464*h)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.time h J cut ≤
      1200*(J*(464*h)+1)^2*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+1)+
      300*(J+1)*(464*h+1)+600*(J*(464*h)+1)*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+1)+
      _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut*(300*(J*(464*h)+1)^2+
        J*(150*(464*h)+464*(Nat.log 2 ((464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1)+1)+250)+400)+
      314*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut*(Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1)+1)+
      12000*(J*(464*h)+1)^4*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+1)+1122 := by
  have he := _root_.ThreeSum.LightDownsetEnumerationSetup.time_bound hcut
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.time_bound (_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut) J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.time_bound (E := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) hcut
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.time
  nlinarith





end ThreeSum.LightBlockSourceRetainedProgram

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram.time_le_factor__implementation_b0c3802c73 {h J cut : ℕ} (hcut : cut ≤ J*(464*h)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.time h J cut ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram.factor h J*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+1) := by
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram.time_bound hcut
  have hc := Nat.le_succ (_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut)
  have hsetup : 300*(J+1)*(464*h+1) ≤
      300*(J+1)*(464*h+1)*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have htrim := Nat.mul_le_mul_right
    (300*(J*(464*h)+1)^2+J*(150*(464*h)+464*(Nat.log 2 ((464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1)+1)+250)+400) hc
  have hg := Nat.mul_le_mul_left (314*(Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1)+1)) hc
  have hconst : 1122 ≤ 1122*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+1) := by omega
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram.factor
  nlinarith
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram.time_le_factor__implementation_b0c3802c73) := (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram.time_le_factor__implementation_b0c3802c73)

#print axioms solution
