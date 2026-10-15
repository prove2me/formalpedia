-- Prove2me | solution 1 for ThreeSum.LightBlockSourceRetainedProgram.time_le_factor
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:39:34.894232+00:00
-- url     : https://prove2.me/submissions/1783c194-cdfc-4472-8601-63b124dc5f97

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_LightDownsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaStages_time_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightBlockSourceRetainedHost
end ThreeSum.LightBlockSourceRetainedHost
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
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

section


/-!
# Constructing the positional one-hot coefficient arrays

The program reads one map occurrence per block. It copies both symbol rows
of that map and multiplies them by the block's radix power. The powers are
built internally. All original map and occurrence data are preserved.
-/

namespace ThreeSum.LightBlockCoefficients

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : Limits} {P : Program}
















































































































































































































theorem time_bound (J L : ℕ) : time J L ≤ 300*(J+1)*(L+1) := by
  unfold time roundTime LightScaleArray.time powTableTime
  nlinarith

end ThreeSum.LightBlockCoefficients

end

section


/-!
# Evaluating a whole list of one-hot mask hashes

This wrapper builds the powers table itself, hashes each stored mask, and
writes the raw nonnegative values. It is shared by the local-cover matrix
construction and input-source encoding. The cost is linear in the number
of masks times their width; no evaluation oracle is assumed.
-/

namespace ThreeSum.LightMaskHashes

open Light LightSubsetAddress

set_option maxHeartbeats 1000000



















variable {lim : Limits} {P : Program} {d : ℕ}









































































































theorem time_bound (L n : ℕ) : time L n ≤ 300*(L+1)*(n+1) := by
  unfold time powTableTime LightOneHot.time
  nlinarith

end ThreeSum.LightMaskHashes

end

section


/-!
# Constructing both raw endpoint arrays from selected block maps

The program constructs radix-weighted coefficient rows itself, then hashes
each stored subset in both orientations. Both endpoint arrays and the
coefficient rows are retained. The final specialization identifies the
results with the original block encoding, preserving occurrence indices.
-/

namespace ThreeSum.LightBlockSourceHashes

open Light BlockCoefficientRows

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000





























variable {lim : Limits} {P : Program} {d : ℕ}



















































































































































theorem time_bound (J L n : ℕ) :
    time J L n ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+200 := by
  have hc := LightBlockCoefficients.time_bound J L
  have hh := LightMaskHashes.time_bound (J*L) n
  unfold time
  nlinarith

end ThreeSum.LightBlockSourceHashes

end

section


/-!
# Residue-indexed source lookup and independent trimming

Each endpoint is reduced by the global modulus and its original-input
histogram count is gathered. The already constructed independent endpoint
flag selects that count or zero. No search through the original inputs is
performed for individual subset masks.
-/

namespace ThreeSum.LightSourceGather

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000




























variable {lim : Limits} {P : Program} {d : ℕ}













































































































theorem time_bound (n U : ℕ) : time n U ≤ 157*n*(Nat.log 2 (U+1)+1)+6 := by
  unfold time LightResidues.residueBudget
  nlinarith

end ThreeSum.LightSourceGather

end

section


/-!
# Source stages gathered from a retained original-input histogram

The histogram is built once for a source band and fixed modulus/offset by
`LightSourceHistogram`. This program then gathers the independently trimmed
source for each occurrence vector and runs the actual suffix transforms.
Neither the original array nor the full histogram is rescanned in this loop.
-/

namespace ThreeSum.LightSourceRetainedStages

open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000








































variable {lim : Limits} {P : Program} {d : ℕ}















































































theorem time_bound {L cut E : ℕ} (hcut : cut ≤ L) :
    time L cut E ≤ 157*downsetCap L cut*(Nat.log 2 (E+1)+1)+
      6000*(L+1)^4*(downsetCap L cut+1)+106 := by
  have hg := LightSourceGather.time_bound (downsetCap L cut) E
  have hz := LightZetaStages.time_bound hcut
  unfold time
  omega

end ThreeSum.LightSourceRetainedStages

end

section


/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits

open Light LightSubsetAddress MaskErase































variable {lim : Limits} {P : Program} {d : ℕ}






















































































theorem time_bound (L : ℕ) : time L ≤ 300*(L+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith

end ThreeSum.LightMaskBits

end

section


/-!
# Constructing both independent trimming flags for one block row

The program counts and hashes the actual Boolean row, reduces both local
hashes, reads the selected map's retained bucket tables, and independently
tests the two endpoint buckets. The cardinality test is performed for both
orientations, with no disjoint-pair or shared trimming assumption.
-/

namespace ThreeSum.LightSourceRowFlag

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000




























variable {lim : Limits} {P : Program} {d : ℕ}






















































































































theorem time_bound (L U : ℕ) :
    time L U ≤ 150*L+464*(Nat.log 2 (L*U+1)+1) := by
  unfold time LightSourceRowScan.time LightResidues.residueBudget LightSourceFlagTest.time
  nlinarith

end ThreeSum.LightSourceRowFlag

end

section


/-!
# Independent endpoint trimming across all selected blocks

The loop reads each occurrence index and its exact selected-candidate index,
then calls the concrete row flag constructor on the corresponding map and
retained bucket tables. The product of the independent Boolean flags is
written in each orientation. Input Boolean rows and tables are preserved.
-/

namespace ThreeSum.LightSourceTrim

open Light SourceFlagProduct

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000























































variable {lim : Limits} {P : Program} {d : ℕ}





































































































































































theorem time_bound (J L U : ℕ) :
    time J L U ≤ J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+100 := by
  have hh := LightSourceRowFlag.time_bound L U
  unfold time
  exact Nat.add_le_add_right (Nat.mul_le_mul_left J (Nat.add_le_add_right hh 250)) 100

end ThreeSum.LightSourceTrim

end

section


/-!
# Constructing independent endpoint flags directly from a global mask

The fixed program creates its own powers and Boolean coordinate row, then
performs the actual selected-block trimming scan. There is no Boolean-bit or
trim-flag oracle in the contract.
-/

namespace ThreeSum.LightSourceMaskFlags

open Light SourceFlagProduct

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000



























variable {lim : Limits} {P : Program} {d : ℕ}






































































































theorem time_bound (J L U : ℕ) :
    time J L U ≤ 300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+200 := by
  have hb := LightMaskBits.time_bound (J*L)
  have ht := LightSourceTrim.time_bound J L U
  unfold time
  omega

end ThreeSum.LightSourceMaskFlags

end

section


/-!
# Constructing contiguous arrays of independent source flags

The actual loop reads the already enumerated global masks. For each one it
constructs both independent flags from selected maps and retained bucket
counts, then writes the two orientations in separate adjacent arrays. Powers,
Boolean coordinates and local arithmetic scratch are reused across masks.
-/

namespace ThreeSum.LightSourceFlagArray

open Light SourceFlagProduct

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000




































variable {lim : Limits} {P : Program} {d : ℕ}














































































































































theorem time_bound (n J L U : ℕ) :
    time n J L U ≤ n*(300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+10 := by
  have hh := LightSourceMaskFlags.time_bound J L U
  unfold time
  exact Nat.add_le_add_right (Nat.mul_le_mul_left n (by omega)) 10

end ThreeSum.LightSourceFlagArray

end

section


/-!
# Actual endpoint and independent-flag preparation from stored selected maps

The host constructs radix coefficient rows, both raw endpoint arrays, and
both independent trim-flag arrays. All four arrays are retained for the
original-input histogram/source-stage constructors.
-/

namespace ThreeSum.LightSourcePreparation

open Light BlockCoefficientRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
























variable {lim : Limits} {P : Program} {d : ℕ}
























































































































theorem time_bound (n J L U : ℕ) :
    time n J L U ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+
      n*(300*(J*L+1)^2+J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+410 := by
  have hh := LightBlockSourceHashes.time_bound J L n
  have hf := LightSourceFlagArray.time_bound n J L U
  unfold time
  omega

end ThreeSum.LightSourcePreparation

end

section


/-!
# Literal efficient program for original source-stage construction

The 41 procedures construct all occurrence-dependent data and reuse the
original band histograms. The cost has no factor proportional to the number
of original input incidences or the dense global modulus in this inner loop.
-/

namespace ThreeSum.LightBlockSourceRetainedProgram

open Light LightPascal LightSubsetAddress LightBlockSourceRetainedHost
open LocalCoverBounds SubsetAddress BlockSourceEncoding LightBlockSourceBuild

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000






























theorem time_bound {h J cut : ℕ} (hcut : cut ≤ J*(512*h)) :
    LightBlockSourceRetainedHost.time h J cut ≤
      1200*(J*(512*h)+1)^2*(downsetCap (J*(512*h)) cut+1)+
      300*(J+1)*(512*h+1)+600*(J*(512*h)+1)*(downsetCap (J*(512*h)) cut+1)+
      downsetCap (J*(512*h)) cut*(300*(J*(512*h)+1)^2+
        J*(150*(512*h)+464*(Nat.log 2 ((512*h)*localPrime h+1)+1)+250)+400)+
      314*downsetCap (J*(512*h)) cut*(Nat.log 2 (endpointBound h J+1)+1)+
      12000*(J*(512*h)+1)^4*(downsetCap (J*(512*h)) cut+1)+1122 := by
  have he := LightDownsetEnumerationSetup.time_bound hcut
  have hp := LightSourcePreparation.time_bound (downsetCap (J*(512*h)) cut) J (512*h) (localPrime h)
  have hs := LightSourceRetainedStages.time_bound (E := endpointBound h J) hcut
  unfold LightBlockSourceRetainedHost.time
  nlinarith






theorem time_le_factor_sourceProof {h J cut : ℕ} (hcut : cut ≤ J*(512*h)) :
    LightBlockSourceRetainedHost.time h J cut ≤ factor h J*(downsetCap (J*(512*h)) cut+1) := by
  have ht := time_bound hcut
  have hc := Nat.le_succ (downsetCap (J*(512*h)) cut)
  have hsetup : 300*(J+1)*(512*h+1) ≤
      300*(J+1)*(512*h+1)*(downsetCap (J*(512*h)) cut+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have htrim := Nat.mul_le_mul_right
    (300*(J*(512*h)+1)^2+J*(150*(512*h)+464*(Nat.log 2 ((512*h)*localPrime h+1)+1)+250)+400) hc
  have hg := Nat.mul_le_mul_left (314*(Nat.log 2 (endpointBound h J+1)+1)) hc
  have hconst : 1122 ≤ 1122*(downsetCap (J*(512*h)) cut+1) := by omega
  unfold factor
  nlinarith

end ThreeSum.LightBlockSourceRetainedProgram

end


theorem solution : ∀ {h J cut : Nat},
  @LE.le.{0} Nat instLENat cut
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) →
    @LE.le.{0} Nat instLENat (ThreeSum.LightBlockSourceRetainedHost.time h J cut)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (ThreeSum.LightBlockSourceRetainedProgram.factor h J)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (ThreeSum.SubsetAddress.downsetCap
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
            cut)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @ThreeSum.LightBlockSourceRetainedProgram.time_le_factor_sourceProof

#print axioms solution
