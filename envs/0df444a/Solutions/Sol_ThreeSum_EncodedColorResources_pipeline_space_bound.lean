-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.pipeline_space_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:34:04.068142+00:00
-- url     : https://prove2.me/submissions/a3186778-d4b1-41c4-b74e-e9fa880f389b

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
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_EncodedColorResources_dimensions
import Theorems.Thm_ThreeSum_EncodedColorResources_encoder_le
import Theorems.Thm_ThreeSum_EncodedColorResources_global_keys_space_bound
import Theorems.Thm_ThreeSum_EncodedColorResources_source_space_bound
import Theorems.Thm_ThreeSum_EncodedColorResources_source_storage_le
import Theorems.Thm_ThreeSum_EncodedColorResources_wanted_source_base_bound
import Theorems.Thm_ThreeSum_KaratsubaInterface_capacity_lt_twice
import Theorems.Thm_ThreeSum_LightBandRawAResources_cells_bound
import Theorems.Thm_ThreeSum_LightLocalCoverMagnitude_bounds
import Theorems.Thm_ThreeSum_LightLocalCoverResources_space_polynomial
import Theorems.Thm_ThreeSum_LocalParameterBounds_space_bound
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMagnitude
end ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum.LightLocalCoverMetadata
end ThreeSum.LightLocalCoverMetadata
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.ModuloCosts
end ThreeSum.ModuloCosts
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum.UniformStageBounds
end ThreeSum.UniformStageBounds

section


/-!
# The arithmetic and balancing work outside the six reporting stages

The finite bounds here include complete modular-counting invocations, their
signed-remainder bit cost, and the actual correlation/minimum routine. They
augment the six-stage reporting budget. The whole solver still has to charge
its actual host operations to this combined budget.
-/

namespace ThreeSum.ArithmeticStageBounds

open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology

set_option maxHeartbeats 1000000



















theorem maxMod_pos (n : ℕ) : 0 < maxMod n := by
  unfold maxMod
  exact Nat.mul_pos (radix_pos n) (Nat.pow_pos (by have := primeWindow_ge_two n; omega))






























noncomputable section


































































































































end
end ThreeSum.ArithmeticStageBounds

end

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition





theorem size_le (n g : ℕ) : size n g ≤ n := by
  unfold size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega
































































































end ThreeSum.BandPartition

end

section


/-! # A packed layout for the complete local-cover constructor -/

namespace ThreeSum.LightLocalCoverLayout

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables






























theorem schedule_end_le_space (base h : ℕ) :
    scheduleMaps base h+scheduleSize h*(2*(512*h)) ≤ space base h := Nat.le_max_right ..


















end ThreeSum.LightLocalCoverLayout

end

section


/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata

set_option maxHeartbeats 1000000






















































theorem nextFree_le_space (base h : ℕ) : nextFree base h ≤ space base h :=
  schedule_end_le_space base h

end ThreeSum.LightLocalCoverRetention

end

section


/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000























theorem keyEnd_le_space (free h J : ℕ) : keyEnd free h J ≤ LightCoverKeys.space free h J := by
  have hg : LightRadixKeys.space (LightGlobalKeys.scratch (LightCoverKeys.afterCover free h) h)
      (LightGlobalKeys.localCount h) J ≤ LightGlobalKeys.space (LightCoverKeys.afterCover free h) h J :=
    le_max_right _ _
  exact hg.trans (le_max_right _ _)










































end ThreeSum.LightCoverKeyData

end

section


/-!
# Exact resource formulas for the original-input band and incidence program

These formulas use the existing selected-color layout without changing any
address or procedure. The physical BC, AB, AC owner records and the packed
value, owner, and sorted-position arrays are all included in the extent.
-/

namespace ThreeSum.LightBandRawAResources

open Light EncodedColorLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000




theorem space_eq (free W n g : ℕ) :
    LightBandRawAColor.space (tables free n) (vals free n g) W n g=free+cells W n g := by
  unfold cells LightBandRawAColor.space LightColorBands.space ColorBandBounds.space
    LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase LightBandRawA.capacity
    vals rec tables ce cv be bv ae av class2 class1 class0 colors
  omega












theorem count_le (n g : ℕ) : ColorBandBounds.count n g ≤ 3*n^2 :=
  Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (BandPartition.size_le n g) 2)






















end ThreeSum.LightBandRawAResources

end

section


/-!
# The complete local-cover program fits the uniform local-search budget

Every bound below is for the actual fixed program, including mask and
coefficient construction, counting division, histograms, matrix assembly,
the original greedy loop, and selected-row gathering.
-/

namespace ThreeSum.LightLocalCoverResources

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude

set_option maxHeartbeats 1800000
















































































































































theorem space_bound (base h : ℕ) : space base h ≤ base+envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  apply (space_polynomial (bounds h) base).trans
  apply Nat.add_le_add_left
  calc
    20*(magnitude h)^3 ≤ 2^5*(magnitude h)^3 := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(5+600000*(h+1)^2*3) := by rw [magnitude,← pow_mul,← pow_add]
    _ ≤ envelope h := Nat.pow_le_pow_right (by decide) (by omega)





















































end ThreeSum.LightLocalCoverResources

end

section


/-! # Resource bounds for the complete h-and-free local-cover initializer -/

namespace ThreeSum.LightLocalCoverInitResources

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout

set_option maxHeartbeats 1500000



theorem parameters_envelope_le (h : ℕ) :
    LocalParameterBounds.envelope h ≤ LightLocalCoverResources.envelope h := by
  unfold LocalParameterBounds.envelope LightLocalCoverResources.envelope
  apply Nat.pow_le_pow_right (by decide)
  nlinarith only [Nat.zero_le (h*h)]

theorem constant_le (h : ℕ) : 600 ≤ LightLocalCoverResources.envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  exact (by decide : 600 ≤ 2^10).trans
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem four_envelope_le (h : ℕ) :
    4*LightLocalCoverResources.envelope h ≤ envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ = 2^2*2^(4000000*(h+1)^2) := rfl
    _ = 2^(2+4000000*(h+1)^2) := (pow_add _ _ _).symm
    _ ≤ envelope h := Nat.pow_le_pow_right (by decide) (by omega)
























theorem space_bound (free h : ℕ) : LightLocalCoverInit.space free h ≤ free+envelope h := by
  have hp := (LocalParameterBounds.space_bound (LightLocalCoverInit.base free) h).trans
    (Nat.add_le_add_left (parameters_envelope_le h) (LightLocalCoverInit.base free))
  have hc := LightLocalCoverResources.space_bound (LightLocalCoverInit.base free) h
  have hk := constant_le h
  have hm : LightLocalCoverInit.space free h ≤ free+4*LightLocalCoverResources.envelope h := by
    unfold LightLocalCoverInit.space LightLocalCoverInit.base at *
    omega
  exact hm.trans (Nat.add_le_add_left (four_envelope_le h) free)








































































end ThreeSum.LightLocalCoverInitResources

end

section


/-! # A proved polynomial scale for the selected-color program's dimensions -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000








theorem scale_bounds (n : ℕ) : 100 ≤ scale n ∧ n+1 ≤ scale n ∧
    SharedReportingBankResourceBounds.magnitude n ≤ scale n ∧ localEnvelope n ≤ scale n ∧
    maxMod n ≤ scale n ∧ primeWindow n ≤ scale n := by
  unfold scale
  omega

theorem local_bounds (n : ℕ) : LightLocalCoverMagnitude.Bounds (half n) (scale n) := by
  have hm : LightLocalCoverMagnitude.magnitude (half n) ≤ localEnvelope n := by
    unfold LightLocalCoverMagnitude.magnitude localEnvelope LightLocalCoverInitResources.envelope
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))
  have hs := hm.trans (scale_bounds n).2.2.2.1
  have H := LightLocalCoverMagnitude.bounds (half n)
  exact ⟨H.positive.trans hs,H.width.trans hs,H.vertices.trans hs,H.prime.trans hs,
    H.cap.trans hs,H.candidates.trans hs,H.rounds.trans hs,H.decodePower.trans hs,H.maskPower.trans hs⟩

















theorem powers (n : ℕ) : 2^(width n+1) ≤ scale n ∧
    LightBlockSourceCatalog.count (half n) (blocks n) ≤ scale n ∧
    localPrime (half n)^(blocks n)*localPrime (half n) ≤ scale n ∧
    2^(blocks n) ≤ scale n := by
  have H := SharedReportingBankResourceBounds.components n
  have hm := (scale_bounds n).2.2.1
  refine ⟨H.widthPower.trans hm,H.occurrence.trans hm,H.primePower.trans hm,?_⟩
  have htwo : (2 : ℕ) ≤ 2^(512*half n)+1 := by have hh := Nat.two_pow_pos (512*half n); omega
  exact (Nat.pow_le_pow_left htwo (blocks n)).trans (H.radixPower.trans hm)

theorem modulus_le (n : ℕ) : BlockSourceEncoding.modulus (half n) (blocks n) ≤ scale n := by
  exact (Nat.le_mul_of_pos_right _ (localPrime_pos (half n))).trans (powers n).2.2.1






theorem radix_power_le (n : ℕ) : (localPrime (half n)+1)^(blocks n) ≤ (scale n)^2 := by
  have hp := localPrime_pos (half n)
  have hmod := modulus_le n
  calc
    _ ≤ (2*localPrime (half n))^(blocks n) := Nat.pow_le_pow_left (by omega) _
    _ = 2^(blocks n)*localPrime (half n)^(blocks n) := mul_pow _ _ _
    _ ≤ scale n*scale n := Nat.mul_le_mul (powers n).2.2.2 hmod
    _ = _ := by ring



















theorem totalKeys_le (n : ℕ) : LightGuardedWanted.totalKeys (half n) (blocks n) ≤ (scale n)^2 := by
  have hq : outputCount (512*half n) (half n)^(blocks n) ≤ scale n := by
    calc
      _ ≤ (2^(512*half n))^(blocks n) := Nat.pow_le_pow_left (Nat.choose_le_two_pow _ _) _
      _ = 2^(width n) := by unfold width; rw [← pow_mul]; congr 1; ring
      _ ≤ 2^(width n+1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ scale n := (powers n).1
  unfold LightGuardedWanted.totalKeys LightGlobalKeys.localCount
  rw [mul_pow]
  exact (Nat.mul_le_mul (powers n).2.1 hq).trans_eq (pow_two _).symm

theorem keyBound_le (n : ℕ) : LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n) ≤ 3*(scale n)^4 := by
  have hP := (scale_bounds n).2.2.2.2.1
  have hL : 512*half n ≤ scale n := by have h := (local_bounds n).width; omega
  have hp : localPrime (half n) ≤ scale n := by have h := (local_bounds n).prime; omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul hL hp) (radix_power_le n)
  have hs4 : scale n ≤ (scale n)^4 := Nat.le_self_pow (by decide) _
  unfold LightGuardedWanted.keyBound
  nlinarith only [hm,hP,hs4]

noncomputable section


















end
end ThreeSum.EncodedColorResources

end

section


/-! # Polynomial bounds for the retained local cover and complete global key array -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000





theorem after_cover_bound (free n : ℕ) : LightCoverKeys.afterCover free (half n) ≤ free+scale n := by
  have hs := LightLocalCoverInitResources.space_bound free (half n)
  have he := LightLocalCoverRetention.nextFree_le_space (LightLocalCoverInit.base free) (half n)
  have hm : LightLocalCoverLayout.space (LightLocalCoverInit.base free) (half n) ≤
      LightLocalCoverInit.space free (half n) := le_max_right _ _
  exact ((he.trans hm).trans hs).trans (Nat.add_le_add_left (scale_bounds n).2.2.2.1 free)


























theorem cover_space_bound (free n : ℕ) :
    LightCoverKeys.space free (half n) (blocks n) ≤ free+20*(scale n)^3 := by
  have hb := (scale_bounds n).1
  have hlocal := LightLocalCoverInitResources.space_bound free (half n)
  change LightLocalCoverInit.space free (half n) ≤ free+localEnvelope n at hlocal
  have henv := (scale_bounds n).2.2.2.1
  have hafter := after_cover_bound free n
  have hglobal := global_keys_space_bound (LightCoverKeys.afterCover free (half n)) n
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  unfold LightCoverKeys.space
  apply max_le <;> nlinarith only [hlocal,henv,hafter,hglobal,hp3]

theorem key_end_bound (free n : ℕ) :
    LightCoverKeyData.keyEnd free (half n) (blocks n) ≤ free+20*(scale n)^3 :=
  (LightCoverKeyData.keyEnd_le_space free (half n) (blocks n)).trans (cover_space_bound free n)

























end ThreeSum.EncodedColorResources

end

section


/-! # Affine storage and finite word bounds for the unchanged prime host -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface

set_option maxHeartbeats 2400000
set_option maxRecDepth 13000

theorem count_le (n : ℕ) : ColorBandBounds.count n (bandSize n) ≤ 3*(scale n)^2 := by
  have hn : n ≤ scale n := by have h := (scale_bounds n).2.1; omega
  exact (LightBandRawAResources.count_le n (bandSize n)).trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hn 2))

theorem incidence_cap_le (n : ℕ) : EncodedColorStageCosts.incidenceCap n ≤ 3*(scale n)^3 := by
  have hh := Nat.mul_le_mul (dimensions n).2.2.2.1 (count_le n)
  unfold EncodedColorStageCosts.incidenceCap
  nlinarith only [hh]

theorem normalized_cells_bound (n : ℕ) :
    LightBandRawAResources.cells (inputBits n+1) n (bandSize n) ≤ 1000*(scale n)^3 := by
  have hm : SharedReportingBankResourceBounds.magnitude n+1 ≤ scale n := by unfold scale; omega
  have hn := (scale_bounds n).2.1
  apply (LightBandRawAResources.cells_bound n).trans
  unfold LightBandRawAResources.envelope LightBandRawAResources.base
  have hh := Nat.mul_le_mul hm (Nat.pow_le_pow_left hn 2)
  nlinarith only [hh]

theorem normalized_space_bound (free n : ℕ) :
    LightEncodedColorNormalize.space free n ≤ free+1000*(scale n)^3+1 := by
  unfold LightEncodedColorNormalize.space
  rw [LightBandRawAResources.space_eq]
  exact Nat.add_le_add_right (Nat.add_le_add_left (normalized_cells_bound n) free) 1

theorem normalized_end_bound (free n : ℕ) : normalizedEnd free n (bandSize n) ≤ free+1000*(scale n)^3 := by
  have hh : normalizedEnd free n (bandSize n) ≤
      LightBandRawAColor.space (tables free n) (vals free n (bandSize n)) (inputBits n+1) n (bandSize n) :=
    le_max_right _ _
  rw [LightBandRawAResources.space_eq] at hh
  exact hh.trans (Nat.add_le_add_left (normalized_cells_bound n) free)

theorem prime_address_bound (free n : ℕ) : prime free n (bandSize n) ≤ free+1000*(scale n)^3+1 :=
  Nat.add_le_add_right (normalized_end_bound free n) 1

theorem depth_control_bound (n : ℕ) : LightBandPrimeDepth.depth (radix n) (primeWindow n) ≤ scale n := by
  exact ((Nat.log_le_self _ _).trans (Nat.div_le_self _ _)).trans (dimensions n).2.2.2.2

theorem cover_address_bound (free n : ℕ) :
    EncodedColorPipelineData.coverBase free n ≤ free+2000*(scale n)^3 := by
  have hp := prime_address_bound free n
  have hy := (scale_bounds n).2.2.2.2.2
  have hd := depth_control_bound n
  have hb := (scale_bounds n).1
  unfold EncodedColorPipelineData.coverBase cover EncodedColorPrimeData.nextFree
    EncodedColorPrimeData.prefixBase EncodedColorPrimeData.poolBase
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  nlinarith only [hp,hy,hd,hb,hp3]













theorem capacity_bound (n : ℕ) : capacity (maxMod n) ≤ 2*scale n :=
  (capacity_lt_twice (maxMod_pos n)).le.trans (Nat.mul_le_mul_left 2 (scale_bounds n).2.2.2.2.1)


































































theorem prime_core_space_bound (free n U : ℕ) :
    LightEncodedColorPrimeCore.space free (maxMod n) (bandSize n) (radix n) (primeWindow n) U ≤
      free+40*scale n+U+10 := by
  have hy := (scale_bounds n).2.2.2.2.2
  have hd := depth_control_bound n
  have hp := (scale_bounds n).2.2.2.2.1
  have hg := (dimensions n).2.2.2.1
  have hc := capacity_bound n
  have hlogy := Nat.log_le_self 2 (4*primeWindow n+1)
  have hlogp := Nat.log_le_self 2 (maxMod n+1)
  have hlogU := Nat.log_le_self 2 (U+1)
  unfold LightEncodedColorPrimeCore.space LightPrimePool.space LightBandPrimeChain.space
    LightWeightedScore.space LightModuloCounts.space EncodedColorPrimeData.prefixBase EncodedColorPrimeData.poolBase
  apply max_le
  · omega
  · apply max_le <;> omega

theorem prime_space_bound (free n U : ℕ) :
    LightEncodedColorPrimeHost.inputSpace free n U ≤ free+2000*(scale n)^3+U := by
  have hb := (scale_bounds n).1
  have hnrm := normalized_space_bound free n
  have hprime := prime_address_bound free n
  have hcore := prime_core_space_bound (prime free n (bandSize n)) n U
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  unfold LightEncodedColorPrimeHost.inputSpace
  apply max_le <;> nlinarith only [hb,hnrm,hprime,hcore,hp3]











end ThreeSum.EncodedColorResources

end

section


/-! # Finite space and word bounds for the actual retained source constructors -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open SubsetAddress CostLedger TrimScales

set_option maxHeartbeats 2600000
set_option maxRecDepth 13000



















































theorem source_finish_bound (base n : ℕ) : SourceFiniteCosts.finish base n ≤ base+200*(scale n)^5 := by
  have hb := (scale_bounds n).1
  have hJ := (dimensions n).2.1
  have hstorage := source_storage_le n
  have hfactor : 29+blocks n+SourceBandBanksCosts.storageFactor n ≤ 60*(scale n)^2 := by
    nlinarith only [hb,hJ,hstorage]
  have hmul := Nat.mul_le_mul hfactor (encoder_le n)
  unfold SourceFiniteCosts.finish
  change base+(29+blocks n+SourceBandBanksCosts.storageFactor n)*encoderCount n+17 ≤ _
  have hp5 : scale n ≤ (scale n)^5 := Nat.le_self_pow (by decide) _
  nlinarith only [hmul,hb,hp5]









































































































































end ThreeSum.EncodedColorResources

end

section


/-! # Finite affine resource bounds for balanced wanted records and shared sources -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open KaratsubaInterface

set_option maxHeartbeats 2400000
set_option maxRecDepth 13000


















theorem wanted_space_bound (free n U : ℕ) :
    EncodedColorWantedCosts.space free (maxMod n) (radix n) (half n) (blocks n) U
      (EncodedColorStageCosts.incidenceCap n) ≤ free+200*(scale n)^5+U := by
  have hb := (scale_bounds n).1
  have hlen := incidence_cap_le n
  have hG := totalKeys_le n
  have hM := (dimensions n).2.2.2.2
  have hkey := key_end_bound free n
  have hbound := keyBound_le n
  have hbase := wanted_source_base_bound free n
  have hcover := cover_space_bound free n
  have hcapacity := (capacity_lt_twice (radix_pos n)).le.trans (Nat.mul_le_mul_left 2 hM)
  have hlogU := Nat.log_le_self 2 (U+1)
  have hlogK := Nat.log_le_self 2 (LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n)+1)
  have hlogM := Nat.log_le_self 2 (radix n+radix n+1)
  have hp5 : scale n ≤ (scale n)^5 := Nat.le_self_pow (by decide) _
  have hp25 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 5)
  have hp35 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 5)
  have hp45 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 4 ≤ 5)
  have hpair : LightWantedSetup.pairBase
      (LightGuardedWanted.wantedFree free (half n) (blocks n) (EncodedColorStageCosts.incidenceCap n))
      (3*EncodedColorStageCosts.incidenceCap n) (LightGuardedWanted.totalKeys (half n) (blocks n)) (radix n) ≤
      free+100*(scale n)^5 := by
    unfold EncodedColorWantedCosts.sourceBase at hbase
    omega
  have hlogs : max (Nat.log 2 (LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n)+1)+2)
      (Nat.log 2 (radix n+radix n+1)+2) ≤ 3*(scale n)^4+2*scale n+3 := by omega
  unfold EncodedColorWantedCosts.space
  refine max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))
  · omega
  · unfold LightRawAKeys.space
    omega
  · unfold LightOriginalOffset.space LightGuardedWanted.wantedFree
    nlinarith only [hb,hkey,hlen,hG,hcapacity,hlogK,hbound,hp5,hp25,hp35,hp45]
  · unfold LightSourceResidues.space
    nlinarith only [hb,hpair,hlogs,hp5,hp45]
  · omega






































theorem stage_space_bound (free n U : ℕ) :
    EncodedColorStageCosts.space free n (maxMod n) (radix n) U (EncodedColorStageCosts.incidenceCap n) ≤
      free+300*(scale n)^5+U := by
  have hw := wanted_space_bound free n U
  have hb := wanted_source_base_bound free n
  have hs := source_space_bound (EncodedColorStageCosts.sourceBase free n (radix n)
    (EncodedColorStageCosts.incidenceCap n)) n U
  unfold EncodedColorStageCosts.sourceBase at hs
  dsimp only [half,blocks] at hw hb
  unfold EncodedColorStageCosts.space EncodedColorStageCosts.sourceBase
  apply max_le <;> omega


























end ThreeSum.EncodedColorResources

end

section


/-! # Polynomial Need for the exact closed selected-color pipeline -/

namespace ThreeSum.EncodedColorResources

open Light Scales BandScales ArithmeticStageBounds StageBounds

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

theorem pipeline_space_bound_sourceProof (free n U : ℕ) :
    LightEncodedColorPipeline.space free n U ≤ free+3000*(scale n)^5+U := by
  have hb := (scale_bounds n).1
  have hp5 : scale n ≤ (scale n)^5 := Nat.le_self_pow (by decide) _
  have hp35 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 5)
  have hcover := cover_address_bound free n
  have hprime := prime_space_bound free n U
  have hstage := stage_space_bound (EncodedColorPipelineData.coverBase free n) n U
  have hsource : LightEncodedColorPipeline.sourceBound free n ≤
      EncodedColorPipelineData.coverBase free n+100*(scale n)^5 :=
    wanted_source_base_bound (EncodedColorPipelineData.coverBase free n) n
  have hfinish : LightEncodedColorPipeline.finishBound free n ≤
      LightEncodedColorPipeline.sourceBound free n+200*(scale n)^5 :=
    source_finish_bound (LightEncodedColorPipeline.sourceBound free n) n
  unfold LightEncodedColorPipeline.space
  refine max_le ?_ (max_le ?_ ?_) <;>
    nlinarith only [hb,hp5,hp35,hcover,hprime,hstage,hsource,hfinish]




























































noncomputable section











end
























end ThreeSum.EncodedColorResources

end


theorem solution : ∀ (free n U : Nat),
  @LE.le.{0} Nat instLENat (ThreeSum.LightEncodedColorPipeline.space free n U)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3000) (instOfNatNat (nat_lit 3000)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (ThreeSum.EncodedColorResources.scale n) (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
      U) := by
  exact @ThreeSum.EncodedColorResources.pipeline_space_bound_sourceProof

#print axioms solution
