-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.actual_separation
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:04:50.419644+00:00
-- url     : https://prove2.me/submissions/d04d03f7-fc79-4dd1-96a6-ced95fe6d115

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle036
import Definitions.Def_ThreeSum1960614_Machine_Bundle037
import Definitions.Def_ThreeSum1960614_Machine_Bundle038
import Definitions.Def_ThreeSum1960614_Machine_Bundle039
import Definitions.Def_ThreeSum1960614_Machine_Bundle040
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
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
import Definitions.Def_ThreeSum1962Source_Bundle18
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
import Theorems.Thm_ThreeSum_BandRawA_product_values_mem

namespace Filter
end Filter
namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightColorBands
end ThreeSum.LightColorBands
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.ThreeSumWantedHostConditions
end ThreeSum.ThreeSumWantedHostConditions
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightColorBands
end ThreeSum1960614.Machine.ThreeSum.LightColorBands
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions

namespace ThreeSum1960614.Machine

/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000



















@[simp] theorem mem_finiteAllProducts {nA nB nC g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    {t : Fin (_root_.ThreeSum.BandRawA.items nA g rs).length × Fin nB × Fin nC} :
    t ∈ _root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs ↔
      _root_.ThreeSum.BandRawA.coordinates t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs := by
  simp only [_root_.ThreeSum.BandRawA.finiteAllProducts,mem_filter,mem_univ,true_and]























end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original-value membership and equation coverage of the owner catalog

Normalized sorted coordinates remain distinct from original input
positions. The normalization membership equivalence transfers values back
to their original color classes; the color-class bridge can then recover
the required distinct original positions.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000





theorem product_original_values {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {t : ℕ × ℕ × ℕ}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ _root_.ThreeSum.BandRawA.allProducts A.length B.length C.length g rs) :
    _root_.ThreeSum.BandRawA.valueAt A.length g rs (fun i => A.getD i 0) t.1 ∈ originalA ∧
      B.getD t.2.1 0 ∈ originalB ∧ C.getD t.2.2 0 ∈ originalC := by
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum.BandRawA.product_values_mem ht
  exact ⟨(hA _).mp ha,(hB _).mp hb,(hC _).mp hc⟩







end ThreeSum.BandRawA

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









theorem mem_items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) (z : ℤ) :
    z ∈ _root_.ThreeSum.LightClassFilter.items x color want scale n ↔ ∃ i, i < n ∧ color i = want ∧ scale*x i = z := by
  simp [_root_.ThreeSum.LightClassFilter.items,and_assoc]









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightClassFilter

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Original-value soundness and completeness on the bounded reporting domain -/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset

set_option maxHeartbeats 1200000
set_option maxRecDepth 7000

theorem finite_product_original_values {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    {t : Fin (_root_.ThreeSum.BandRawA.items A.length g rs).length × Fin B.length × Fin C.length}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ _root_.ThreeSum.BandRawA.finiteAllProducts A.length B.length C.length g rs) :
    _root_.ThreeSum.BandRawA.valueAt A.length g rs (fun i => A.getD i 0) t.1.val ∈ originalA ∧
      B.getD t.2.1.val 0 ∈ originalB ∧ C.getD t.2.2.val 0 ∈ originalC :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.product_original_values hA hB hC (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_finiteAllProducts.mp ht)





end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original input to normalized color bands

This fixed program computes index colors, writes the three class arrays and
their headers, then reads those headers into the existing normalization and
owner-table program. All buffers and resource bounds depend on the original
input length, rather than on externally supplied color-class lengths.
-/

namespace ThreeSum.LightColorBands
open _root_.ThreeSum.LightColorBands


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000








theorem class_bounded {n W U : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) (hs : |scale| ≤ 1) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ∀ z ∈ _root_.ThreeSum.ColorClassLists.classList p x c scale, |z| ≤ (U : ℤ) := by
  intro z hz
  obtain ⟨i,hi,_,rfl⟩ :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.mem_items (_root_.ThreeSum.ColorClassLists.value x) (_root_.ThreeSum.LightColorIndex.color p) c scale n z).mp hz
  have hv : |_root_.ThreeSum.ColorClassLists.value x i| ≤ (U : ℤ) := by
    simpa only [_root_.ThreeSum.ColorClassLists.value,hi,dite_true] using hx ⟨i,hi⟩
  rw [abs_mul]
  calc
    |scale| * |_root_.ThreeSum.ColorClassLists.value x i| ≤ 1 * (U : ℤ) :=
      mul_le_mul hs hv (abs_nonneg _) (by norm_num)
    _ = (U : ℤ) := one_mul _



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













end ThreeSum.LightColorBands

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.Filter
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open scoped _root_.Topology
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000
section

theorem ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.actual_separation__implementation_fa0a3b449f {μ : ℕ→ℤ} {free n k : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.Ready k n) (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    let rs := _root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC
    ∀ t∈_root_.ThreeSum.BandRawA.finiteAllProducts A.length B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs,
      _root_.ThreeSum.RawIncidences.difference (fun i => _root_.ThreeSum.BandRawA.valueAt A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs (fun j => A.getD j 0) i.val)
        (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t≠0 →
      ∃ l∈_root_.ThreeSum.DenseGuard.actualAux n, ¬l∣ _root_.ThreeSum.RawIncidences.difference
        (fun i => _root_.ThreeSum.BandRawA.valueAt A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs (fun j => A.getD j 0) i.val)
        (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t := by
  dsimp only
  intro t ht hz
  apply hn.separates _ hz
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.finite_product_original_values
    H.normalized.2.1.2.2.1 H.normalized.2.2.1.2.2.1 H.normalized.2.2.2.1.2.2.1 ht
  have haBound := _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded color x 0 1 (by norm_num) hx _ ha
  have hbBound := _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded color x 1 1 (by norm_num) hx _ hb
  have hcBound := _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded color x 2 (-1) (by norm_num) hx _ hc
  have hdiff : |_root_.ThreeSum.RawIncidences.difference
      (fun i => _root_.ThreeSum.BandRawA.valueAt A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
        (_root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC) (fun j => A.getD j 0) i.val)
      (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t|≤((3*n^k : ℕ) : ℤ) := by
    unfold _root_.ThreeSum.RawIncidences.difference
    have hfirst := abs_sub_le (C.getD t.2.2.val 0) 0 (B.getD t.2.1.val 0)
    have hlast := abs_sub_le (C.getD t.2.2.val 0-B.getD t.2.1.val 0) 0
      (_root_.ThreeSum.BandRawA.valueAt A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
        (_root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC) (fun j => A.getD j 0) t.1.val)
    simp only [sub_zero,zero_sub,abs_neg] at hfirst hlast
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    omega
  exact_mod_cast (show ((_root_.ThreeSum.RawIncidences.difference
      (fun i => _root_.ThreeSum.BandRawA.valueAt A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
        (_root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC) (fun j => A.getD j 0) i.val)
      (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t).natAbs : ℤ)≤((3*n^k : ℕ) : ℤ) by
    simpa only [Int.natCast_natAbs] using hdiff)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.actual_separation__implementation_fa0a3b449f) := (@ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.actual_separation__implementation_fa0a3b449f)

#print axioms solution
