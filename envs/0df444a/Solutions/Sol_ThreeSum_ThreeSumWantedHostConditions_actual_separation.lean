-- Prove2me | solution 1 for ThreeSum.ThreeSumWantedHostConditions.actual_separation
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:15:30.995899+00:00
-- url     : https://prove2.me/submissions/d2a4d621-fd7f-4c21-bfa0-cb58cbc1283a

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle16
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BandRawA_product_values_mem


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales

section


/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000










































@[simp] theorem mem_finiteAllProducts {nA nB nC g : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteAllProducts nA nB nC g rs ↔
      coordinates t ∈ allProducts nA nB nC g rs := by
  simp only [finiteAllProducts,mem_filter,mem_univ,true_and]







































































































end ThreeSum.BandRawA

end

section


/-!
# Exact original-value membership and equation coverage of the owner catalog

Normalized sorted coordinates remain distinct from original input
positions. The normalization membership equivalence transfers values back
to their original color classes; the color-class bridge can then recover
the required distinct original positions.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000























theorem product_original_values {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ allProducts A.length B.length C.length g rs) :
    valueAt A.length g rs (fun i => A.getD i 0) t.1 ∈ originalA ∧
      B.getD t.2.1 0 ∈ originalB ∧ C.getD t.2.2 0 ∈ originalC := by
  obtain ⟨ha,hb,hc⟩ := product_values_mem ht
  exact ⟨(hA _).mp ha,(hB _).mp hb,(hC _).mp hc⟩
































































end ThreeSum.BandRawA

end

section


/-! # Original-value soundness and completeness on the bounded reporting domain -/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset

set_option maxHeartbeats 1200000
set_option maxRecDepth 7000

theorem finite_product_original_values {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List Record}
    {t : Fin (items A.length g rs).length × Fin B.length × Fin C.length}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ finiteAllProducts A.length B.length C.length g rs) :
    valueAt A.length g rs (fun i => A.getD i 0) t.1.val ∈ originalA ∧
      B.getD t.2.1.val 0 ∈ originalB ∧ C.getD t.2.2.val 0 ∈ originalC :=
  product_original_values hA hB hC (mem_finiteAllProducts.mp ht)






























end ThreeSum.BandRawA

end

section


/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter

open Light

set_option maxHeartbeats 1200000

















theorem mem_items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) (z : ℤ) :
    z ∈ items x color want scale n ↔ ∃ i, i < n ∧ color i = want ∧ scale*x i = z := by
  simp [items,and_assoc]





















variable {lim : Limits} {P : Program} {d : ℕ}























































































end ThreeSum.LightClassFilter

end

section


/-!
# Original input to normalized color bands

This fixed program computes index colors, writes the three class arrays and
their headers, then reads those headers into the existing normalization and
owner-table program. All buffers and resource bounds depend on the original
input length, rather than on externally supplied color-class lengths.
-/

namespace ThreeSum.LightColorBands

open Light ColorClassLists

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000













theorem class_bounded {n W U : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) (hs : |scale| ≤ 1) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ∀ z ∈ classList p x c scale, |z| ≤ (U : ℤ) := by
  intro z hz
  obtain ⟨i,hi,_,rfl⟩ :=
    (LightClassFilter.mem_items (value x) (LightColorIndex.color p) c scale n z).mp hz
  have hv : |value x i| ≤ (U : ℤ) := by
    simpa only [value,hi,dite_true] using hx ⟨i,hi⟩
  rw [abs_mul]
  calc
    |scale| * |value x i| ≤ 1 * (U : ℤ) :=
      mul_le_mul hs hv (abs_nonneg _) (by norm_num)
    _ = (U : ℤ) := one_mul _








variable {lim : Limits} {P : Program} {d : ℕ}

























































































































end ThreeSum.LightColorBands

end

section


/-!
# Uniform size conditions and original-color semantics for the wanted consumer

The cutoff is chosen before any memory, color, or original array. The
auxiliary-prime separation premise is proved for the actual generated pool.
-/

namespace ThreeSum.ThreeSumWantedHostConditions

open Light Scales BandScales Filter RawIncidences BandRawA ColorClassLists
open scoped Topology

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000














































theorem actual_separation_sourceProof {μ : ℕ→ℤ} {free n k : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : Ready k n) (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    let rs := sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC
    ∀ t∈finiteAllProducts A.length B.length C.length (bandSize n) rs,
      difference (fun i => valueAt A.length (bandSize n) rs (fun j => A.getD j 0) i.val)
        (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t≠0 →
      ∃ l∈DenseGuard.actualAux n, ¬l∣difference
        (fun i => valueAt A.length (bandSize n) rs (fun j => A.getD j 0) i.val)
        (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t := by
  dsimp only
  intro t ht hz
  apply hn.separates _ hz
  obtain ⟨ha,hb,hc⟩ := finite_product_original_values
    H.normalized.2.1.2.2.1 H.normalized.2.2.1.2.2.1 H.normalized.2.2.2.1.2.2.1 ht
  have haBound := LightColorBands.class_bounded color x 0 1 (by norm_num) hx _ ha
  have hbBound := LightColorBands.class_bounded color x 1 1 (by norm_num) hx _ hb
  have hcBound := LightColorBands.class_bounded color x 2 (-1) (by norm_num) hx _ hc
  have hdiff : |difference
      (fun i => valueAt A.length (bandSize n)
        (sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC) (fun j => A.getD j 0) i.val)
      (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t|≤((3*n^k : ℕ) : ℤ) := by
    unfold difference
    have hfirst := abs_sub_le (C.getD t.2.2.val 0) 0 (B.getD t.2.1.val 0)
    have hlast := abs_sub_le (C.getD t.2.2.val 0-B.getD t.2.1.val 0) 0
      (valueAt A.length (bandSize n)
        (sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC) (fun j => A.getD j 0) t.1.val)
    simp only [sub_zero,zero_sub,abs_neg] at hfirst hlast
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    omega
  exact_mod_cast (show ((difference
      (fun i => valueAt A.length (bandSize n)
        (sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC) (fun j => A.getD j 0) i.val)
      (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t).natAbs : ℤ)≤((3*n^k : ℕ) : ℤ) by
    simpa only [Int.natCast_natAbs] using hdiff)

end ThreeSum.ThreeSumWantedHostConditions

end


theorem solution : ∀ {μ : Nat → Int} {free n k : Nat}
  {color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {x : Fin n → Int} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C},
  ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC →
    ThreeSum.ThreeSumWantedHostConditions.Ready k n →
      (∀ (i : Fin n),
          @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
            (@Nat.cast.{0} Int instNatCastInt
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) n k))) →
        have rs :=
          ThreeSum.BandRawA.sortedRecords A B C (ThreeSum.BandScales.bandSize n) (ThreeSum.BandScales.bandSize_pos n)
            hsA hsB hsC;
        ∀
          (t :
            Prod.{0, 0}
              (Fin
                (@List.length.{0} ThreeSum.BandRawA.Label
                  (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
              (Prod.{0, 0} (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C)))),
          @Membership.mem.{0, 0}
              (Prod.{0, 0}
                (Fin
                  (@List.length.{0} ThreeSum.BandRawA.Label
                    (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
                (Prod.{0, 0} (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C))))
              (Finset.{0}
                (Prod.{0, 0}
                  (Fin
                    (@List.length.{0} ThreeSum.BandRawA.Label
                      (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
                  (Prod.{0, 0} (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C)))))
              (@SetLike.instMembership.{0, 0}
                (Finset.{0}
                  (Prod.{0, 0}
                    (Fin
                      (@List.length.{0} ThreeSum.BandRawA.Label
                        (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
                    (Prod.{0, 0} (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C)))))
                (Prod.{0, 0}
                  (Fin
                    (@List.length.{0} ThreeSum.BandRawA.Label
                      (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
                  (Prod.{0, 0} (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C))))
                (@Finset.instSetLike.{0}
                  (Prod.{0, 0}
                    (Fin
                      (@List.length.{0} ThreeSum.BandRawA.Label
                        (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
                    (Prod.{0, 0} (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C))))))
              (ThreeSum.BandRawA.finiteAllProducts (@List.length.{0} Int A) (@List.length.{0} Int B)
                (@List.length.{0} Int C) (ThreeSum.BandScales.bandSize n) rs)
              t →
            @Ne.{1} Int
                (@ThreeSum.RawIncidences.difference.{0, 0, 0}
                  (Fin
                    (@List.length.{0} ThreeSum.BandRawA.Label
                      (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
                  (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C))
                  (fun
                      (i :
                        Fin
                          (@List.length.{0} ThreeSum.BandRawA.Label
                            (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs))) =>
                    ThreeSum.BandRawA.valueAt (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs
                      (fun (j : Nat) =>
                        @List.getD.{0} Int A j (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                      (@Fin.val
                        (@List.length.{0} ThreeSum.BandRawA.Label
                          (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs))
                        i))
                  (fun (i : Fin (@List.length.{0} Int B)) =>
                    @List.getD.{0} Int B (@Fin.val (@List.length.{0} Int B) i)
                      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                  (fun (i : Fin (@List.length.{0} Int C)) =>
                    @List.getD.{0} Int C (@Fin.val (@List.length.{0} Int C) i)
                      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                  t)
                (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
              ∃ (l : Int),
                And
                  (@Membership.mem.{0, 0} Int (Finset.{0} Int)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
                    (ThreeSum.DenseGuard.actualAux n) l)
                  (Not
                    (@Dvd.dvd.{0} Int Int.instDvd l
                      (@ThreeSum.RawIncidences.difference.{0, 0, 0}
                        (Fin
                          (@List.length.{0} ThreeSum.BandRawA.Label
                            (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs)))
                        (Fin (@List.length.{0} Int B)) (Fin (@List.length.{0} Int C))
                        (fun
                            (i :
                              Fin
                                (@List.length.{0} ThreeSum.BandRawA.Label
                                  (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n)
                                    rs))) =>
                          ThreeSum.BandRawA.valueAt (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs
                            (fun (j : Nat) =>
                              @List.getD.{0} Int A j (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                            (@Fin.val
                              (@List.length.{0} ThreeSum.BandRawA.Label
                                (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n) rs))
                              i))
                        (fun (i : Fin (@List.length.{0} Int B)) =>
                          @List.getD.{0} Int B (@Fin.val (@List.length.{0} Int B) i)
                            (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                        (fun (i : Fin (@List.length.{0} Int C)) =>
                          @List.getD.{0} Int C (@Fin.val (@List.length.{0} Int C) i)
                            (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                        t))) := by
  exact @ThreeSum.ThreeSumWantedHostConditions.actual_separation_sourceProof

#print axioms solution
