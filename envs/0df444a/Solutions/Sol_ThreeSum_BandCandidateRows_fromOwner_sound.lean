-- Prove2me | solution 1 for ThreeSum.BandCandidateRows.fromOwner_sound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:37:35.979892+00:00
-- url     : https://prove2.me/submissions/567bc267-c42a-44d3-a09b-ec7018cd60ab

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum_BinarySearch_locate_sound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress

section


/-!
# A closed machine program listing all relevant sorted-band candidates

The program computes its own binary width and power table, then executes
exactly the three rectangular owner tables. Every table cell contains an
interval lookup result (index plus one, zero for a miss). The source arrays
remain intact. The coverage theorem below connects these actual memory cells
to every relevant triple, and hence to every exact equation in the bands.
-/

namespace ThreeSum.LightBandEnumeration

set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}









































































































































































































































































theorem lookup_sound (A : Family) {i : ℕ} {x : ℤ}
    (hr : LightBandLookup.result A.lower A.upper A.size x = i+1) :
    i < A.size ∧ A.lower i ≤ x ∧ x ≤ A.upper i := by
  unfold LightBandLookup.result at hr
  cases h : BinarySearch.locate A.lower A.upper A.size x with
  | none => simp [h] at hr
  | some j =>
      simp only [h,Option.map_some,Option.getD_some] at hr
      have heq : j = i := by omega
      subst j
      exact BinarySearch.locate_sound A.lower A.upper A.size x A.sorted h






















































































end ThreeSum.LightBandEnumeration

end

section


/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows

open BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000





















































































































theorem make_flag_one_iff (mode : Mode) (i j r : ℕ) :
    (make mode i j r).flag=1 ↔ 0 < r := by
  cases mode <;> simp only [make] <;> split_ifs <;> simp_all

theorem fromOwner_sound_sourceProof (A B C : Family) (o : Owner A B C)
    (hf : (fromOwner A B C o).flag=1) :
    let r := fromOwner A B C o
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩
  · have hp := (make_flag_one_iff .bc j.val k.val _).mp hf
    let r := LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j)
    have hr : r=(r-1)+1 := by omega
    have hs := LightBandEnumeration.lookup_sound A (i := r-1) hr
    have hB := B.nonempty j j.isLt
    have hC := C.nonempty k k.isLt
    refine ⟨hs.1,j.isLt,k.isLt,?_⟩
    change A.lower (r-1) ≤ C.upper k-B.lower j ∧ C.lower k-B.upper j ≤ A.upper (r-1)
    omega
  · have hp := (make_flag_one_iff .ab i.val j.val _).mp hf
    let r := LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j)
    have hr : r=(r-1)+1 := by omega
    have hs := LightBandEnumeration.lookup_sound C (i := r-1) hr
    have hA := A.nonempty i i.isLt
    have hB := B.nonempty j j.isLt
    refine ⟨i.isLt,j.isLt,hs.1,?_⟩
    change A.lower i ≤ C.upper (r-1)-B.lower j ∧ C.lower (r-1)-B.upper j ≤ A.upper i
    omega
  · have hp := (make_flag_one_iff .ac i.val k.val _).mp hf
    let r := LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i)
    have hr : r=(r-1)+1 := by omega
    have hs := LightBandEnumeration.lookup_sound B (i := r-1) hr
    have hA := A.nonempty i i.isLt
    have hC := C.nonempty k k.isLt
    refine ⟨i.isLt,hs.1,k.isLt,?_⟩
    change A.lower i ≤ C.upper k-B.lower (r-1) ∧ C.lower k-B.upper (r-1) ≤ A.upper i
    omega


















































end ThreeSum.BandCandidateRows

end


theorem solution : ∀ (A B C : ThreeSum.BandEnumeration.Family) (o : ThreeSum.BandEnumeration.Owner A B C),
  @Eq.{1} Nat (ThreeSum.BandCandidateRows.fromOwner A B C o).flag
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    have r := ThreeSum.BandCandidateRows.fromOwner A B C o;
    And (@LT.lt.{0} Nat instLTNat r.a A.size)
      (And (@LT.lt.{0} Nat instLTNat r.b B.size)
        (And (@LT.lt.{0} Nat instLTNat r.c C.size)
          (@ThreeSum.Bands.Relevant.{0, 0, 0} Nat Nat Nat A.lower A.upper B.lower B.upper C.lower C.upper
            (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat Nat) r.a (@Prod.mk.{0, 0} Nat Nat r.b r.c))))) := by
  exact @ThreeSum.BandCandidateRows.fromOwner_sound_sourceProof

#print axioms solution
