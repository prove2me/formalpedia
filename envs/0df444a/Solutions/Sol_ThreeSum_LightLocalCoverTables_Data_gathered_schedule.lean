-- Prove2me | solution 1 for ThreeSum.LightLocalCoverTables.Data.gathered_schedule
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:16:21.148976+00:00
-- url     : https://prove2.me/submissions/53ccab3f-cd84-48c5-9610-286f737dc1b2

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
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_indices_lt
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_indices_map


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask

open Finset SubsetAddress LocalHashMoments
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

























































@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    extend f i.val = f i := by simp [extend, i.isLt]









































end ThreeSum.OneHotMask

end

section


/-!
# Reading constructed block coefficients in the flat mask order

The imperative coefficient constructor writes rows. The mask evaluator reads
one flat array. These lemmas identify the two layouts, including empty ground
sets, and specialize them to the unchanged schedule-occurrence encoding.
-/

namespace ThreeSum.BlockCoefficientRows

open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds


















































@[simp] theorem mapRow_fin {h : ℕ} (b : Bool) (s : Occurrence h) (i : Fin (512*h)) :
    mapRow h b s.val i.val = (mapAt h s (i,b)).val := by
  simp only [mapRow,s.isLt,dite_true,OneHotMask.extend_fin]




































end ThreeSum.BlockCoefficientRows

end

section


/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy

open Finset
open scoped BigOperators











































































































theorem choices_length (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    (choices matrix rows cols t).length = t := Cover.greedyChoices_length ..




end ThreeSum.BooleanGreedy

end

section


/-!
# Ordered radix enumeration of local hash coefficients

The Cartesian-product list used by `allWeights` enumerates the first
coordinate most slowly. The radix index consequently stores that coordinate
in its most significant digit. The equality below is equality of lists,
including their order and repetitions, rather than a membership equivalence.
-/

namespace ThreeSum.WeightEnumeration

open LocalHashMoments

variable {ι K : Type*} [DecidableEq ι] [NatCast K]





























































































































































theorem decodedWeight_val (L p k : ℕ) (i : Fin L × Bool) :
    (decodedWeight (K := ZMod p) L p k i).val = digit p (2*L) k (coordinateIndex i) := by
  simp [decodedWeight,digit,ZMod.val_natCast]































end ThreeSum.WeightEnumeration

end

section


/-!
# Exact local schedule occurrence indices

The machine's Boolean matrix uses radix-indexed candidate rows and ordered
residue-pair columns. These changes of representation preserve the entire
original local schedule, including ties and repeated selected maps.
-/

namespace ThreeSum.LightLocalCoverSchedule

open Finset LocalHashMoments LocalCoverBounds GlobalEncoding











































































theorem indices_length (h : ℕ) : (indices h).length = scheduleSize h :=
  BooleanGreedy.choices_length ..
















theorem candidateAt_lt (h : ℕ) (s : Occurrence h) : candidateAt h s < rows h := by
  have hs : s.val < (indices h).length := by rw [indices_length]; exact s.isLt
  unfold candidateAt
  rw [List.getD_eq_getElem _ _ hs]
  exact indices_lt h (List.getElem_mem hs)

theorem candidateAt_mapAt (h : ℕ) (s : Occurrence h) :
    candidate h (candidateAt h s) = mapAt h s := by
  have hs : s.val < (indices h).length := by rw [indices_length]; exact s.isLt
  have hs' : s.val < (localSchedule h).length := by
    rw [← scheduleSize_eq_length]
    exact s.isLt
  have he := congrArg (fun xs : List (Weight (512*h) (LocalField h)) => xs.getD s.val default) (indices_map h)
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hs),List.getElem_map,
    List.getD_eq_getElem _ _ hs'] at he
  unfold candidateAt mapAt
  rw [List.getD_eq_getElem _ _ hs]
  exact he





































end ThreeSum.LightLocalCoverSchedule

end

section


/-!
# Actual decoding of the unchanged ordered hash-weight enumeration

The five-procedure program constructs its own power table, then decodes
the even and odd coordinates into two contiguous coefficient rows. The
digits are exactly those of `WeightEnumeration.decodedWeight`, which is
already proved equal to the original `allWeights` enumeration in order.
-/

namespace ThreeSum.LightWeightDecode

open Light


























variable {lim : Limits} {P : Program} {d : ℕ}




















































































theorem Rows.decodedWeight {μ : ℕ → ℤ} {dst L p k : ℕ}
    (hrows : Rows μ dst L p k) (i : Fin L) :
    μ (dst+i.val) = ((WeightEnumeration.decodedWeight (K := ZMod p) L p k (i,false)).val : ℤ) ∧
    μ (dst+L+i.val) = ((WeightEnumeration.decodedWeight (K := ZMod p) L p k (i,true)).val : ℤ) := by
  simpa only [WeightEnumeration.decodedWeight_val,WeightEnumeration.coordinateIndex,
    Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using hrows i.val i.isLt





end ThreeSum.LightWeightDecode

end

section


/-!
# Exact semantic interfaces for constructed local-cover tables

The concrete matrix constructor uses the unchanged radix enumeration of
the original local maps. Its retained histograms and gathered coefficient
rows are identified with the original occurrence-indexed encoding.
-/

namespace ThreeSum.LightLocalCoverTables

open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule






































































theorem Data.gathered_schedule_sourceProof {μ ν : ℕ → ℤ} {h maps hist0 hist1 matrixPtr dst : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr)
    (hcopy : ∀ s < scheduleSize h, ∀ a < 2*(512*h),
      ν (dst+s*(2*(512*h))+a) = μ (maps+(indices h).getD s 0*(2*(512*h))+a)) :
    ScheduleRows ν h dst := by
  intro s hs i hi
  let o : Occurrence h := ⟨s,hs⟩
  have hc := ((H (candidateAt h o) (candidateAt_lt h o)).1).decodedWeight ⟨i,hi⟩
  change
    μ (maps+candidateAt h o*(2*(512*h))+i) = ((candidate h (candidateAt h o) (⟨i,hi⟩,false)).val : ℤ) ∧
    μ (maps+candidateAt h o*(2*(512*h))+512*h+i) = ((candidate h (candidateAt h o) (⟨i,hi⟩,true)).val : ℤ) at hc
  rw [candidateAt_mapAt h o] at hc
  rw [BlockCoefficientRows.mapRow_fin false o ⟨i,hi⟩,
    BlockCoefficientRows.mapRow_fin true o ⟨i,hi⟩]
  constructor
  · rw [hcopy s hs i (by omega)]
    exact hc.1
  · have he := hcopy s hs (512*h+i) (by omega)
    rw [← Nat.add_assoc,← Nat.add_assoc] at he
    rw [he]
    exact hc.2

end ThreeSum.LightLocalCoverTables

end


theorem solution : ∀ {μ ν : Nat → Int} {h maps hist0 hist1 matrixPtr dst : Nat},
  ThreeSum.LightLocalCoverTables.Data μ h maps hist0 hist1 matrixPtr →
    (∀ (s : Nat),
        @LT.lt.{0} Nat instLTNat s (ThreeSum.GlobalEncoding.scheduleSize h) →
          ∀ (a : Nat),
            @LT.lt.{0} Nat instLTNat a
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) →
              @Eq.{1} Int
                (ν
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) s
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                    a))
                (μ
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@List.getD.{0} Nat (ThreeSum.LightLocalCoverSchedule.indices h) s
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                    a))) →
      ThreeSum.LightLocalCoverTables.ScheduleRows ν h dst := by
  exact @ThreeSum.LightLocalCoverTables.Data.gathered_schedule_sourceProof

#print axioms solution
