-- Prove2me | solution 1 for ThreeSum.LightLocalCoverSchedule.indices_map
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:05:16.334184+00:00
-- url     : https://prove2.me/submissions/38ecda72-c3d4-41c8-b336-b30e8dd449c9

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_target_injective
import Theorems.Thm_ThreeSum_LightLocalCoverTransport_choices_map
import Theorems.Thm_ThreeSum_LocalCoverMatrix_entry_eq_one_iff
import Theorems.Thm_ThreeSum_WeightEnumeration_coordinates_idxOf
import Theorems.Thm_ThreeSum_WeightEnumeration_decode_eq_digit
import Theorems.Thm_ThreeSum_WeightEnumeration_pi_eq_range


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.LocalMaskHashes
end ThreeSum.LocalMaskHashes

section


/-!
# The literal cover-matrix entry is the retained-edge predicate

This identifies the actual all-pairs, histogram-trimmed support table with
the same `Covers` relation used by the finite moment and greedy proof.
-/

namespace ThreeSum.LocalCoverMatrix

open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes

variable {h L k : ℕ}




















theorem radix_div {p a b : ℕ} (hb : b < p) : (a*p+b)/p=a := by
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hb]
  omega

theorem radix_mod {p a b : ℕ} (hb : b < p) : (a*p+b)%p=b := by
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hb]





























































































end ThreeSum.LocalCoverMatrix

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










































































theorem coordinates_succ (L : ℕ) :
    coordinates (L+1) = (0,false)::(0,true)::(coordinates L).map liftCoordinate := by
  simp only [coordinates,List.finRange_succ,List.flatMap_cons,List.flatMap_map,
    List.map_flatMap,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    liftCoordinate]

theorem coordinates_length (L : ℕ) : (coordinates L).length = 2*L := by
  induction L with
  | zero => simp [coordinates]
  | succ L ih =>
    rw [coordinates_succ]
    simp only [List.length_cons,List.length_map,ih]
    omega
















































/-- Exact ordered equality, preserving the occurrence indices used by the
greedy schedule and global hash encoding. -/
theorem allWeights_eq_range (L p : ℕ) :
    allWeights L ((List.range p).map (fun n : ℕ => (n : K))) =
      (List.range (p^(2*L))).map (decodedWeight (K := K) L p) := by
  unfold allWeights
  rw [pi_eq_range,List.map_map,coordinates_length]
  apply List.map_congr_left
  intro k hk
  funext i
  have hidx := coordinates_idxOf i
  simp only [List.idxOf,Bool.beq_eq_decide_eq] at hidx
  simp only [Function.comp_apply,decode_eq_digit,coordinates_length,
    decodedWeight,digit,List.idxOf,Bool.beq_eq_decide_eq,hidx]























theorem localWeights_eq_range (h : ℕ) :
    allWeights (512*h) (localValues h) =
      (List.range ((LocalCoverBounds.localPrime h)^(2*(512*h)))).map
        (decodedWeight (K := LocalField h) (512*h) (LocalCoverBounds.localPrime h)) := by
  exact allWeights_eq_range _ _

/-- Rewriting the schedule preserves its precise tie rule and every chosen
map occurrence because the candidate lists are equal in order. -/
theorem localSchedule_eq_radix (h : ℕ) :
    localSchedule h =
      Cover.greedyChoices
        ((List.range ((LocalCoverBounds.localPrime h)^(2*(512*h)))).map
          (decodedWeight (K := LocalField h) (512*h) (LocalCoverBounds.localPrime h)))
        (Covers (512*h) h (bucketBound (512*h) h (Fintype.card (LocalField h))))
        (Finset.univ : Finset (LocalField h × LocalField h))
        (scheduleLength h (Fintype.card (LocalField h))) := by
  unfold localSchedule schedule
  rw [localWeights_eq_range]

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












theorem rows_pos (h : ℕ) : 0 < rows h := Nat.pow_pos (localPrime_pos h)


















theorem target_surjective (h : ℕ) (u : LocalField h × LocalField h) :
    ∃ r < cols h, target h r = u := by
  obtain ⟨a,b⟩ := u
  have ha := a.val_lt
  have hb := b.val_lt
  refine ⟨a.val*localPrime h+b.val,?_,?_⟩
  · unfold cols
    nlinarith
  · unfold target
    rw [LocalCoverMatrix.radix_div hb,LocalCoverMatrix.radix_mod hb]
    simp only [ZMod.natCast_zmod_val]

theorem target_image (h : ℕ) : (range (cols h)).image (target h) = univ := by
  ext u
  simp only [mem_univ,iff_true]
  obtain ⟨r,hr,he⟩ := target_surjective h u
  exact mem_image.mpr ⟨r,mem_range.mpr hr,he⟩

theorem matrix_covers (h i : ℕ) {r : ℕ} (hr : r < cols h) :
    BooleanGreedy.covers (matrix h) i r ↔
      Covers (512*h) h (localBucketCap h) (candidate h i) (target h r) := by
  have hq := (Nat.div_lt_iff_lt_mul (localPrime_pos h)).mpr hr
  have hm := Nat.mod_lt r (localPrime_pos h)
  have he := LocalCoverMatrix.entry_eq_one_iff (candidate h i) (k := h) (B := localBucketCap h) hq hm
  have hidx : r/localPrime h*localPrime h+r%localPrime h=r := by
    simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div r (localPrime h)
  rw [hidx] at he
  exact he

theorem indices_map_sourceProof (h : ℕ) : (indices h).map (candidate h) = localSchedule h := by
  have hc : candidate h = WeightEnumeration.decodedWeight (K := LocalField h) (512*h) (localPrime h) := by
    funext i
    rfl
  have ht := LightLocalCoverTransport.choices_map (matrix h) (candidate h) (target h)
    (Covers (512*h) h (localBucketCap h)) (rows := rows h) (cols := cols h)
    (rows_pos h) (target_injective h) (fun i _ hr => matrix_covers h i hr) (scheduleSize h)
  rw [target_image] at ht
  rw [hc] at ht ⊢
  rw [WeightEnumeration.localSchedule_eq_radix]
  dsimp only [localBucketCap,bucketBound] at ht ⊢
  simp only [indices,rows,scheduleSize,ZMod.card] at ht ⊢
  convert ht using 1
  congr 1










































































end ThreeSum.LightLocalCoverSchedule

end


theorem solution : ∀ (h : Nat),
  @Eq.{1}
    (List.{0}
      (ThreeSum.LocalHashMoments.Weight.{0}
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
        (ThreeSum.LocalHashMoments.LocalField h)))
    (@List.map.{0, 0} Nat
      (ThreeSum.LocalHashMoments.Weight.{0}
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
        (ThreeSum.LocalHashMoments.LocalField h))
      (ThreeSum.LightLocalCoverSchedule.candidate h) (ThreeSum.LightLocalCoverSchedule.indices h))
    (ThreeSum.LocalHashMoments.localSchedule h) := by
  exact @ThreeSum.LightLocalCoverSchedule.indices_map_sourceProof

#print axioms solution
