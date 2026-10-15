-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_map
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:21:57.544958+00:00
-- url     : https://prove2.me/submissions/b6b1c405-cf73-4983-9e94-806c414ed5c7

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverSchedule_target_injective
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LocalCoverMatrix_entry_eq_one_iff
import Theorems.Thm_ThreeSum_LightLocalCoverTransport_choices_map
import Theorems.Thm_ThreeSum_WeightEnumeration_coordinates_idxOf
import Theorems.Thm_ThreeSum_WeightEnumeration_decode_eq_digit
import Theorems.Thm_ThreeSum_WeightEnumeration_pi_eq_range

namespace Finset
end Finset
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalCoverMatrix
end ThreeSum.LocalCoverMatrix
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.WeightEnumeration
end ThreeSum.WeightEnumeration
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix
end ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
end ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
end ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
namespace ThreeSum1960614.Machine.ThreeSum.WeightEnumeration
end ThreeSum1960614.Machine.ThreeSum.WeightEnumeration

namespace ThreeSum1960614.Machine

/-!
# The literal cover-matrix entry is the retained-edge predicate

This identifies the actual all-pairs, histogram-trimmed support table with
the same `Covers` relation used by the finite moment and greedy proof.
-/

namespace ThreeSum.LocalCoverMatrix
open _root_.ThreeSum.LocalCoverMatrix


open _root_.Finset
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes

variable {h L k : ℕ}










theorem radix_div {p a b : ℕ} (hb : b < p) : (a*p+b)/p=a := by
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hb]
  omega

theorem radix_mod {p a b : ℕ} (hb : b < p) : (a*p+b)%p=b := by
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hb]









end ThreeSum.LocalCoverMatrix

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Ordered radix enumeration of local hash coefficients

The Cartesian-product list used by `allWeights` enumerates the first
coordinate most slowly. The radix index consequently stores that coordinate
in its most significant digit. The equality below is equality of lists,
including their order and repetitions, rather than a membership equivalence.
-/

namespace ThreeSum.WeightEnumeration
open _root_.ThreeSum.WeightEnumeration


open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments

variable {ι K : Type*} [DecidableEq ι] [NatCast K]















theorem coordinates_succ (L : ℕ) :
    _root_.ThreeSum.LocalHashMoments.coordinates (L+1) = (0,false)::(0,true)::(_root_.ThreeSum.LocalHashMoments.coordinates L).map _root_.ThreeSum.WeightEnumeration.liftCoordinate := by
  simp only [_root_.ThreeSum.LocalHashMoments.coordinates,List.finRange_succ,List.flatMap_cons,List.flatMap_map,
    List.map_flatMap,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    _root_.ThreeSum.WeightEnumeration.liftCoordinate]

theorem coordinates_length (L : ℕ) : (_root_.ThreeSum.LocalHashMoments.coordinates L).length = 2*L := by
  induction L with
  | zero => simp [_root_.ThreeSum.LocalHashMoments.coordinates]
  | succ L ih =>
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.WeightEnumeration.coordinates_succ]
    simp only [List.length_cons,List.length_map,ih]
    omega













/-- Exact ordered equality, preserving the occurrence indices used by the
greedy schedule and global hash encoding. -/
theorem allWeights_eq_range (L p : ℕ) :
    _root_.ThreeSum.LocalHashMoments.allWeights L ((List.range p).map (fun n : ℕ => (n : K))) =
      (List.range (p^(2*L))).map (_root_.ThreeSum.WeightEnumeration.decodedWeight (K := K) L p) := by
  unfold _root_.ThreeSum.LocalHashMoments.allWeights
  rw [_root_.ThreeSum.WeightEnumeration.pi_eq_range,List.map_map,_root_.ThreeSum1960614.Machine.ThreeSum.WeightEnumeration.coordinates_length]
  apply List.map_congr_left
  intro k hk
  funext i
  have hidx := _root_.ThreeSum.WeightEnumeration.coordinates_idxOf i
  simp only [List.idxOf,Bool.beq_eq_decide_eq] at hidx
  simp only [Function.comp_apply,_root_.ThreeSum.WeightEnumeration.decode_eq_digit,_root_.ThreeSum1960614.Machine.ThreeSum.WeightEnumeration.coordinates_length,
    _root_.ThreeSum.WeightEnumeration.decodedWeight,_root_.ThreeSum.WeightEnumeration.digit,List.idxOf,Bool.beq_eq_decide_eq,hidx]











theorem localWeights_eq_range (h : ℕ) :
    _root_.ThreeSum.LocalHashMoments.allWeights (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localValues h) =
      (List.range ((_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)^(2*(464*h)))).map
        (_root_.ThreeSum.WeightEnumeration.decodedWeight (K := _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)) := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum.WeightEnumeration.allWeights_eq_range _ _

/-- Rewriting the schedule preserves its precise tie rule and every chosen
map occurrence because the candidate lists are equal in order. -/
theorem localSchedule_eq_radix (h : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule h =
      _root_.ThreeSum.Cover.greedyChoices
        ((List.range ((_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)^(2*(464*h)))).map
          (_root_.ThreeSum.WeightEnumeration.decodedWeight (K := _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)))
        (_root_.ThreeSum.LocalHashMoments.Covers (464*h) h (_root_.ThreeSum.LocalHashMoments.bucketBound (464*h) h (Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h))))
        (Finset.univ : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h × _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h))
        (_root_.ThreeSum.LocalHashMoments.scheduleLength h (Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h))) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule _root_.ThreeSum.LocalHashMoments.schedule
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.WeightEnumeration.localWeights_eq_range]

end ThreeSum.WeightEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact local schedule occurrence indices

The machine's Boolean matrix uses radix-indexed candidate rows and ordered
residue-pair columns. These changes of representation preserve the entire
original local schedule, including ties and repeated selected maps.
-/

namespace ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum.LightLocalCoverSchedule


open _root_.Finset
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding








theorem rows_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h := Nat.pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h)



theorem target_surjective (h : ℕ) (u : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h × _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) :
    ∃ r < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.target h r = u := by
  obtain ⟨a,b⟩ := u
  have ha := a.val_lt
  have hb := b.val_lt
  refine ⟨a.val*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+b.val,?_,?_⟩
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols
    nlinarith
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.target
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.radix_div hb,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.radix_mod hb]
    simp only [ZMod.natCast_zmod_val]

theorem target_image (h : ℕ) : (range (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h)).image (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.target h) = univ := by
  ext u
  simp only [mem_univ,iff_true]
  obtain ⟨r,hr,he⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.target_surjective h u
  exact mem_image.mpr ⟨r,mem_range.mpr hr,he⟩

theorem matrix_covers (h i : ℕ) {r : ℕ} (hr : r < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h) :
    _root_.ThreeSum.BooleanGreedy.covers (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.matrix h) i r ↔
      _root_.ThreeSum.LocalHashMoments.Covers (464*h) h (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h i) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.target h r) := by
  have hq := (Nat.div_lt_iff_lt_mul (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h)).mpr hr
  have hm := Nat.mod_lt r (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h)
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.entry_eq_one_iff (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h i) (k := h) (B := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) hq hm
  have hidx : r/_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+r%_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h=r := by
    simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div r (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
  rw [hidx] at he
  exact he



















end ThreeSum.LightLocalCoverSchedule

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule

open _root_.Finset
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
section

theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_map__implementation_2847ac675f (h : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).map (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h) = _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule h := by
  have hc : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h = _root_.ThreeSum.WeightEnumeration.decodedWeight (K := _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) := by
    funext i
    rfl
  have ht := _root_.ThreeSum.LightLocalCoverTransport.choices_map (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.matrix h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.target h)
    (_root_.ThreeSum.LocalHashMoments.Covers (464*h) h (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h)) (rows := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (cols := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows_pos h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.target_injective h) (fun i _ hr => _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.matrix_covers h i hr) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.target_image] at ht
  rw [hc] at ht ⊢
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.WeightEnumeration.localSchedule_eq_radix]
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap,_root_.ThreeSum.LocalHashMoments.bucketBound] at ht ⊢
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize,ZMod.card] at ht ⊢
  convert ht using 1
  congr 1
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_map__implementation_2847ac675f) := (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_map__implementation_2847ac675f)

#print axioms solution
