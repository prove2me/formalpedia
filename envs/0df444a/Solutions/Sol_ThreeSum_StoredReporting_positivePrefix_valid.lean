-- Prove2me | solution 1 for ThreeSum.StoredReporting.positivePrefix_valid
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:21:54.610222+00:00
-- url     : https://prove2.me/submissions/ab31e54d-11fb-4749-8ef5-2af2c1655f75

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.RingTheory.Coprime.Lemmas
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
import Theorems.Thm_ThreeSum_RawReporting_partitionWord_length


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting

section


/-!
# Executable positive-prefix reporting

The routine enumerates children of the current positive frontier and discards
zero counts. Its correctness interface asks for exact natural prefix counts;
the subset-transform identities supply those counts in the application.
No bound on the cost of obtaining a count is assumed or proved here.
-/

namespace ThreeSum.Reporting

open Finset
open scoped BigOperators

variable {ι α : Type*} [DecidableEq α]





theorem mass_pos_iff (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (k : ℕ) (pre : List α) :
    0 < mass I word weight k pre ↔
      ∃ i ∈ I, (word i).take k = pre ∧ 0 < weight i := by
  unfold mass Subset.fiberMass
  rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [mem_filter]
  constructor
  · rintro ⟨i, ⟨hi, hpre⟩, hw⟩
    exact ⟨i, hi, hpre, hw⟩
  · rintro ⟨i, hi, hpre, hw⟩
    exact ⟨i, ⟨hi, hpre⟩, hw⟩






























































































































end ThreeSum.Reporting

end

section


/-!
# Exact stored-subset queries for the concrete reporting tree

A malformed prefix has zero mass. Every valid prefix is evaluated by the
stored suffix-zeta stages and the signed subset formula. These values are
proved to equal the natural raw-incidence fiber counts at every tree node.
-/

namespace ThreeSum.StoredReporting

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding BlockForced





















theorem prefixRows_take {J L k : ℕ} (u : Fin J → Finset (Fin L)) (i : Fin J)
    (hi : i.val < k) : prefixRows ((List.ofFn u).take k) i = u i := by
  simp only [prefixRows, List.getElem?_take_of_lt hi, List.getElem?_ofFn,
    dif_pos i.isLt, Option.getD_some]






























section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem positivePrefix_valid_sourceProof {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512 * h)))) (hk : k ≤ J)
    (hp : 0 < prefixQuery I w k pre) : ValidPrefix w.2.2 k pre := by
  obtain ⟨r, hr, hpre, _⟩ := (Reporting.mass_pos_iff (domain I w) word (fun _ => 1) k pre).mp hp
  have hw := (Finset.mem_filter.mp hr).2
  have hq : tupleOutput r.2.1 = w.2.2 := congrArg (fun w => w.2.2) hw
  constructor
  · rw [← hpre, List.length_take, word, partitionWord_length, Nat.min_eq_left hk]
  · intro i hi
    have hrows : prefixRows pre i = (edge (r.2.1 i)).val.1 := by
      rw [← hpre]
      exact prefixRows_take (fun j => (edge (r.2.1 j)).val.1) i hi
    rw [hrows]
    refine ⟨?_, (edge_data (edge (r.2.1 i))).1⟩
    have he : output (edge (r.2.1 i)) = outputRows w.2.2 i :=
      congrArg (fun q => (q i).2.val) hq
    rw [← he]
    exact Finset.subset_union_left
















































































































end Indices

end ThreeSum.StoredReporting

end

universe u_1 u_2 u_3

theorem solution : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β] [Fintype.{u_3} γ]
  [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {h J k : Nat}
  (I : Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.RawItem.{u_1, u_2, u_3} h J α β γ))
  (w : ThreeSum.RawReporting.Wanted.{u_1} h J α)
  (pre :
    List.{0}
      (Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))),
  @LE.le.{0} Nat instLENat k J →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@ThreeSum.RawReporting.prefixQuery.{u_1, u_2, u_3} α β γ inst h J I w k pre) →
      @ThreeSum.StoredReporting.ValidPrefix h J
        (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (ThreeSum.GlobalEncoding.GlobalOutput h J)
          (@Prod.snd.{u_1, 0} α
            (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput h J))
            w))
        k pre := by
  exact @ThreeSum.StoredReporting.positivePrefix_valid_sourceProof

#print axioms solution
