-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.prefixQuery_eq_bucketPrefixMass
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:13:55.183268+00:00
-- url     : https://prove2.me/submissions/c019d730-6ec5-495c-a38f-20413bdce98b

import Aesop
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
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
import Theorems.Thm_ThreeSum_Radix_mem_representations

namespace Finset
end Finset
namespace ThreeSum
end ThreeSum
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting

namespace ThreeSum1960614.Machine

/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalEncoding


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments




















































theorem mem_representations (h J : ℕ) (a b : ℤ) (xs : List (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)) :
    xs ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J a b ↔ xs.length = J ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ a - _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft xs ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ b - _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight xs := by
  exact _root_.ThreeSum.Radix.mem_representations (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
    (by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h).ne') _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight J a b xs







































end ThreeSum.GlobalEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-index incidences in the guarded global encoding

An incidence retains its original input indices, its complete sequence of
chosen-map occurrences and retained local edges, and its signed arithmetic
lift. Equal input values remain distinct original indices. The lift is
unique for a fixed original triple and representation, so it does not add
a factor of three to the representation bound.
-/

namespace ThreeSum.RawIncidences
open _root_.ThreeSum.RawIncidences


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds







































theorem tuple_mem_representations {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (b c : ℤ) :
    List.ofFn t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J b c ↔
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ b - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft t ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ c - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight t := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mem_representations]
  simp only [List.length_ofFn, true_and, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight]









theorem mem_witnesses {h J : ℕ} {P d a b c : ℤ} {w : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.Witness h J} :
    w ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d a b c ↔
      List.ofFn w.1 ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J (b % P) (c % P + d) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a % P + _root_.ThreeSum.RawIncidences.lift w.2 * P + d) - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey w.1 := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses, Finset.mem_filter, Finset.mem_univ, true_and]















section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]









theorem mem_rawOn {h J : ℕ} {P d : ℤ} {T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ} :
    r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c ↔
      r.1 ∈ T ∧ r.2 ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d (a r.1.1) (b r.1.2.1) (c r.1.2.2) :=
  Finset.mem_sigma























theorem bucket_product_eq_sum {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.leftBucket P B b t * _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rightBucket P d C c t =
      ∑ j ∈ B, ∑ k ∈ C,
        if _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ b j % P - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft t ∧
          _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ c k % P + d - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight t then 1 else 0 := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.leftBucket _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rightBucket
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hL : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ b j % P - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft t <;>
    by_cases hR : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ c k % P + d - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight t <;> simp [hL, hR]

theorem bucket_product_eq_card {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.leftBucket P B b t * _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rightBucket P d C c t =
      ((B ×ˢ C).filter fun p => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ b p.1 % P - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft t ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ c p.2 % P + d - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight t).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.bucket_product_eq_sum P d B C b c t











end OriginalIndices

end ThreeSum.RawIncidences

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact bucket products at a wanted reporting prefix

The raw fiber used by the reporting theorem is here expanded into independently
counted B and C buckets. The wanted query fixes its original A index, lift,
and all chosen-map occurrences and output subsets.
-/

namespace ThreeSum.RawPrefixCounts
open _root_.ThreeSum.RawPrefixCounts


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting

section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



theorem prefixQuery_eq_card {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (k : ℕ) (pre : List (Finset (Fin (464 * h)))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w k pre = (_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.prefixItems I w k pre).card := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery, _root_.ThreeSum.Reporting.mass, _root_.ThreeSum.Subset.fiberMass, _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.prefixItems,
    Finset.sum_const, smul_eq_mul, mul_one]





section

private def private_b946aacb2b_pack {h J : ℕ} (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (s : Σ _t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J, β × γ) : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ :=
  ⟨(w.1, s.2), (s.1, w.2.1)⟩
end


section

private theorem private_c3fa1f867e_pack_injective {h J : ℕ} (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) :
    Function.Injective (_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.private_b946aacb2b_pack (β := β) (γ := γ) w) := by
  intro s t he
  apply Sigma.ext
  · exact congrArg (fun r => r.2.1) he
  · exact heq_of_eq (congrArg (fun r => r.1.2) he)
end


section

private theorem private_8453fe8658_pack_unpack {h J : ℕ} (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)
    (hw : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.wantedOf r = w) : _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.private_b946aacb2b_pack w ⟨r.2.1, r.1.2⟩ = r := by
  rw [← hw]
  rfl
end


section

private theorem private_7f8ae00c38_pack_mem_prefixItems {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (464 * h))))
    (s : Σ _t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J, β × γ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.private_b946aacb2b_pack w s ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.prefixItems (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre ↔
      (w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
        (a w.1 % P + _root_.ThreeSum.RawIncidences.lift w.2.1 * P + d) - _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2) ∧
      s.1 ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions w.2.2 k pre ∧ s.2 ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.compatiblePairs P d B C b c s.1 := by
  constructor
  · intro hr
    obtain ⟨hd, hpre⟩ := Finset.mem_filter.mp hr
    obtain ⟨hraw, hw⟩ := Finset.mem_filter.mp hd
    obtain ⟨hm, hrep, hkey⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_rawOn.mp hraw).imp_right _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_witnesses.mp
    have hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput s.1 = w.2.2 := congrArg (fun z => z.2.2) hw
    have hke : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey s.1 = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2 := congrArg _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey hq
    have hpair := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tuple_mem_representations s.1 (b s.2.1 % P)
      (c s.2.2 % P + d)).mp hrep
    have hm' : w.1 ∈ A ∧ s.2 ∈ B ×ˢ C := Finset.mem_product.mp hm
    refine ⟨⟨hm'.1, ?_⟩, ?_, ?_⟩
    · simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.private_b946aacb2b_pack, hke] using hkey
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, hpre⟩
    · exact Finset.mem_filter.mpr ⟨hm'.2, hpair⟩
  · rintro ⟨⟨ha, hkey⟩, ht, hp⟩
    obtain ⟨_, hq, hpre⟩ := Finset.mem_filter.mp ht
    obtain ⟨hm, hpair⟩ := Finset.mem_filter.mp hp
    have hke : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey s.1 = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2 := congrArg _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey hq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, hpre⟩
    · apply _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_rawOn.mpr
      refine ⟨Finset.mem_product.mpr ⟨ha, hm⟩, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_witnesses.mpr ⟨?_, ?_⟩⟩
      · exact (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tuple_mem_representations s.1 _ _).mpr hpair
      · simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.private_b946aacb2b_pack, hke] using hkey
    · exact Prod.ext rfl (Prod.ext rfl hq)
end






end Indices

end ThreeSum.RawPrefixCounts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts

set_option maxRecDepth 8000
open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.prefixQuery_eq_bucketPrefixMass__implementation_1cf93028dd {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (464 * h)))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre =
      _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.bucketPrefixMass P d A B C a b c w k pre := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.prefixQuery_eq_card, _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.bucketPrefixMass]
  split
  next hguard =>
    let pairs := (_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions w.2.2 k pre).sigma fun t => _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.compatiblePairs P d B C b c t
    have he : pairs.card =
        (_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.prefixItems (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre).card := by
      apply Finset.card_bij (fun s _ => _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.private_b946aacb2b_pack w s)
      · intro s hs
        exact (_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.private_7f8ae00c38_pack_mem_prefixItems P d A B C a b c w k pre s).mpr
          ⟨hguard, (Finset.mem_sigma.mp hs).1, (Finset.mem_sigma.mp hs).2⟩
      · intro s _ t _ he
        exact _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.private_c3fa1f867e_pack_injective w he
      · intro r hr
        have hw := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
        let s : Σ _t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J, β × γ := ⟨r.2.1, r.1.2⟩
        have he : _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.private_b946aacb2b_pack w s = r := _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.private_8453fe8658_pack_unpack w r hw
        refine ⟨s, ?_, he⟩
        have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.private_7f8ae00c38_pack_mem_prefixItems P d A B C a b c w k pre s).mp (he ▸ hr)
        exact Finset.mem_sigma.mpr hs.2
    rw [← he, Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro t _
    exact (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.bucket_product_eq_card P d B C b c t).symm
  next hguard =>
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hw := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
    have he := _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.private_8453fe8658_pack_unpack w r hw
    have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.private_7f8ae00c38_pack_mem_prefixItems P d A B C a b c w k pre ⟨r.2.1, r.1.2⟩).mp
      (he ▸ hr)
    exact hguard hs.1
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.prefixQuery_eq_bucketPrefixMass__implementation_1cf93028dd.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.prefixQuery_eq_bucketPrefixMass__implementation_1cf93028dd.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
