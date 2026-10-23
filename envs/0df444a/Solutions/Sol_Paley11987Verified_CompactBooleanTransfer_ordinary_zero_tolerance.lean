-- Prove2me | solution 1 for Paley11987Verified.CompactBooleanTransfer.ordinary_zero_tolerance
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T04:55:37.333415+00:00
-- url     : https://prove2.me/submissions/7bdfb229-5a0f-4df3-a4ac-59785d8aefbe

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Paley11987Support_053
import Definitions.Def_Paley11987Support_054
import Definitions.Def_Paley11987Support_055
import Theorems.Thm_Paley11987Verified_Sensitivity2075_tolerant_repair_cases

set_option autoImplicit false
set_option Elab.async false
section z29

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open scoped Classical BigOperators
namespace OAI.Paper320













namespace Tournament
variable {k : ℕ} (T : Tournament k)



theorem not_adj_reverse {i j : Fin k} (h : T.Adj i j) : ¬ T.Adj j i :=
  (T.edge_compl (T.ne_of_adj h)).mp h

theorem adj_or_reverse {i j : Fin k} (h : i ≠ j) : T.Adj i j ∨ T.Adj j i := by
  by_cases hh : T.Adj j i
  · exact Or.inr hh
  · exact Or.inl ((T.edge_compl h).mpr hh)



end Tournament









@[simp] theorem mem_childLift {J I : Type} (j : J) (A : Finset I) (p : J × I) :
    p ∈ childLift j A ↔ p.1 = j ∧ p.2 ∈ A := by
  rcases p with ⟨k, a⟩
  unfold childLift
  rw [Finset.mem_map]
  constructor
  · rintro ⟨b, hb, hp⟩
    change (j, b) = (k, a) at hp
    cases hp
    exact ⟨rfl, hb⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

@[simp] theorem childLift_card {J I : Type} (j : J) (A : Finset I) :
    (childLift j A).card = A.card := Finset.card_map _





theorem card_biUnion_le_mul {J I : Type} [DecidableEq I] (A : Finset J) (B : J → Finset I) (n : ℕ)
    (hn : ∀ j ∈ A, (B j).card ≤ n) : (A.biUnion B).card ≤ A.card * n := by
  calc
    (A.biUnion B).card ≤ ∑ j ∈ A, (B j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ A, n := Finset.sum_le_sum hn
    _ = A.card * n := by simp

end OAI.Paper320
namespace Sensitivity205
open OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205













@[simp] theorem mem_missingTargets {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) (c : Fin r) :
    c ∈ missingTargets F A x i ↔ F A (recursiveChild x i c) = false := by
  simp [missingTargets]

@[simp] theorem mem_failedGuards {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) :
    j ∈ failedGuards T label F G x i ↔
      T.Adj i j ∧ F G (recursiveChild x j (label i j)) = true := by
  simp [failedGuards]

theorem missingTargets_empty {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    missingTargets F A x i = ∅ ↔ ∀ c, F A (recursiveChild x i c) = true := by
  simp [missingTargets, Finset.filter_eq_empty_iff]







section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

















end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)





end RowFlips

section Nesting
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F)

include hF in
theorem failedGuards_subset {Gi Gj : Fin n} (hG : Gj ≤ Gi)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    failedGuards T label F Gi x i ⊆ failedGuards T label F Gj x i := by
  intro j hj
  obtain ⟨hij, hon⟩ := (mem_failedGuards T label F Gi x i j).mp hj
  exact (mem_failedGuards T label F Gj x i j).mpr ⟨hij, hF.accepts_of_le hG hon⟩

include hF in
theorem tolerantRow_nested {Ai Aj Gi Gj : Fin n} {qi qj : ℕ}
    (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hq : qj ≤ qi)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : tolerantRow T label F Aj Gj qj x i = true) :
    tolerantRow T label F Ai Gi qi x i = true := by
  obtain ⟨ht, hg⟩ := (tolerantRow_true T label F Aj Gj qj x i).mp hi
  exact (tolerantRow_true T label F Ai Gi qi x i).mpr
    ⟨fun c => hF.accepts_of_le hA (ht c),
      (Finset.card_le_card (failedGuards_subset T label F hF hG x i)).trans (hg.trans hq)⟩

end Nesting



theorem missing_singleton {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) :
    missingTargets F A x i = {missingWitness F A x hr i} := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hi
  have hne : (missingTargets F A x i).Nonempty := hc ▸ Finset.singleton_nonempty c
  have hm : missingWitness F A x hr i ∈ missingTargets F A x i := by
    simp only [missingWitness, dif_pos hne]
    exact hne.choose_spec
  rw [hc, Finset.mem_singleton] at hm
  simpa only [hm] using hc



theorem missingWitness_unique {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) (c : Fin r)
    (hc : F A (recursiveChild x i c) = false) : c = missingWitness F A x hr i := by
  have hm := (mem_missingTargets F A x i c).mpr hc
  rwa [missing_singleton F A x hr i hi, Finset.mem_singleton] at hm

theorem missingWitness_other_true {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) (c : Fin r)
    (hc : c ≠ missingWitness F A x hr i) : F A (recursiveChild x i c) = true := by
  cases hh : F A (recursiveChild x i c)
  · exact False.elim (hc (missingWitness_unique F A x hr i hi c hh))
  · rfl

section JointCandidates
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F) (Ai Aj Gi Gj : Fin n)
  (hA : Ai ≤ Aj) (hG : Gj ≤ Gi)
  (x : ((Fin k × Fin r) × I) → Bool)

include hF hA hG in

theorem tolerant_target_weak_false {qi qj : ℕ} (hq : qj ≤ qi) (hr : 0 < r)
    (hx : tolerantFamily T label F Ai Gi qi x = false) {i : Fin k}
    (hi : i ∈ tolerantTargets T label F Aj Gj qj x) :
    F Ai (recursiveChild x i (missingWitness F Aj x hr i)) = false := by
  obtain ⟨hmiss, hguards⟩ := (Finset.mem_filter.mp hi).2
  cases hw : F Ai (recursiveChild x i (missingWitness F Aj x hr i))
  · rfl
  · have hrow : tolerantRow T label F Ai Gi qi x i = true := by
      apply (tolerantRow_true T label F Ai Gi qi x i).mpr
      constructor
      · intro c
        by_cases hc : c = missingWitness F Aj x hr i
        · simpa only [hc] using hw
        · exact hF.accepts_of_le hA (missingWitness_other_true F Aj x hr i hmiss c hc)
      · exact (Finset.card_le_card (failedGuards_subset T label F hF hG x i)).trans
          (hguards.trans hq)
    have hoff := (tolerantFamily_false T label F Ai Gi qi x).mp hx i
    simp [hoff] at hrow

include hF hA hG in

theorem tolerant_guard_sets_eq (q : ℕ)
    (hx : tolerantFamily T label F Ai Gi q x = false) {i : Fin k}
    (hi : i ∈ tolerantGuards T label F Aj Gj q x) :
    failedGuards T label F Gi x i = failedGuards T label F Gj x i := by
  obtain ⟨hmiss, hguards⟩ := (Finset.mem_filter.mp hi).2
  have htargets : ∀ c, F Ai (recursiveChild x i c) = true :=
    fun c => hF.accepts_of_le hA ((missingTargets_empty F Aj x i).mp hmiss c)
  have hcount : q < (failedGuards T label F Gi x i).card := by
    by_contra hn
    have hrow := (tolerantRow_true T label F Ai Gi q x i).mpr ⟨htargets, by omega⟩
    have hoff := (tolerantFamily_false T label F Ai Gi q x).mp hx i
    simp [hoff] at hrow
  exact Finset.eq_of_subset_of_card_le (failedGuards_subset T label F hF hG x i) (by omega)



end JointCandidates





end Sensitivity2075
end
end z29

section z30

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity205 Sensitivity2075

namespace ZT

variable {I : Type} [Fintype I]



@[simp] theorem mem_flipsTo (f : (I → Bool) → Bool) (b : Bool) (x : I → Bool)
    (a : I) : a ∈ flipsTo f b x ↔ f (flip x {a}) = b := by
  simp [flipsTo]



















theorem family_nested {n k r : ℕ} {J : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (J → Bool) → Bool) (hF : NestedFamily F)
    {Ai Aj Gi Gj : Fin n} {qi qj : ℕ}
    (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hq : qj ≤ qi)
    (x : ((Fin k × Fin r) × J) → Bool)
    (hx : tolerantFamily T label F Aj Gj qj x = true) :
    tolerantFamily T label F Ai Gi qi x = true := by
  obtain ⟨v, hv⟩ := (tolerantFamily_true T label F Aj Gj qj x).mp hx
  exact (tolerantFamily_true T label F Ai Gi qi x).mpr
    ⟨v, tolerantRow_nested T label F hF hA hG hq x v hv⟩



end ZT
end
end z30

section z31

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT

variable {n k r : ℕ} {I : Type} [Fintype I]



@[simp] theorem childFlipsTo_card (F : Fin n → (I → Bool) → Bool) (a : Fin n) (b : Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (v : Fin k) (c : Fin r) :
    (childFlipsTo F a b x v c).card = (flipsTo (F a) b (recursiveChild x v c)).card := by
  simp [childFlipsTo]

@[simp] theorem mem_childFlipsTo_same (F : Fin n → (I → Bool) → Bool) (a : Fin n) (b : Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (v : Fin k) (c : Fin r) (z : I) :
    ((v,c),z) ∈ childFlipsTo F a b x v c ↔
      F a (flip (recursiveChild x v c) {z}) = b := by
  simp [childFlipsTo]

















end ZT
end
end z31

section z32
set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators
namespace OAI.Paper320.Tournament
variable {k : ℕ} (T : Tournament k)



theorem card_internalEdges (I : Finset (Fin k)) :
    (T.internalEdges I).card = I.card.choose 2 := by
  let U := T.internalEdges I
  let V := (I ×ˢ I).filter fun p => T.Adj p.2 p.1
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact T.not_adj_reverse (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  have hu : U.disjUnion V hd = I.offDiag := by
    ext ⟨i,j⟩
    simp only [Finset.mem_disjUnion, U, V, internalEdges, Finset.mem_filter,
      Finset.mem_product, Finset.mem_offDiag]
    constructor
    · rintro (⟨⟨hi,hj⟩,h⟩ | ⟨⟨hi,hj⟩,h⟩)
      · exact ⟨hi,hj,T.ne_of_adj h⟩
      · exact ⟨hi,hj,(T.ne_of_adj h).symm⟩
    · rintro ⟨hi,hj,hne⟩
      exact (T.adj_or_reverse hne).imp (fun h => ⟨⟨hi,hj⟩,h⟩) (fun h => ⟨⟨hi,hj⟩,h⟩)
  have hs : U.card = V.card := Finset.card_equiv (Equiv.prodComm (Fin k) (Fin k)) (by
    intro p
    simp only [U,V,internalEdges,Finset.mem_filter,Finset.mem_product,Equiv.prodComm_apply]
    tauto)
  have hc := congrArg Finset.card hu
  rw [Finset.card_disjUnion, ← hs, Finset.offDiag_card] at hc
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  change U.card = _
  omega

theorem sum_outdegree_eq (I : Finset (Fin k)) :
    ∑ i ∈ I, (I.filter (T.Adj i)).card = (T.internalEdges I).card := by
  simp only [internalEdges, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

end OAI.Paper320.Tournament
namespace SensitivityQ



theorem card_bound_arithmetic (m q : ℕ) (hc : m.choose 2 ≤ m * (q+1)) :
    m ≤ 2*q+3 := by
  have hd : m * (m-1) ≤ 2*(m*(q+1))+1 := by
    rw [Nat.choose_two_right] at hc
    omega
  by_contra hn
  have hm : 2*q+4 ≤ m := by omega
  have hs : 2*q+3 ≤ m-1 := by omega
  have hmul := Nat.mul_le_mul_left m hs
  nlinarith

theorem guards_card {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (A G : Fin n) (hGA : G ≤ A)
    (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) :
    (tolerantGuards T label F A G q x).card ≤ 2*q+3 := by
  let GC := tolerantGuards T label F A G q x
  have hlocal : ∀ i ∈ GC, (GC.filter (T.Adj i)).card ≤ q+1 := by
    intro i hi
    have hsub : GC.filter (T.Adj i) ⊆ failedGuards T label F G x i := by
      intro j hj
      obtain ⟨hj, hij⟩ := Finset.mem_filter.mp hj
      exact (mem_failedGuards T label F G x i j).mpr ⟨hij,
        hF.accepts_of_le hGA ((missingTargets_empty F A x j).mp
          (Finset.mem_filter.mp hj).2.1 _)⟩
    have hc := Finset.card_le_card hsub
    have he := (Finset.mem_filter.mp hi).2.2
    omega
  apply card_bound_arithmetic
  calc
    GC.card.choose 2 = ∑ i ∈ GC, (GC.filter (T.Adj i)).card := by
      rw [T.sum_outdegree_eq, T.card_internalEdges]
    _ ≤ ∑ _i ∈ GC, (q+1) := Finset.sum_le_sum hlocal
    _ = GC.card * (q+1) := by simp

theorem guard_charge {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (A G : Fin n) (hGA : G ≤ A)
    (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (c e : ℕ) :
    let GC := tolerantGuards T label F A G q x
    (∑ i ∈ GC, ∑ j ∈ failedGuards T label F G x i,
      if j ∈ GC then e else c) =
      (GC.card*(q+1)-GC.card.choose 2)*c + GC.card.choose 2*e := by
  let GC := tolerantGuards T label F A G q x
  let B := failedGuards T label F G x
  have hinside : ∀ i, (B i).filter (fun j => j ∈ GC) = GC.filter (T.Adj i) := by
    intro i
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hb, hj⟩
      exact ⟨hj, ((mem_failedGuards T label F G x i j).mp hb).1⟩
    · rintro ⟨hj, hij⟩
      exact ⟨(mem_failedGuards T label F G x i j).mpr ⟨hij,
        hF.accepts_of_le hGA ((missingTargets_empty F A x j).mp
          (Finset.mem_filter.mp hj).2.1 _)⟩, hj⟩
  have htotal : (∑ i ∈ GC, (B i).card) = GC.card*(q+1) := by
    calc
      _ = ∑ _i ∈ GC, (q+1) := Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2.2)
      _ = _ := by simp
  have hin : (∑ i ∈ GC, ((B i).filter fun j => j ∈ GC).card) = GC.card.choose 2 := by
    simp only [hinside]
    rw [T.sum_outdegree_eq, T.card_internalEdges]
  have hout : (∑ i ∈ GC, ((B i).filter fun j => j ∉ GC).card) =
      GC.card*(q+1)-GC.card.choose 2 := by
    have hh : (∑ i ∈ GC, ((B i).filter fun j => j ∈ GC).card) +
        (∑ i ∈ GC, ((B i).filter fun j => j ∉ GC).card) = GC.card*(q+1) := by
      rw [← Finset.sum_add_distrib, ← htotal]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.card_filter_add_card_filter_not (s := B i) (fun j => j ∈ GC)
    omega
  change (∑ i ∈ GC, ∑ j ∈ B i, if j ∈ GC then e else c) =
    (GC.card*(q+1)-GC.card.choose 2)*c + GC.card.choose 2*e
  calc
    _ = ∑ i ∈ GC, (((B i).filter fun j => j ∈ GC).card*e +
        ((B i).filter fun j => j ∉ GC).card*c) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hin, hout]
      omega





theorem source_card_arithmetic (m q : ℕ) (hc : m.choose 2 ≤ m*q) :
    m ≤ 2*q+1 := by
  have hd : m*(m-1) ≤ 2*(m*q)+1 := by
    rw [Nat.choose_two_right] at hc
    omega
  by_contra hn
  have hm : 2*q+2 ≤ m := by omega
  have hs : 2*q+1 ≤ m-1 := by omega
  have hmul := Nat.mul_le_mul_left m hs
  nlinarith

theorem positiveTargets_card {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (A G : Fin n) (hGA : G ≤ A)
    (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    (positiveTargets T label F A G q x hr).card ≤ 2*q+1 := by
  let S := positiveTargets T label F A G q x hr
  have hgate : ∀ j ∈ S, ∀ c, F G (recursiveChild x j c) = true := by
    intro j hj c
    obtain ⟨hj, hgate⟩ := Finset.mem_filter.mp hj
    by_cases hc : c = missingWitness F A x hr j
    · simpa only [hc] using hgate
    · exact hF.accepts_of_le hGA
        (missingWitness_other_true F A x hr j (Finset.mem_filter.mp hj).2.1 c hc)
  have hlocal : ∀ i ∈ S, (S.filter (T.Adj i)).card ≤ q := by
    intro i hi
    have hsub : S.filter (T.Adj i) ⊆ failedGuards T label F G x i := by
      intro j hj
      obtain ⟨hj, hij⟩ := Finset.mem_filter.mp hj
      exact (mem_failedGuards T label F G x i j).mpr ⟨hij, hgate j hj _⟩
    exact (Finset.card_le_card hsub).trans
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.2
  apply source_card_arithmetic
  calc
    S.card.choose 2 = ∑ i ∈ S, (S.filter (T.Adj i)).card := by
      rw [T.sum_outdegree_eq, T.card_internalEdges]
    _ ≤ ∑ _i ∈ S, q := Finset.sum_le_sum hlocal
    _ = S.card*q := by simp

theorem positiveTargets_guards_coupling {n k r : ℕ} {I : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    ((positiveTargets T label F A G q x hr).card +
      (tolerantGuards T label F A G q x).card).choose 2 ≤
      q * (positiveTargets T label F A G q x hr).card +
      (q+1) * (tolerantGuards T label F A G q x).card := by
  let P := positiveTargets T label F A G q x hr
  let GC := tolerantGuards T label F A G q x
  let S := P ∪ GC
  have hdis : Disjoint P GC := by
    apply Finset.disjoint_left.mpr
    intro i hiP hiGC
    have hone : (missingTargets F A x i).card = 1 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hiP).1).2.1
    have hempty : missingTargets F A x i = ∅ :=
      (Finset.mem_filter.mp hiGC).2.1
    simp only [hempty, Finset.card_empty] at hone
    omega
  have hgate : ∀ j ∈ S, ∀ c, F G (recursiveChild x j c) = true := by
    intro j hj c
    rcases Finset.mem_union.mp hj with hjP | hjGC
    · obtain ⟨hjTC, hpass⟩ := Finset.mem_filter.mp hjP
      by_cases hc : c = missingWitness F A x hr j
      · simpa only [hc] using hpass
      · exact hF.accepts_of_le hGA
          (missingWitness_other_true F A x hr j (Finset.mem_filter.mp hjTC).2.1 c hc)
    · exact hF.accepts_of_le hGA
        ((missingTargets_empty F A x j).mp (Finset.mem_filter.mp hjGC).2.1 c)
  have hsub (i : Fin k) : S.filter (T.Adj i) ⊆ failedGuards T label F G x i := by
    intro j hj
    obtain ⟨hjS, hij⟩ := Finset.mem_filter.mp hj
    exact (mem_failedGuards T label F G x i j).mpr ⟨hij, hgate j hjS _⟩
  have hlocalP : ∀ i ∈ P, (S.filter (T.Adj i)).card ≤ q := by
    intro i hi
    exact (Finset.card_le_card (hsub i)).trans
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.2
  have hlocalGC : ∀ i ∈ GC, (S.filter (T.Adj i)).card ≤ q+1 := by
    intro i hi
    have he : (failedGuards T label F G x i).card = q+1 :=
      (Finset.mem_filter.mp hi).2.2
    exact (Finset.card_le_card (hsub i)).trans (Nat.le_of_eq he)
  change (P.card + GC.card).choose 2 ≤ q*P.card + (q+1)*GC.card
  calc
    (P.card + GC.card).choose 2 = S.card.choose 2 := by
      rw [show S.card = P.card + GC.card from Finset.card_union_of_disjoint hdis]
    _ = ∑ i ∈ S, (S.filter (T.Adj i)).card := by
      rw [T.sum_outdegree_eq, T.card_internalEdges]
    _ = (∑ i ∈ P, (S.filter (T.Adj i)).card) +
        ∑ i ∈ GC, (S.filter (T.Adj i)).card := Finset.sum_union hdis
    _ ≤ (∑ _i ∈ P, q) + ∑ _i ∈ GC, (q+1) :=
      Nat.add_le_add (Finset.sum_le_sum hlocalP) (Finset.sum_le_sum hlocalGC)
    _ = q*P.card + (q+1)*GC.card := by simp [Nat.mul_comm]

end SensitivityQ
namespace SensitivitySourceZero
variable {n k r : ℕ} {I : Type}





theorem target_no_edge_to_full_gate (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k)
    (hi : i ∈ tolerantTargets T label F A G 0 x)
    (hj : ∀ c, F G (recursiveChild x j c) = true) : ¬ T.Adj i j := by
  intro hij
  have hz : (failedGuards T label F G x i).card = 0 := by
    have hh := (Finset.mem_filter.mp hi).2.2
    omega
  have hempty := Finset.card_eq_zero.mp hz
  have hmem : j ∈ failedGuards T label F G x i :=
    (mem_failedGuards T label F G x i j).mpr ⟨hij, hj _⟩
  simpa only [hempty, Finset.notMem_empty] using hmem

theorem guard_not_target_zero (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ tolerantGuards T label F A G 0 x) :
    i ∉ tolerantTargets T label F A G 0 x := by
  intro hit
  have hone := (Finset.mem_filter.mp hit).2.1
  have hempty := (Finset.mem_filter.mp hi).2.1
  simp only [hempty, Finset.card_empty] at hone
  omega



theorem guard_dominates_target_zero (T : Tournament k)
    (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A)
    (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k)
    (hi : i ∈ tolerantGuards T label F A G 0 x)
    (hj : j ∈ tolerantTargets T label F A G 0 x) : T.Adj i j := by
  have hne : i ≠ j := by
    intro he
    subst j
    exact guard_not_target_zero T label F A G x i hi hj
  have hfull : ∀ c, F G (recursiveChild x i c) = true := by
    intro c
    exact hF.accepts_of_le hGA
      ((missingTargets_empty F A x i).mp (Finset.mem_filter.mp hi).2.1 c)
  exact (T.adj_or_reverse hne).resolve_right
    (target_no_edge_to_full_gate T label F A G x j i hj hfull)









end SensitivitySourceZero
end
end z32

section z33

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





theorem up_subset_repairs (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F t g q x = false) :
    flipsTo (tolerantFamily T label F t g q) true x ⊆
      targetRepairs T label F t g q x ∪ guardRepairs T label F t g q x := by
  rintro ⟨⟨w,c⟩,a⟩ hp
  obtain ⟨v,hv⟩ := (tolerantFamily_true T label F t g q _).mp
    ((mem_flipsTo _ _ _ _).mp hp)
  have hoff := (tolerantFamily_false T label F t g q x).mp hx v
  rcases _root_.Paley11987Verified.Sensitivity2075.tolerant_repair_cases T label F t g q x v w c a hoff hv with
    ⟨hT, hw, hfalse, htrue⟩ | ⟨hG, hadj, hc, htrue, hfalse⟩
  · subst w
    have hc := missingWitness_unique F t x (by decide) v
      (Finset.mem_filter.mp hT).2.1 c hfalse
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨v,hT,?_⟩
    rw [← hc]
    exact (mem_childFlipsTo_same _ _ _ _ _ _ _).mpr htrue
  · subst c
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨v,hG,Finset.mem_biUnion.mpr ⟨w,?_,?_⟩⟩
    · exact (mem_failedGuards T label F g x v w).mpr ⟨hadj,htrue⟩
    · exact (mem_childFlipsTo_same _ _ _ _ _ _ _).mpr hfalse

theorem sum_binary_weights {V : Type} [DecidableEq V] (S : Finset V)
    (p : V → Prop) [DecidablePred p] (a b : ℕ) :
    (∑ v ∈ S, if p v then a else b) =
      (S.filter p).card*a+(S.card-(S.filter p).card)*b := by
  have hsplit : (∑ v ∈ S, if p v then a else b) =
      (∑ v ∈ S.filter p, a)+(∑ v ∈ S.filter (fun v => ¬p v), b) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hp : p v <;> simp [hp]
  rw [hsplit]
  simp only [Finset.sum_const, smul_eq_mul]
  have hcard := Finset.card_filter_add_card_filter_not (s := S) p
  congr 1
  congr 1
  omega

theorem targetRepairs_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga)
    (qa q : ℕ) (hq : q ≤ qa) (a b : ℕ)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga qa x = false) :
    (targetRepairs T label F tb gb q x).card ≤
      (positiveTargets T label F tb gb q x (by decide)).card*a+
      ((tolerantTargets T label F tb gb q x).card-
        (positiveTargets T label F tb gb q x (by decide)).card)*b := by
  let S := tolerantTargets T label F tb gb q x
  let tw := missingWitness F tb x (by decide)
  let p := fun v => F gb (recursiveChild x v (tw v)) = true
  have hsum : (targetRepairs T label F tb gb q x).card ≤
      ∑ v ∈ S, if p v then a else b := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro v hv
    have hta := tolerant_target_weak_false T label F hF ta tb ga gb ht hg x hq
      (by decide) hx hv
    by_cases hp : p v
    · simpa only [if_pos hp, childFlipsTo_card] using ha _ hp hta
    · have hfalse : F gb (recursiveChild x v (tw v)) = false := by
        simpa only [p, Bool.not_eq_true] using hp
      simpa only [if_neg hp, childFlipsTo_card] using hb _ hfalse
  rw [sum_binary_weights] at hsum
  exact hsum





end ZT
end
end z33

section z34

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]









@[simp] theorem mem_guardArcs (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (e : Fin k × Fin k) :
    e ∈ guardArcs T label F t g q x ↔
      e.1 ∈ tolerantGuards T label F t g q x ∧ e.2 ∈ failedGuards T label F g x e.1 := by
  simp [guardArcs]

theorem guardArcs_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (externalGuardArcs T label F t g q x).card =
      (tolerantGuards T label F t g q x).card*(q+1)-
        (tolerantGuards T label F t g q x).card.choose 2 ∧
    (internalGuardArcs T label F t g q x).card =
      (tolerantGuards T label F t g q x).card.choose 2 := by
  let R := tolerantGuards T label F t g q x
  let B := failedGuards T label F g x
  have he : (externalGuardArcs T label F t g q x).card =
      ∑ v ∈ R, ∑ w ∈ B v, if w ∈ R then 0 else 1 := by
    simp only [externalGuardArcs,guardArcs,Finset.card_eq_sum_ones,
      Finset.sum_filter,Finset.sum_product,Finset.sum_const_zero]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hr : w ∈ R <;> simp [R,B,hr]
  have hi : (internalGuardArcs T label F t g q x).card =
      ∑ v ∈ R, ∑ w ∈ B v, if w ∈ R then 1 else 0 := by
    simp only [internalGuardArcs,guardArcs,Finset.card_eq_sum_ones,
      Finset.sum_filter,Finset.sum_product,Finset.sum_const_zero]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hr : w ∈ R <;> simp [R,B,hr]
  constructor
  · rw [he]
    simpa using guard_charge T label F hF t g hgt q x 1 0
  · rw [hi]
    simpa using guard_charge T label F hF t g hgt q x 0 1

theorem guardRepairs_subset_coordinates (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    guardRepairs T label F t g q x ⊆
      ((externalGuardArcs T label F t g q x).image (arcCoordinate label)).biUnion
        (fun z => childFlipsTo F g false x z.1 z.2) ∪
      ((internalGuardArcs T label F t g q x).image (arcCoordinate label)).biUnion
        (fun z => childFlipsTo F g false x z.1 z.2) := by
  intro p hp
  obtain ⟨v,hv,hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨w,hw,hp⟩ := Finset.mem_biUnion.mp hp
  have harc : (v,w) ∈ guardArcs T label F t g q x := (mem_guardArcs _ _ _ _ _ _ _ _).mpr ⟨hv,hw⟩
  by_cases hin : w ∈ tolerantGuards T label F t g q x
  · apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨(w,label v w),Finset.mem_image.mpr
      ⟨(v,w),Finset.mem_filter.mpr ⟨harc,hin⟩,rfl⟩,hp⟩
  · apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨(w,label v w),Finset.mem_image.mpr
      ⟨(v,w),Finset.mem_filter.mpr ⟨harc,hin⟩,rfl⟩,hp⟩

theorem filter_image_card_le {A B : Type} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (f : A → B) (p : B → Prop) [DecidablePred p] :
    ((S.image f).filter p).card ≤ (S.filter fun a => p (f a)).card := by
  have hsub : (S.image f).filter p ⊆ (S.filter fun a => p (f a)).image f := by
    intro b hb
    obtain ⟨hb,hp⟩ := Finset.mem_filter.mp hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hp⟩,rfl⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

theorem positive_costly_coordinates_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (Z : Finset (Fin k × Fin 2)) :
    (Z.filter fun z => z.1 ∈ positiveTargets T label F t g q x (by decide) ∧
      F t (recursiveChild x z.1 z.2) = false).card ≤
      (positiveTargets T label F t g q x (by decide)).card := by
  let S := Z.filter fun z => z.1 ∈ positiveTargets T label F t g q x (by decide) ∧
    F t (recursiveChild x z.1 z.2) = false
  have hinj : Set.InjOn Prod.fst (↑S : Set (Fin k × Fin 2)) := by
    intro z hz w hw he
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hzt := (Finset.mem_filter.mp hz'.1).1
    have hwt := (Finset.mem_filter.mp hw'.1).1
    have hzc := missingWitness_unique F t x (by decide) z.1
      (Finset.mem_filter.mp hzt).2.1 z.2 hz'.2
    have hwc := missingWitness_unique F t x (by decide) w.1
      (Finset.mem_filter.mp hwt).2.1 w.2 hw'.2
    apply Prod.ext he
    rw [hzc,hwc,he]
  have hcard : (S.image Prod.fst).card = S.card := Finset.card_image_iff.mpr hinj
  have hsub : S.image Prod.fst ⊆ positiveTargets T label F t g q x (by decide) := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hz).2.1
  change S.card ≤ _
  rw [← hcard]
  exact Finset.card_le_card hsub

theorem positive_coordinates_card (P : Finset (Fin k)) (Z : Finset (Fin k × Fin 2)) :
    (Z.filter fun z => z.1 ∈ P).card ≤ 2*P.card := by
  have hs : Z.filter (fun z => z.1 ∈ P) ⊆ P ×ˢ Finset.univ := by
    intro z hz
    exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hz).2,Finset.mem_univ _⟩
  simpa [Nat.mul_comm] using Finset.card_le_card hs

end ZT
end
end z34

section z35

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
namespace ZT

theorem binary_capacity_charge (n z N J s j : ℕ)
    (hjs : j ≤ s) (hnz : n ≤ z) (hnN : n ≤ N) (hz : z ≤ N+J) :
    n*s+(z-n)*j ≤ N*s+J*j := by
  have hn : n+(N-n)=N := Nat.add_sub_of_le hnN
  have hzn : n+(z-n)=z := Nat.add_sub_of_le hnz
  have hm := Nat.mul_le_mul_left (N-n) hjs
  have htail := Nat.mul_le_mul_right j (show z-n ≤ (N-n)+J by omega)
  nlinarith

theorem positive_capacity_charge (n z E W L u δ s j : ℕ)
    (hjs : j ≤ s) (hnz : n ≤ z)
    (hnE : n+δ ≤ E) (hnW : n+δ ≤ W+u)
    (hzE : z ≤ E) (hzW : z ≤ W+2*u)
    (hWL : W+L ≤ E) (hδW : δ ≤ W) :
    n*s+(z-n)*j ≤
      (E-(L-u)-δ)*s+(min u (L-u)+δ)*j := by
  apply binary_capacity_charge _ _ _ _ _ _ hjs hnz
  · omega
  · omega

theorem positive_union_charge {V α : Type} [DecidableEq V] [DecidableEq α]
    (Z : Finset V) (inside costly : V → Prop)
    [DecidablePred inside] [DecidablePred costly]
    (D : V → Finset α) (E W L u δ s j : ℕ)
    (hjs : j ≤ s)
    (hZ : Z.card ≤ E) (hW : (Z.filter (fun v => ¬ inside v)).card ≤ W)
    (hL : W+L ≤ E)
    (hin : (Z.filter inside).card ≤ 2*u)
    (hcost : (Z.filter fun v => inside v ∧ costly v).card ≤ u)
    (hcheap : δ ≤ (Z.filter fun v => ¬ inside v ∧ ¬ costly v).card)
    (hD : ∀ v ∈ Z, (D v).card ≤ if costly v then s else j) :
    (Z.biUnion D).card ≤ (E-(L-u)-δ)*s+(min u (L-u)+δ)*j := by
  let n := (Z.filter costly).card
  let z := Z.card
  let ni := (Z.filter fun v => inside v ∧ costly v).card
  let no := (Z.filter fun v => ¬ inside v ∧ costly v).card
  let co := (Z.filter fun v => ¬ inside v ∧ ¬ costly v).card
  let out := (Z.filter fun v => ¬ inside v).card
  have hnz : n ≤ z := Finset.card_filter_le _ _
  have hout : no+co=out := by
    simpa only [no,co,out,Finset.filter_filter,and_assoc] using
      (Finset.card_filter_add_card_filter_not (s := Z.filter fun v => ¬inside v) costly)
  have hn : ni+no=n := by
    simpa only [ni,no,n,Finset.filter_filter,and_comm] using
      (Finset.card_filter_add_card_filter_not (s := Z.filter costly) inside)
  have hsplit : (Z.filter inside).card+out=z := by
    exact Finset.card_filter_add_card_filter_not (s := Z) inside
  have hδW : δ ≤ W := by
    have hco : co ≤ out := by omega
    exact hcheap.trans (hco.trans hW)
  have hnW : n+δ ≤ W+u := by
    change ni ≤ u at hcost
    change δ ≤ co at hcheap
    change out ≤ W at hW
    omega
  have hzW : z ≤ W+2*u := by
    change out ≤ W at hW
    omega
  have hnE : n+δ ≤ E := by
    have hdis : Disjoint (Z.filter costly)
        (Z.filter fun v => ¬inside v ∧ ¬costly v) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      exact (Finset.mem_filter.mp hw).2.2 (Finset.mem_filter.mp hv).2
    have hcard : n+co ≤ z := by
      rw [← Finset.card_union_of_disjoint hdis]
      exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _))
    change δ ≤ co at hcheap
    omega
  have hbound : (Z.biUnion D).card ≤ n*s+(z-n)*j := by
    apply Finset.card_biUnion_le.trans
    apply (Finset.sum_le_sum hD).trans_eq
    exact sum_binary_weights Z costly s j
  exact hbound.trans (positive_capacity_charge n z E W L u δ s j hjs hnz hnE hnW hZ hzW hL hδW)

theorem by_head_child_card {H α : Type} [DecidableEq H] [DecidableEq α]
    (S : Finset H) (Z : Finset (H × Fin 2)) (D : H × Fin 2 → Finset α) (j : ℕ)
    (hZS : ∀ z ∈ Z, z.1 ∈ S) (hD : ∀ z ∈ Z, (D z).card ≤ j) :
    (Z.biUnion D).card ≤ (2*S.card)*j := by
  have hcard : Z.card ≤ 2*S.card := by
    have hsub : Z ⊆ S ×ˢ Finset.univ := by
      intro z hz
      exact Finset.mem_product.mpr ⟨hZS z hz,Finset.mem_univ _⟩
    simpa [Nat.mul_comm] using Finset.card_le_card hsub
  calc
    (Z.biUnion D).card ≤ ∑ z ∈ Z, (D z).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ Z, j := Finset.sum_le_sum hD
    _ = Z.card*j := by simp
    _ ≤ (2*S.card)*j := Nat.mul_le_mul_right j hcard

end ZT
end
end z35

section z36
set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace SensitivityOrdinaryGuard
theorem tournament_outside_budget {k : ℕ} (T : Tournament k)
    (P R : Finset (Fin k)) (B O : Fin k → Finset (Fin k)) (q : ℕ)
    (hdis : Disjoint P R)
    (hinside : ∀ i, (P ∪ R).filter (T.Adj i) ⊆ B i)
    (hP : ∀ i ∈ P, (B i).card ≤ q)
    (hR : ∀ i ∈ R, (B i).card = q+1)
    (hOB : ∀ i, O i ⊆ B i)
    (hOR : ∀ i, ∀ j ∈ O i, j ∉ R) :
    (∑ i ∈ R, ((O i).filter fun j => j ∉ P).card)+
      (P.card+R.card).choose 2 ≤ q*P.card+(q+1)*R.card := by
  let S := P ∪ R
  let W := ∑ i ∈ R, ((O i).filter fun j => j ∉ P).card
  have hlocalP : ∀ i ∈ P, (S.filter (T.Adj i)).card ≤ q := by
    intro i hi
    exact (Finset.card_le_card (hinside i)).trans (hP i hi)
  have hlocalR : ∀ i ∈ R,
      ((O i).filter fun j => j ∉ P).card+
        (S.filter (T.Adj i)).card ≤ q+1 := by
    intro i hi
    have hd : Disjoint ((O i).filter fun j => j ∉ P) (S.filter (T.Adj i)) := by
      apply Finset.disjoint_left.mpr
      intro j hjO hjS
      obtain ⟨hjO, hjnotP⟩ := Finset.mem_filter.mp hjO
      obtain ⟨hjS, _⟩ := Finset.mem_filter.mp hjS
      rcases Finset.mem_union.mp hjS with hjP | hjR
      · exact hjnotP hjP
      · exact hOR i j hjO hjR
    calc
      _ = (((O i).filter fun j => j ∉ P) ∪ S.filter (T.Adj i)).card :=
        (Finset.card_union_of_disjoint hd).symm
      _ ≤ (B i).card := Finset.card_le_card (Finset.union_subset
        ((Finset.filter_subset _ _).trans (hOB i)) (hinside i))
      _ = q+1 := hR i hi
  have hs : (P.card+R.card).choose 2 =
      (∑ i ∈ P, (S.filter (T.Adj i)).card)+
        ∑ i ∈ R, (S.filter (T.Adj i)).card := by
    calc
      _ = S.card.choose 2 := by
        rw [show S.card = P.card+R.card from Finset.card_union_of_disjoint hdis]
      _ = ∑ i ∈ S, (S.filter (T.Adj i)).card := by
        rw [T.sum_outdegree_eq, T.card_internalEdges]
      _ = _ := Finset.sum_union hdis
  have hp : (∑ i ∈ P, (S.filter (T.Adj i)).card) ≤ P.card*q := by
    simpa using Finset.sum_le_sum hlocalP
  have hr : W+(∑ i ∈ R, (S.filter (T.Adj i)).card) ≤ R.card*(q+1) := by
    calc
      _ = ∑ i ∈ R, (((O i).filter fun j => j ∉ P).card+
          (S.filter (T.Adj i)).card) := by rw [Finset.sum_add_distrib]
      _ ≤ ∑ _i ∈ R, (q+1) := Finset.sum_le_sum hlocalR
      _ = _ := by simp
  change W+(P.card+R.card).choose 2 ≤ _
  rw [hs]
  have hh := Nat.add_le_add hp hr
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_comm] using hh

theorem positive_guards_disjoint {n k r : ℕ} {I : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    Disjoint (positiveTargets T label F A G q x hr)
      (tolerantGuards T label F A G q x) := by
  apply Finset.disjoint_left.mpr
  intro i hiP hiR
  have hone : (missingTargets F A x i).card = 1 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hiP).1).2.1
  have hempty : missingTargets F A x i = ∅ :=
    (Finset.mem_filter.mp hiR).2.1
  simp only [hempty, Finset.card_empty] at hone
  omega

theorem positive_gate_true {n k r : ℕ} {I : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (j : Fin k) (hj : j ∈ positiveTargets T label F A G q x hr)
    (c : Fin r) : F G (recursiveChild x j c) = true := by
  obtain ⟨hjT, hpass⟩ := Finset.mem_filter.mp hj
  by_cases hc : c = missingWitness F A x hr j
  · simpa only [hc] using hpass
  · exact hF.accepts_of_le hGA
      (missingWitness_other_true F A x hr j (Finset.mem_filter.mp hjT).2.1 c hc)

theorem choose_add_two (u m : ℕ) :
    (u+m).choose 2 = u.choose 2+m.choose 2+u*m := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [show u+1+m=(u+m)+1 by omega, Nat.choose_succ_succ, ih,
      Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    ring

theorem positive_lower_budget (q u m W : ℕ)
    (hW : W ≤ m*(q+1)-m.choose 2)
    (hbudget : W+(u+m).choose 2 ≤ q*u+(q+1)*m) :
    W+((u*m+u.choose 2)-q*u) ≤ m*(q+1)-m.choose 2 := by
  rw [choose_add_two] at hbudget
  have hbudget' : W+(u.choose 2+m.choose 2+u*m) ≤ q*u+m*(q+1) := by
    simpa only [Nat.mul_comm] using hbudget
  omega

end SensitivityOrdinaryGuard
end
end z36

section z37

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





theorem ordinary_failed_target_true (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (z : Fin k × Fin 2)
    (hz : z ∈ externalGuardCoordinates T label F t g q x)
    (hT : z.1 ∈ tolerantTargets T label F t g q x)
    (hU : z.1 ∉ positiveTargets T label F t g q x (by decide)) :
    F t (recursiveChild x z.1 z.2) = true := by
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
  have harc := (mem_guardArcs T label F t g q x e).mp (Finset.mem_filter.mp he).1
  have hgate := ((mem_failedGuards T label F g x e.1 e.2).mp harc.2).2
  cases ht : F t (recursiveChild x e.2 (label e.1 e.2))
  · have hsel := missingWitness_unique F t x (by decide) e.2
      (Finset.mem_filter.mp hT).2.1 (label e.1 e.2) ht
    apply False.elim
    apply hU
    apply Finset.mem_filter.mpr
    refine ⟨hT,?_⟩
    simpa only [arcCoordinate,←hsel] using hgate
  · exact ht

theorem crossedTargetHeads_cheap_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (crossedTargetHeads T label F t g q x).card ≤
      ((externalGuardCoordinates T label F t g q x).filter fun z =>
        z.1 ∉ positiveTargets T label F t g q x (by decide) ∧
          ¬ F t (recursiveChild x z.1 z.2) = false).card := by
  apply Finset.card_image_le.trans
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hz,hT,hU⟩ := Finset.mem_filter.mp hz
  refine Finset.mem_filter.mpr ⟨hz,hU,?_⟩
  have hon := ordinary_failed_target_true T label F t g q x z hz hT hU
  simp [hon]

theorem selected_guard_weak_true (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga q x = false)
    (e : Fin k × Fin k) (he : e ∈ guardArcs T label F tb gb q x) :
    F ga (recursiveChild x e.2 (label e.1 e.2)) = true := by
  have he' := (mem_guardArcs T label F tb gb q x e).mp he
  have hh := tolerant_guard_sets_eq T label F hF ta tb ga gb ht hg x q hx he'.1
  have hmem : e.2 ∈ failedGuards T label F ga x e.1 := by rw [hh]; exact he'.2
  exact ((mem_failedGuards T label F ga x e.1 e.2).mp hmem).2

theorem internal_guard_cost (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ) (j : ℕ) (hj : BBound F g t j)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (((internalGuardArcs T label F t g q x).image (arcCoordinate label)).biUnion
      (fun z => childFlipsTo F g false x z.1 z.2)).card ≤
      min ((tolerantGuards T label F t g q x).card.choose 2)
        (2*(tolerantGuards T label F t g q x).card)*j := by
  let R := tolerantGuards T label F t g q x
  let S := internalGuardArcs T label F t g q x
  let Z := S.image (arcCoordinate label)
  let D := fun z : Fin k × Fin 2 => childFlipsTo F g false x z.1 z.2
  have hhead : ∀ z ∈ Z, z.1 ∈ R := by
    intro z hz
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp he).2
  have hD : ∀ z ∈ Z, (D z).card ≤ j := by
    intro z hz
    have hon := (missingTargets_empty F t x z.1).mp (Finset.mem_filter.mp (hhead z hz)).2.1 z.2
    simpa only [D,childFlipsTo_card] using hj _ hon
  have hbyarc : (Z.biUnion D).card ≤ R.card.choose 2*j := by
    calc
      (Z.biUnion D).card ≤ ∑ z ∈ Z, (D z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ Z, j := Finset.sum_le_sum hD
      _ = Z.card*j := by simp
      _ ≤ S.card*j := Nat.mul_le_mul_right j Finset.card_image_le
      _ = R.card.choose 2*j := by rw [(guardArcs_card T label F hF t g hgt q x).2]
  have hbyhead : (Z.biUnion D).card ≤ (2*R.card)*j :=
    by_head_child_card R Z D j hhead hD
  rw [min_mul]
  exact le_min hbyarc hbyhead

theorem external_guard_cost (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hgbtb : gb ≤ tb)
    (q s j L : ℕ) (hjs : j ≤ s) (hs : BBound F gb ga s) (hj : BBound F gb tb j)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga q x = false)
    (hL : ((externalGuardArcs T label F tb gb q x).filter fun e =>
        e.2 ∉ positiveTargets T label F tb gb q x (by decide)).card+L ≤
      (externalGuardArcs T label F tb gb q x).card) :
    ((externalGuardCoordinates T label F tb gb q x).biUnion
      (fun z => childFlipsTo F gb false x z.1 z.2)).card ≤
      ((externalGuardArcs T label F tb gb q x).card-
        (L-(positiveTargets T label F tb gb q x (by decide)).card)-
        (crossedTargetHeads T label F tb gb q x).card)*s+
      (min (positiveTargets T label F tb gb q x (by decide)).card
        (L-(positiveTargets T label F tb gb q x (by decide)).card)+
        (crossedTargetHeads T label F tb gb q x).card)*j := by
  let Z := externalGuardCoordinates T label F tb gb q x
  let S := externalGuardArcs T label F tb gb q x
  let P := positiveTargets T label F tb gb q x (by decide)
  let D := fun z : Fin k × Fin 2 => childFlipsTo F gb false x z.1 z.2
  apply positive_union_charge Z (fun z => z.1 ∈ P)
    (fun z => F tb (recursiveChild x z.1 z.2) = false) D
    S.card ((S.filter fun e => e.2 ∉ P).card) L P.card
    (crossedTargetHeads T label F tb gb q x).card s j hjs
  · exact Finset.card_image_le
  · exact filter_image_card_le S (arcCoordinate label) (fun z => z.1 ∉ P)
  · exact hL
  · exact positive_coordinates_card P Z
  · exact positive_costly_coordinates_card T label F tb gb q x Z
  · exact crossedTargetHeads_cheap_card T label F tb gb q x
  · intro z hz
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    have hweak := selected_guard_weak_true T label F hF ta tb ga gb ht hg q x hx e
      (Finset.mem_filter.mp he).1
    by_cases hc : F tb (recursiveChild x e.2 (label e.1 e.2)) = false
    · simpa [D,arcCoordinate,hc] using hs _ hweak
    · have hon : F tb (recursiveChild x e.2 (label e.1 e.2)) = true := by
        simpa only [Bool.not_eq_false] using hc
      simpa [D,arcCoordinate,hc] using hj _ hon

end ZT
end
end z37

section z40

set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators

namespace ZT
variable {n k : ℕ} {I : Type}

theorem target_guard_disjoint (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (t g : Fin n) (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool) :
    Disjoint (tolerantTargets T label F t g q x)
      (tolerantGuards T label F t g q x) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hone := (Finset.mem_filter.mp hi).2.1
  have hempty := (Finset.mem_filter.mp hj).2.1
  simp only [hempty, Finset.card_empty] at hone
  omega

theorem positive_or_guard_full (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool)
    (j : Fin k)
    (hj : j ∈ SensitivityQ.positiveTargets T label F t g q x (by decide) ∪
      tolerantGuards T label F t g q x) :
    ∀ c, F g (recursiveChild x j c) = true := by
  intro c
  rcases Finset.mem_union.mp hj with hp | hg
  · obtain ⟨hjt,hgate⟩ := Finset.mem_filter.mp hp
    by_cases hc : c = missingWitness F t x (by decide) j
    · simpa only [hc] using hgate
    · exact hF.accepts_of_le hgt
        (missingWitness_other_true F t x (by decide) j
          (Finset.mem_filter.mp hjt).2.1 c hc)
  · exact hF.accepts_of_le hgt
      ((missingTargets_empty F t x j).mp (Finset.mem_filter.mp hg).2.1 c)

theorem target_mismatch_failed (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool)
    (A : Finset (Fin k)) (hA : A ⊆ tolerantTargets T label F t g q x)
    (i : Fin k) :
    ZL.mismatch T.Adj (fun e => label e.1 e.2) A
      (missingWitness F t x (by decide)) i ⊆ failedGuards T label F g x i := by
  intro j hj
  obtain ⟨hjA,hij,hl⟩ := Finset.mem_filter.mp hj
  exact (mem_failedGuards T label F g x i j).mpr ⟨hij,
    hF.accepts_of_le hgt (missingWitness_other_true F t x (by decide) j
      (Finset.mem_filter.mp (hA hjA)).2.1 _ hl)⟩

theorem targets_ordinaryGood (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool) :
    ZL.OrdinaryGood T.Adj (fun e => label e.1 e.2)
      (tolerantTargets T label F t g q x) q (missingWitness F t x (by decide)) := by
  intro i hi
  exact (Finset.card_le_card
    (target_mismatch_failed T label F hF t g hgt q x _ (fun _ h => h) i)).trans
    (Finset.mem_filter.mp hi).2.2

theorem candidate_local_charge (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool)
    (A M : Finset (Fin k)) (hA : A ⊆ tolerantTargets T label F t g q x)
    (hM : M ⊆ SensitivityQ.positiveTargets T label F t g q x (by decide) ∪
      tolerantGuards T label F t g q x) (hdis : Disjoint A M) (i : Fin k) :
    (ZL.mismatch T.Adj (fun e => label e.1 e.2) A
      (missingWitness F t x (by decide)) i).card +
      (ZL.outOn T.Adj M i).card ≤ (failedGuards T label F g x i).card := by
  let D := ZL.mismatch T.Adj (fun e => label e.1 e.2) A
    (missingWitness F t x (by decide)) i
  let O := ZL.outOn T.Adj M i
  have hD : D ⊆ failedGuards T label F g x i :=
    target_mismatch_failed T label F hF t g hgt q x A hA i
  have hO : O ⊆ failedGuards T label F g x i := by
    intro j hj
    obtain ⟨hjM,hij⟩ := Finset.mem_filter.mp hj
    exact (mem_failedGuards T label F g x i j).mpr
      ⟨hij, positive_or_guard_full T label F hF t g hgt q x j (hM hjM) _⟩
  have hd : Disjoint D O := by
    apply Finset.disjoint_left.mpr
    intro j hjD hjO
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_filter.mp hjD).1 (Finset.mem_filter.mp hjO).1
  calc
    D.card + O.card = (D ∪ O).card := (Finset.card_union_of_disjoint hd).symm
    _ ≤ (failedGuards T label F g x i).card :=
      Finset.card_le_card (Finset.union_subset hD hO)

theorem candidates_markedGood (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q B : ℕ) (x : ((Fin k × Fin 2) × I) → Bool)
    (A M P : Finset (Fin k)) (hA : A ⊆ tolerantTargets T label F t g q x)
    (hM : M ⊆ SensitivityQ.positiveTargets T label F t g q x (by decide) ∪
      tolerantGuards T label F t g q x)
    (hP : P ⊆ SensitivityQ.positiveTargets T label F t g q x (by decide))
    (hdis : Disjoint A M)
    (hB : (∑ y ∈ M, (ZL.mismatch T.Adj
      (fun e => label e.1 e.2) A (missingWitness F t x (by decide)) y).card) ≤ B) :
    ZL.MarkedGood T.Adj (fun e => label e.1 e.2)
      A M P q B (missingWitness F t x (by decide)) := by
  refine ⟨?_,?_,hB⟩
  · intro i hi
    exact (candidate_local_charge T label F hF t g hgt q x A M hA hM hdis i).trans
      (Finset.mem_filter.mp (hA hi)).2.2
  · intro i hi
    have hcharge := candidate_local_charge T label F hF t g hgt q x A M hA hM hdis i
    rw [Nat.add_comm] at hcharge
    by_cases hip : i ∈ P
    · simp only [if_pos hip, Nat.add_zero]
      exact hcharge.trans (Finset.mem_filter.mp (Finset.mem_filter.mp (hP hip)).1).2.2
    · simp only [if_neg hip]
      rcases Finset.mem_union.mp (hM hi) with hiU | hiG
      · have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hiU).1).2.2
        omega
      · have hh := (Finset.mem_filter.mp hiG).2.2
        omega

theorem targets_card_of_exclusion (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q w : ℕ) (hd : SensitivityQ.DefectBound T label q w)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (tolerantTargets T label F t g q x).card < w := by
  exact hd _ _ (targets_ordinaryGood T label F hF t g hgt q x)



end ZT
end
end z40

section z41

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



theorem crossedTargetHeads_subset (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    crossedTargetHeads T label F t g q x ⊆
      tolerantTargets T label F t g q x \ positiveTargets T label F t g q x (by decide) := by
  intro v hv
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_sdiff.mpr (Finset.mem_filter.mp hz).2

theorem crossedTargetHeads_of_failed (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (v w : Fin k)
    (hv : v ∈ tolerantGuards T label F t g q x)
    (hw : w ∈ tolerantTargets T label F t g q x)
    (hP : w ∉ positiveTargets T label F t g q x (by decide))
    (hfailed : w ∈ failedGuards T label F g x v) :
    w ∈ crossedTargetHeads T label F t g q x := by
  have hwG : w ∉ tolerantGuards T label F t g q x := by
    exact Finset.disjoint_left.mp (target_guard_disjoint T label F t g q x) hw
  have hext : (v,w) ∈ externalGuardArcs T label F t g q x :=
    Finset.mem_filter.mpr ⟨(mem_guardArcs _ _ _ _ _ _ _ _).mpr ⟨hv,hfailed⟩,hwG⟩
  exact Finset.mem_image.mpr ⟨(w,label v w),Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨(v,w),hext,rfl⟩,hw,hP⟩,rfl⟩

theorem remaining_targets_subset (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    remainingOrdinaryTargets T label F t g q x ⊆ tolerantTargets T label F t g q x := by
  intro v hv
  exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).1

theorem remaining_targets_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (remainingOrdinaryTargets T label F t g q x).card+
      (crossedTargetHeads T label F t g q x).card+
      (positiveTargets T label F t g q x (by decide)).card =
      (tolerantTargets T label F t g q x).card := by
  have hC := Finset.card_sdiff_add_card_eq_card (crossedTargetHeads_subset T label F t g q x)
  have hP := Finset.card_sdiff_add_card_eq_card
    (show positiveTargets T label F t g q x (by decide) ⊆ tolerantTargets T label F t g q x from
      Finset.filter_subset _ _)
  change (remainingOrdinaryTargets T label F t g q x).card+_=_ at hC
  omega

theorem remaining_targets_guard_mismatch_empty (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k)
    (hv : v ∈ tolerantGuards T label F t g q x) :
    ZL.mismatch T.Adj (fun e => label e.1 e.2)
      (remainingOrdinaryTargets T label F t g q x) (missingWitness F t x (by decide)) v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hfailed := target_mismatch_failed T label F hF t g hgt q x
    (remainingOrdinaryTargets T label F t g q x) (remaining_targets_subset T label F t g q x) v hw
  have hrem := (Finset.mem_filter.mp hw).1
  obtain ⟨hord,hnotC⟩ := Finset.mem_sdiff.mp hrem
  obtain ⟨hT,hnotP⟩ := Finset.mem_sdiff.mp hord
  exact hnotC (crossedTargetHeads_of_failed T label F t g q x v w hv hT hnotP hfailed)



theorem remaining_targets_marked_zero_all (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    let P := positiveTargets T label F t g 0 x (by decide)
    let G := tolerantGuards T label F t g 0 x
    ZL.MarkedGood T.Adj (fun e => label e.1 e.2)
      (remainingOrdinaryTargets T label F t g 0 x) (P ∪ G) P 0 0
      (missingWitness F t x (by decide)) := by
  let A := remainingOrdinaryTargets T label F t g 0 x
  let P := positiveTargets T label F t g 0 x (by decide)
  let G := tolerantGuards T label F t g 0 x
  apply candidates_markedGood T label F hF t g hgt 0 0 x A (P ∪ G) P
    (remaining_targets_subset T label F t g 0 x) (Finset.Subset.refl _) (Finset.Subset.refl _)
  · apply Finset.disjoint_left.mpr
    intro v hv hmark
    rcases Finset.mem_union.mp hmark with hp | hg
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2 hp
    · exact Finset.disjoint_left.mp (target_guard_disjoint T label F t g 0 x)
        (remaining_targets_subset T label F t g 0 x hv) hg
  · have hempty : ∀ v ∈ P ∪ G, ZL.mismatch T.Adj (fun e => label e.1 e.2)
        A (missingWitness F t x (by decide)) v = ∅ := by
      intro v hv
      rcases Finset.mem_union.mp hv with hp | hg
      · have hsub := target_mismatch_failed T label F hF t g hgt 0 x A
          (remaining_targets_subset T label F t g 0 x) v
        have hz : failedGuards T label F g x v = ∅ := by
          apply Finset.card_eq_zero.mp
          have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
          omega
        exact Finset.eq_empty_iff_forall_notMem.mpr (by
          intro w hw
          have hh := hsub hw
          simpa only [hz,Finset.notMem_empty] using hh)
      · exact remaining_targets_guard_mismatch_empty T label F hF t g hgt 0 x v hg
    exact (show (∑ v ∈ P ∪ G, (ZL.mismatch T.Adj (fun e => label e.1 e.2)
      A (missingWitness F t x (by decide)) v).card)=0 by
        apply Finset.sum_eq_zero
        intro v hv
        rw [hempty v hv]
        rfl).le

end ZT
end
end z41

section z42

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 ZL

namespace ZT
variable {k : ℕ}

theorem zero_marked_domination (T : Tournament k) (ell : Fin k × Fin k → Fin 2)
    (A M P : Finset (Fin k)) (color : Fin k → Fin 2)
    (hdis : Disjoint A M) (hgood : MarkedGood T.Adj ell A M P 0 0 color) :
    ∀ i ∈ M, ∀ j ∈ A, T.Adj i j := by
  intro i hi j hj
  have hne : i ≠ j := by
    intro he
    subst j
    exact Finset.disjoint_left.mp hdis hj hi
  apply (T.adj_or_reverse hne).resolve_right
  intro hji
  have hmem : i ∈ outOn T.Adj M j := Finset.mem_filter.mpr ⟨hi,hji⟩
  have hp := Finset.card_pos.mpr ⟨i,hmem⟩
  have hz := hgood.1 j hj
  omega

theorem zero_marked_coherent (T : Tournament k) (ell : Fin k × Fin k → Fin 2)
    (A M P : Finset (Fin k)) (color : Fin k → Fin 2)
    (hgood : MarkedGood T.Adj ell A M P 0 0 color) :
    Coherent T.Adj ell A M color := by
  intro e he
  rcases Finset.mem_union.mp he with heA | heM
  · obtain ⟨heprod,hedge⟩ := Finset.mem_filter.mp heA
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp heprod
    by_contra hn
    have hp := Finset.card_pos.mpr (⟨e.2,Finset.mem_filter.mpr ⟨hy,hedge,hn⟩⟩ :
      (mismatch T.Adj ell A color e.1).Nonempty)
    have hz := hgood.1 e.1 hx
    omega
  · obtain ⟨heprod,hedge⟩ := Finset.mem_filter.mp heM
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp heprod
    by_contra hn
    have hp := Finset.card_pos.mpr (⟨e.2,Finset.mem_filter.mpr ⟨hy,hedge,hn⟩⟩ :
      (mismatch T.Adj ell A color e.1).Nonempty)
    have hs : (mismatch T.Adj ell A color e.1).card ≤
        ∑ i ∈ M, (mismatch T.Adj ell A color i).card :=
      Finset.single_le_sum (f := fun i => (mismatch T.Adj ell A color i).card)
        (fun _ _ => Nat.zero_le _) hx
    have hz := hgood.2.2
    omega

theorem zero_marked_twoDominator (T : Tournament k)
    (ell : Fin k × Fin k → Fin 2) (A M P M' : Finset (Fin k))
    (color : Fin k → Fin 2) (hdis : Disjoint A M)
    (hgood : MarkedGood T.Adj ell A M P 0 0 color)
    (hsub : M' ⊆ M) (hcard : M'.card = 2) :
    TwoDominatorGood T.Adj ell A M' color := by
  refine ⟨hdis.mono_right hsub,hcard,?_,?_⟩
  · exact fun i hi j hj => zero_marked_domination T ell A M P color hdis hgood i (hsub hi) j hj
  · intro e he
    apply zero_marked_coherent T ell A M P color hgood
    rcases Finset.mem_union.mp he with heA | heM
    · exact Finset.mem_union_left _ heA
    · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp heM
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hsub (Finset.mem_product.mp hp).1,
          (Finset.mem_product.mp hp).2⟩,hr⟩)

theorem zero_marked_source_card (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (A M P : Finset (Fin k))
    (color : Fin k → Fin 2) (hdis : Disjoint A M)
    (hgood : MarkedGood T.Adj (fun e => label e.1 e.2) A M P 0 0 color)
    (hne : M.Nonempty) (w : ℕ) (hsource : SensitivitySourceZero.SourceBound T label w) :
    A.card + 1 < w := by
  obtain ⟨i,hi⟩ := hne
  have hinot : i ∉ A := fun h => Finset.disjoint_left.mp hdis h hi
  have hdom := zero_marked_domination T (fun e => label e.1 e.2) A M P color hdis hgood
  have hcoh := zero_marked_coherent T (fun e => label e.1 e.2) A M P color hgood
  have hlocal : ∀ u ∈ insert i A, ∀ v ∈ insert i A,
      T.Adj u v → label u v = color v := by
    intro u hu v hv huv
    have hvA : v ∈ A := by
      rcases Finset.mem_insert.mp hv with he | hvA
      · subst v
        rcases Finset.mem_insert.mp hu with he | huA
        · exact False.elim (T.ne_of_adj huv he)
        · exact False.elim (T.not_adj_reverse (hdom i hi u huA) huv)
      · exact hvA
    rcases Finset.mem_insert.mp hu with he | huA
    · subst u
      exact hcoh (i,v) (Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hi,hvA⟩,huv⟩))
    · exact hcoh (u,v) (Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨huA,hvA⟩,huv⟩))
  have hs : SensitivitySourceZero.HasSource T (insert i A) := by
    refine ⟨i,Finset.mem_insert_self _ _,?_⟩
    intro j hj hji
    exact hdom i hi j ((Finset.mem_insert.mp hj).resolve_left hji)
  have hd : ∀ u ∈ insert i A,
      ((insert i A).filter fun v => T.Adj u v ∧ label u v ≠ color v).card ≤ 0 := by
    intro u hu
    have hempty : (insert i A).filter (fun v => T.Adj u v ∧ label u v ≠ color v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hvA,huv,hn⟩ := Finset.mem_filter.mp hv
      exact hn (hlocal u hu v hvA huv)
    simp only [hempty, Finset.card_empty, le_refl]
  have hh := hsource (insert i A) color hs hd
  simpa only [Finset.card_insert_of_notMem hinot] using hh

end ZT
end
end z42

section z43

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ ZL
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]















theorem remaining_card_source_zero (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (w : ℕ)
    (hsource : SensitivitySourceZero.SourceBound T label w)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hne : (positiveTargets T label F t g 0 x (by decide) ∪ tolerantGuards T label F t g 0 x).Nonempty) :
    (remainingOrdinaryTargets T label F t g 0 x).card+1 < w := by
  let A := remainingOrdinaryTargets T label F t g 0 x
  let P := positiveTargets T label F t g 0 x (by decide)
  let G := tolerantGuards T label F t g 0 x
  have hdis : Disjoint A (P ∪ G) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    rcases Finset.mem_union.mp hw with hp | hg
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2 hp
    · exact Finset.disjoint_left.mp (target_guard_disjoint T label F t g 0 x)
        (remaining_targets_subset T label F t g 0 x hv) hg
  exact zero_marked_source_card T label A (P ∪ G) P _ hdis
    (remaining_targets_marked_zero_all T label F hF t g hgt x) hne w hsource

theorem remaining_card_double_zero (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (w : ℕ) (hdouble : DoubleCardBound T label w)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hne : 2 ≤ (positiveTargets T label F t g 0 x (by decide) ∪ tolerantGuards T label F t g 0 x).card) :
    (remainingOrdinaryTargets T label F t g 0 x).card < w := by
  let A := remainingOrdinaryTargets T label F t g 0 x
  let P := positiveTargets T label F t g 0 x (by decide)
  let G := tolerantGuards T label F t g 0 x
  have hdis : Disjoint A (P ∪ G) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    rcases Finset.mem_union.mp hw with hp | hg
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2 hp
    · exact Finset.disjoint_left.mp (target_guard_disjoint T label F t g 0 x)
        (remaining_targets_subset T label F t g 0 x hv) hg
  obtain ⟨M',hM',hc⟩ := Finset.exists_subset_card_eq hne
  exact hdouble A M' _ (zero_marked_twoDominator T (fun e => label e.1 e.2) A (P ∪ G) P M' _
    hdis (remaining_targets_marked_zero_all T label F hF t g hgt x) hM' hc)

end ZT
end
end z43

section z58

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ SensitivityOrdinaryGuard
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

theorem external_outside_positive_budget (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    let G := tolerantGuards T label F t g q x
    let P := positiveTargets T label F t g q x (by decide)
    let S := externalGuardArcs T label F t g q x
    ((S.filter fun e => e.2 ∉ P).card)+
      ((P.card*G.card+P.card.choose 2)-q*P.card) ≤ S.card := by
  let G := tolerantGuards T label F t g q x
  let P := positiveTargets T label F t g q x (by decide)
  let B := failedGuards T label F g x
  let O := fun v => (B v).filter fun w => w ∉ G
  let S := externalGuardArcs T label F t g q x
  let W := (S.filter fun e => e.2 ∉ P).card
  have hWcount : W = ∑ v ∈ G, ((O v).filter fun w => w ∉ P).card := by
    simp only [W,S,externalGuardArcs,guardArcs,Finset.card_eq_sum_ones,
      Finset.sum_filter,Finset.sum_product,O]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hg : w ∈ G <;> by_cases hp : w ∈ P <;> simp [G,hg,hp]
  have hinside : ∀ v, (P ∪ G).filter (T.Adj v) ⊆ B v := by
    intro v w hw
    obtain ⟨hw,hadj⟩ := Finset.mem_filter.mp hw
    apply (mem_failedGuards T label F g x v w).mpr
    refine ⟨hadj,?_⟩
    rcases Finset.mem_union.mp hw with hw | hw
    · exact positive_gate_true T label F hF t g hgt q x (by decide) w hw _
    · exact hF.accepts_of_le hgt
        ((missingTargets_empty F t x w).mp (Finset.mem_filter.mp hw).2.1 _)
  have hP : ∀ v ∈ P, (B v).card ≤ q := by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2.2
  have hG : ∀ v ∈ G, (B v).card = q+1 := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2.2
  have hbudget := tournament_outside_budget T P G B O q
    (positive_guards_disjoint T label F t g q x (by decide)) hinside hP hG
    (fun _ => Finset.filter_subset _ _) (by
      intro v w hw
      exact (Finset.mem_filter.mp hw).2)
  rw [←hWcount] at hbudget
  have hS : S.card = G.card*(q+1)-G.card.choose 2 :=
    (guardArcs_card T label F hF t g hgt q x).1
  have hW : W ≤ G.card*(q+1)-G.card.choose 2 := by
    rw [←hS]
    exact Finset.card_filter_le _ _
  change W+((P.card*G.card+P.card.choose 2)-q*P.card) ≤ S.card
  rw [hS]
  exact positive_lower_budget q P.card G.card W hW hbudget

end ZT
end
end z58

section z60

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



theorem crossedTargetHeads_budget (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    let G := tolerantGuards T label F t g q x
    let P := positiveTargets T label F t g q x (by decide)
    (crossedTargetHeads T label F t g q x).card+
      ((P.card*G.card+P.card.choose 2)-q*P.card) ≤
      G.card*(q+1)-G.card.choose 2 := by
  let G := tolerantGuards T label F t g q x
  let P := positiveTargets T label F t g q x (by decide)
  let S := externalGuardArcs T label F t g q x
  let Z := externalGuardCoordinates T label F t g q x
  have hcheap := crossedTargetHeads_cheap_card T label F t g q x
  have hout : (Z.filter fun z => z.1 ∉ P ∧ ¬ F t (recursiveChild x z.1 z.2) = false).card ≤
      (S.filter fun e => e.2 ∉ P).card := by
    apply (Finset.card_le_card ?_).trans
      (filter_image_card_le S (arcCoordinate label) (fun z => z.1 ∉ P))
    intro z hz
    obtain ⟨hz,hp,_⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz,hp⟩
  have hδ := hcheap.trans hout
  have hL := external_outside_positive_budget T label F hF t g hgt q x
  have hc := (guardArcs_card T label F hF t g hgt q x).1
  change S.card = G.card*(q+1)-G.card.choose 2 at hc
  change (S.filter fun e => e.2 ∉ P).card+
    ((P.card*G.card+P.card.choose 2)-q*P.card) ≤ S.card at hL
  change (crossedTargetHeads T label F t g q x).card+
    ((P.card*G.card+P.card.choose 2)-q*P.card) ≤ G.card*(q+1)-G.card.choose 2
  rw [←hc]
  exact (Nat.add_le_add_right hδ _).trans hL

theorem ordinary_zero_candidate_cost (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (q a b s j : ℕ) (hjs : j ≤ s)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (hs : BBound F gb ga s) (hj : BBound F gb tb j)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga q x = false) :
    (flipsTo (tolerantFamily T label F tb gb q) true x).card ≤
      candidateCost q (tolerantTargets T label F tb gb q x).card
        (positiveTargets T label F tb gb q x (by decide)).card
        (tolerantGuards T label F tb gb q x).card
        (crossedTargetHeads T label F tb gb q x).card a b s j := by
  let TC := tolerantTargets T label F tb gb q x
  let P := positiveTargets T label F tb gb q x (by decide)
  let G := tolerantGuards T label F tb gb q x
  let δ := (crossedTargetHeads T label F tb gb q x).card
  let E := G.card*(q+1)-G.card.choose 2
  let L := (P.card*G.card+P.card.choose 2)-q*P.card
  let intr := min (G.card.choose 2) (2*G.card)
  let X := (externalGuardCoordinates T label F tb gb q x).biUnion
    (fun z => childFlipsTo F gb false x z.1 z.2)
  let Y := ((internalGuardArcs T label F tb gb q x).image (arcCoordinate label)).biUnion
    (fun z => childFlipsTo F gb false x z.1 z.2)
  have hgt : gb ≤ tb := hg.trans (hga.trans ht)
  have hX : X.card ≤ (E-(L-P.card)-δ)*s+(min P.card (L-P.card)+δ)*j := by
    have hh := external_guard_cost T label F hF ta tb ga gb ht hg hgt q s j L
      hjs hs hj x hx (external_outside_positive_budget T label F hF tb gb hgt q x)
    rw [(guardArcs_card T label F hF tb gb hgt q x).1] at hh
    exact hh
  have hY : Y.card ≤ intr*j := internal_guard_cost T label F hF tb gb hgt q j hj x
  have hG : (guardRepairs T label F tb gb q x).card ≤
      (E-(L-P.card)-δ)*s+(intr+min P.card (L-P.card)+δ)*j := by
    have hh := (Finset.card_le_card (guardRepairs_subset_coordinates T label F tb gb q x)).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add hX hY))
    simpa only [Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
  have hT := targetRepairs_card T label F hF ta tb ga gb ht hg q q (le_refl q) a b ha hb x hx
  have hoff : tolerantFamily T label F tb gb q x = false := by
    cases hh : tolerantFamily T label F tb gb q x
    · rfl
    · have hw := family_nested T label F hF ht hg (le_refl q) x hh
      simp [hx] at hw
  have hh := (Finset.card_le_card (up_subset_repairs T label F tb gb q x hoff)).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hT hG))
  simpa only [candidateCost,Nat.add_assoc] using hh





end ZT
end
end z60

section z62

set_option maxHeartbeats 5000000
namespace ZT



theorem zeroCost_lower (a b s j d : ℕ) :
    23*b ≤ zeroCost a b s j d ∧ a+20*b ≤ zeroCost a b s j d ∧
    17*b+max (min (a+s) d) (a+j) ≤ zeroCost a b s j d ∧
    20*b+s ≤ zeroCost a b s j d ∧ 21*b+j ≤ zeroCost a b s j d ∧
    17*b+s+j ≤ zeroCost a b s j d ∧ 18*b+2*j ≤ zeroCost a b s j d ∧
    17*b+3*j ≤ zeroCost a b s j d := by unfold zeroCost; omega

theorem zero_candidate_cases (z t u m δ a b s j d : ℕ)
    (hu : u ≤ 1) (hm : m ≤ 3) (hc : (u+m).choose 2 ≤ m)
    (ht : t ≤ 23)
    (hδ : δ+((u*m+u.choose 2)-0*u) ≤ m*(0+1)-m.choose 2)
    (hsource : 1 ≤ u+m → t-u ≤ 20+δ)
    (hdouble : 2 ≤ u+m → t-u ≤ 17+δ)
    (hraw : z ≤ candidateCost 0 t u m δ a b s j)
    (hshared : u=1 → m=1 → z ≤ (t-1)*b+max (min (a+s) d) (a+j)) :
    z ≤ zeroCost a b s j d := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := zeroCost_lower a b s j d
  interval_cases u
  · interval_cases m
    · have hd : δ=0 := by norm_num at hδ; omega
      subst δ
      norm_num [candidateCost] at hraw
      exact (hraw.trans (Nat.mul_le_mul_right b ht)).trans h0
    · have hd : δ ≤ 1 := by norm_num at hδ; exact hδ
      have hs := hsource (by decide)
      norm_num at hs
      interval_cases δ
      · norm_num [candidateCost] at hraw
        have hb := Nat.mul_le_mul_right b hs
        exact (by omega : z ≤ 20*b+s).trans h3
      · norm_num [candidateCost] at hraw
        have hb := Nat.mul_le_mul_right b hs
        exact (by omega : z ≤ 21*b+j).trans h4
    · have hd : δ ≤ 1 := by norm_num at hδ; exact hδ
      have hs := hdouble (by decide)
      norm_num at hs
      interval_cases δ
      · norm_num [candidateCost] at hraw
        have hb := Nat.mul_le_mul_right b hs
        exact (by omega : z ≤ 17*b+s+j).trans h5
      · norm_num [candidateCost] at hraw
        have hb := Nat.mul_le_mul_right b hs
        exact (by omega : z ≤ 18*b+2*j).trans h6
    · have hd : δ=0 := by norm_num at hδ; omega
      subst δ
      have hs := hdouble (by decide)
      norm_num at hs
      norm_num [candidateCost] at hraw
      have hb := Nat.mul_le_mul_right b hs
      exact (by omega : z ≤ 17*b+3*j).trans h7
  · interval_cases m
    · have hd : δ=0 := by norm_num at hδ; omega
      subst δ
      have hs : t-1 ≤ 20 := by simpa only [Nat.add_zero] using hsource (by decide)
      norm_num [candidateCost] at hraw
      have hb := Nat.mul_le_mul_right b hs
      exact (by omega : z ≤ a+20*b).trans h1
    · have hd : δ=0 := by norm_num at hδ; omega
      subst δ
      have hs : t-1 ≤ 17 := by simpa only [Nat.add_zero] using hdouble (by decide)
      have hr := hshared rfl rfl
      have hb := Nat.mul_le_mul_right b hs
      exact (by omega : z ≤ 17*b+max (min (a+s) d) (a+j)).trans h2
    · norm_num [Nat.choose] at hc
    · norm_num [Nat.choose] at hc



end ZT
end z62

section z63

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ SensitivitySourceZero
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

theorem childFlips_union_card (F : Fin n → (I → Bool) → Bool) (g t : Fin n)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k) (c : Fin 2) :
    (childFlipsTo F t true x v c ∪ childFlipsTo F g false x v c).card =
      (flipsTo (F g) false (recursiveChild x v c) ∪
        flipsTo (F t) true (recursiveChild x v c)).card := by
  rw [Finset.union_comm]
  change ((childLift (v,c) (flipsTo (F g) false (recursiveChild x v c))) ∪
    childLift (v,c) (flipsTo (F t) true (recursiveChild x v c))).card = _
  rw [show childLift (v,c) (flipsTo (F g) false (recursiveChild x v c)) ∪
      childLift (v,c) (flipsTo (F t) true (recursiveChild x v c)) =
      childLift (v,c) (flipsTo (F g) false (recursiveChild x v c) ∪
        flipsTo (F t) true (recursiveChild x v c)) by
    simp only [childLift,Finset.map_union]]
  exact childLift_card _ _

theorem zero_shared_target_guard (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (a b s j d : ℕ) (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (hs : BBound F gb ga s) (hj : BBound F gb tb j) (hd : DBound F gb ga ta tb d)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga 0 x = false)
    (u v : Fin k)
    (hU : positiveTargets T label F tb gb 0 x (by decide) = {u})
    (hG : tolerantGuards T label F tb gb 0 x = {v}) :
    (flipsTo (tolerantFamily T label F tb gb 0) true x).card ≤
      ((tolerantTargets T label F tb gb 0 x).card-1)*b+
        max (min (a+s) d) (a+j) := by
  let TC := tolerantTargets T label F tb gb 0 x
  let tw := missingWitness F tb x (by decide)
  let Q := (TC.erase u).biUnion fun w => childFlipsTo F tb true x w (tw w)
  let A := childFlipsTo F tb true x u (tw u)
  let B := childFlipsTo F gb false x u (label v u)
  have huU : u ∈ positiveTargets T label F tb gb 0 x (by decide) := by rw [hU]; simp
  have huT : u ∈ TC := (Finset.mem_filter.mp huU).1
  have hgb : F gb (recursiveChild x u (tw u)) = true := (Finset.mem_filter.mp huU).2
  have hta := tolerant_target_weak_false T label F hF ta tb ga gb ht hg x (le_refl 0)
    (by decide) hx huT
  have hvG : v ∈ tolerantGuards T label F tb gb 0 x := by rw [hG]; simp
  have hvu : T.Adj v u := guard_dominates_target_zero T label F hF tb gb
    (hg.trans (hga.trans ht)) x v u hvG huT
  have hfull : ∀ c, F gb (recursiveChild x u c) = true :=
    SensitivityOrdinaryGuard.positive_gate_true T label F hF tb gb (hg.trans (hga.trans ht))
      0 x (by decide) u huU
  have hufailed : u ∈ failedGuards T label F gb x v :=
    (mem_failedGuards T label F gb x v u).mpr ⟨hvu,hfull _⟩
  have hfailed : failedGuards T label F gb x v = {u} := by
    have hc : (failedGuards T label F gb x v).card = 1 := by
      simpa using (Finset.mem_filter.mp hvG).2.2
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hufailed,fun w hw => by
      obtain ⟨w₀,hw₀⟩ := Finset.card_eq_one.mp hc
      have he : u = w₀ := by simpa [hw₀] using hufailed
      simpa [hw₀,←he] using hw⟩
  have hguard : guardRepairs T label F tb gb 0 x = B := by
    simp [guardRepairs,hG,hfailed,B]
  have hweak : F ga (recursiveChild x u (label v u)) = true :=
    selected_guard_weak_true T label F hF ta tb ga gb ht hg 0 x hx (v,u)
      ((mem_guardArcs _ _ _ _ _ _ _ _).mpr ⟨hvG,hufailed⟩)
  have hQ : Q.card ≤ (TC.card-1)*b := by
    have hh : Q.card ≤ (TC.erase u).card*b := by
      apply card_biUnion_le_mul
      intro w hw
      have hwT := Finset.mem_of_mem_erase hw
      have hwne := Finset.ne_of_mem_erase hw
      have hnot : w ∉ positiveTargets T label F tb gb 0 x (by decide) := by
        simpa [hU] using hwne
      have hfalse : F gb (recursiveChild x w (tw w)) = false := by
        have hn : ¬ F gb (recursiveChild x w (tw w)) = true := by
          intro hon
          exact hnot (Finset.mem_filter.mpr ⟨hwT,hon⟩)
        simpa only [Bool.not_eq_true] using hn
      simpa only [childFlipsTo_card] using hb _ hfalse
    simpa [Finset.card_erase_of_mem huT] using hh
  have hA : A.card ≤ a := by simpa only [A,childFlipsTo_card] using ha _ hgb hta
  have hAB : (A ∪ B).card ≤ max (min (a+s) d) (a+j) := by
    by_cases hc : label v u = tw u
    · have hB : B.card ≤ s := by simpa only [B,childFlipsTo_card] using hs _ hweak
      have hab : (A ∪ B).card ≤ a+s :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add hA hB)
      have hd' : (A ∪ B).card ≤ d := by
        have hweak' : F ga (recursiveChild x u (tw u)) = true := by simpa [hc] using hweak
        simpa only [A,B,hc,childFlips_union_card] using hd _ hweak' hta
      exact (le_min hab hd').trans (le_max_left _ _)
    · have htrue : F tb (recursiveChild x u (label v u)) = true :=
        missingWitness_other_true F tb x (by decide) u (Finset.mem_filter.mp huT).2.1 _ hc
      have hB : B.card ≤ j := by simpa only [B,childFlipsTo_card] using hj _ htrue
      exact ((Finset.card_union_le _ _).trans (Nat.add_le_add hA hB)).trans (le_max_right _ _)
  have hfalse : tolerantFamily T label F tb gb 0 x = false := by
    cases hh : tolerantFamily T label F tb gb 0 x
    · rfl
    · have hw := family_nested T label F hF ht hg (le_refl 0) x hh
      simp [hx] at hw
  have hcover : flipsTo (tolerantFamily T label F tb gb 0) true x ⊆ Q ∪ (A ∪ B) := by
    intro p hp
    rcases Finset.mem_union.mp (up_subset_repairs T label F tb gb 0 x hfalse hp) with htar | hgr
    · obtain ⟨w,hw,hp⟩ := Finset.mem_biUnion.mp htar
      by_cases he : w = u
      · subst w
        exact Finset.mem_union_right _ (Finset.mem_union_left _ hp)
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨w,Finset.mem_erase.mpr ⟨he,hw⟩,hp⟩)
    · rw [hguard] at hgr
      exact Finset.mem_union_right _ (Finset.mem_union_right _ hgr)
  exact (Finset.card_le_card hcover).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hQ hAB))

end ZT
end
end z63

section z64

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

theorem _root_.solution (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (a b s j d : ℕ) (hjs : j ≤ s)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (hs : BBound F gb ga s) (hj : BBound F gb tb j) (hd : DBound F gb ga ta tb d)
    (hordinary : DefectBound T label 0 24)
    (hsource : SensitivitySourceZero.SourceBound T label 22)
    (hdouble : DoubleCardBound T label 18)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga 0 x = false) :
    (flipsTo (tolerantFamily T label F tb gb 0) true x).card ≤ zeroCost a b s j d := by
  let TC := tolerantTargets T label F tb gb 0 x
  let P := positiveTargets T label F tb gb 0 x (by decide)
  let G := tolerantGuards T label F tb gb 0 x
  let δ := (crossedTargetHeads T label F tb gb 0 x).card
  have hgt : gb ≤ tb := hg.trans (hga.trans ht)
  have hpart := remaining_targets_card T label F tb gb 0 x
  have hmark : (P ∪ G).card=P.card+G.card :=
    Finset.card_union_of_disjoint (SensitivityOrdinaryGuard.positive_guards_disjoint
      T label F tb gb 0 x (by decide))
  have hu : P.card ≤ 1 := by simpa using positiveTargets_card T label F hF tb gb hgt 0 x (by decide)
  have hm : G.card ≤ 3 := by simpa using guards_card T label F hF tb gb hgt 0 x
  have hc : (P.card+G.card).choose 2 ≤ G.card := by
    simpa using positiveTargets_guards_coupling T label F hF tb gb hgt 0 x (by decide)
  have htcard : TC.card ≤ 23 := by
    have hh := targets_card_of_exclusion T label F hF tb gb hgt 0 24 hordinary x
    change TC.card < 24 at hh
    omega
  have hδ := crossedTargetHeads_budget T label F hF tb gb hgt 0 x
  have hsrc : 1 ≤ P.card+G.card → TC.card-P.card ≤ 20+δ := by
    intro hn
    have hne : (P ∪ G).Nonempty := Finset.card_pos.mp (by rw [hmark]; omega)
    have hh := remaining_card_source_zero T label F hF tb gb hgt 22 hsource x hne
    change (remainingOrdinaryTargets T label F tb gb 0 x).card+δ+P.card=TC.card at hpart
    omega
  have hdbl : 2 ≤ P.card+G.card → TC.card-P.card ≤ 17+δ := by
    intro hn
    have hne : 2 ≤ (P ∪ G).card := by rw [hmark]; exact hn
    have hh := remaining_card_double_zero T label F hF tb gb hgt 18 hdouble x hne
    change (remainingOrdinaryTargets T label F tb gb 0 x).card+δ+P.card=TC.card at hpart
    omega
  have hraw := ordinary_zero_candidate_cost T label F hF ta tb ga gb ht hg hga 0 a b s j
    hjs ha hb hs hj x hx
  apply zero_candidate_cases _ TC.card P.card G.card δ a b s j d hu hm hc htcard hδ hsrc hdbl hraw
  intro hpc hgc
  obtain ⟨u,hu⟩ := Finset.card_eq_one.mp hpc
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hgc
  exact zero_shared_target_guard T label F hF ta tb ga gb ht hg hga a b s j d
    ha hb hs hj hd x hx u v hu hv



end ZT
end
end z64
