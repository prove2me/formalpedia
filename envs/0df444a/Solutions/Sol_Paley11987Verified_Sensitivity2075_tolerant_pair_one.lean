-- Prove2me | solution 1 for Paley11987Verified.Sensitivity2075.tolerant_pair_one
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T04:38:41.975395+00:00
-- url     : https://prove2.me/submissions/77c08283-2d68-4275-89b9-a5ee97fa7aca

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
import Definitions.Def_Paley11987Support_036
import Definitions.Def_Paley11987Support_055

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



@[simp] theorem childJointChanges_card {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q q' : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    (childJointChanges F q q' x j c).card =
      jointSensitivityAt (F q) (F q') (recursiveChild x j c) := by
  simp [childJointChanges, jointSensitivityAt]

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















@[simp] theorem mem_failedGuards {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) :
    j ∈ failedGuards T label F G x i ↔
      T.Adj i j ∧ F G (recursiveChild x j (label i j)) = true := by
  simp [failedGuards]









section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

theorem guard_mem_flip_iff {v : Fin k} (hne : (v, label i v) ≠ (j,c)) :
    v ∈ failedGuards T label F G (flip x {((j,c),a)}) i ↔
      v ∈ failedGuards T label F G x i := by
  simp only [mem_failedGuards, recursiveChild_flip_other x j v c (label i v) a hne]

theorem guards_flip_subset :
    failedGuards T label F G (flip x {((j,c),a)}) i ⊆
      insert j (failedGuards T label F G x i) := by
  intro v hv
  by_cases he : v = j
  · exact Finset.mem_insert.mpr (Or.inl he)
  · exact Finset.mem_insert.mpr (Or.inr
      ((guard_mem_flip_iff T label F G x i j c a (by
        intro hh; exact he (congrArg Prod.fst hh))).mp hv))



theorem guards_flip_card_le :
    (failedGuards T label F G (flip x {((j,c),a)}) i).card ≤
      (failedGuards T label F G x i).card + 1 :=
  (Finset.card_le_card (guards_flip_subset T label F G x i j c a)).trans
    (Finset.card_insert_le _ _)



theorem guards_flip_own :
    failedGuards T label F G (flip x {((i,c),a)}) i =
      failedGuards T label F G x i := by
  ext v
  by_cases hv : T.Adj i v
  · exact guard_mem_flip_iff T label F G x i i c a (by
      intro hh; exact T.ne_of_adj hv (congrArg Prod.fst hh).symm)
  · simp only [mem_failedGuards, hv, false_and]



theorem guard_increase_location
    (hinc : (failedGuards T label F G x i).card <
      (failedGuards T label F G (flip x {((j,c),a)}) i).card) :
    T.Adj i j ∧ c = label i j ∧ F G (recursiveChild x j c) = false ∧
      F G (flip (recursiveChild x j c) {a}) = true := by
  obtain ⟨v, hv', hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hinc
  have hloc : (v, label i v) = (j,c) := by
    by_contra hh
    exact hv ((guard_mem_flip_iff T label F G x i j c a hh).mp hv')
  have hvj : v = j := congrArg Prod.fst hloc
  subst v
  have hcl : c = label i j := (congrArg Prod.snd hloc).symm
  subst c
  obtain ⟨hij, hon⟩ := (mem_failedGuards T label F G _ i j).mp hv'
  refine ⟨hij, rfl, ?_, ?_⟩
  · simpa only [mem_failedGuards, hij, true_and, Bool.not_eq_true] using hv
  · simpa only [recursiveChild_flip_same] using hon

end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)



theorem tolerant_loss_cases
    (hon : tolerantRow T label F A G q x i = true)
    (hoff : tolerantRow T label F A G q (flip x {((j,c),a)}) i = false) :
    (j = i ∧ F A (recursiveChild x j c) = true ∧
      F A (flip (recursiveChild x j c) {a}) = false) ∨
    ((failedGuards T label F G x i).card = q ∧ T.Adj i j ∧ c = label i j ∧
      F G (recursiveChild x j c) = false ∧
      F G (flip (recursiveChild x j c) {a}) = true) := by
  obtain ⟨ht, hg⟩ := (tolerantRow_true T label F A G q x i).mp hon
  by_cases hji : j = i
  · subst j
    refine Or.inl ⟨rfl, ht c, ?_⟩
    cases hc : F A (flip (recursiveChild x i c) {a})
    · rfl
    · have hg' : (failedGuards T label F G (flip x {((i,c),a)}) i).card ≤ q := by
        simpa only [guards_flip_own] using hg
      have hh := (tolerantRow_true T label F A G q _ i).mpr ⟨?_, hg'⟩
      · simp [hoff] at hh
      · intro d
        by_cases hd : d = c
        · subst d
          simpa only [recursiveChild_flip_same] using hc
        · simpa only [recursiveChild_flip_other x i i c d a (by
            intro he; exact hd (congrArg Prod.snd he))] using ht d
  · have htargets : ∀ d, F A (recursiveChild (flip x {((j,c),a)}) i d) = true := by
      intro d
      simpa only [recursiveChild_flip_other x j i c d a (by
        intro he; exact hji (congrArg Prod.fst he).symm)] using ht d
    have hcount : q < (failedGuards T label F G (flip x {((j,c),a)}) i).card := by
      by_contra hn
      have hh := (tolerantRow_true T label F A G q _ i).mpr
        ⟨htargets, by omega⟩
      simp [hoff] at hh
    have hupper := guards_flip_card_le T label F G x i j c a
    have hexact : (failedGuards T label F G x i).card = q := by omega
    exact Or.inr ⟨hexact, guard_increase_location T label F G x i j c a (by omega)⟩

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











section JointCandidates
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F) (Ai Aj Gi Gj : Fin n)
  (hA : Ai ≤ Aj) (hG : Gj ≤ Gi)
  (x : ((Fin k × Fin r) × I) → Bool)







end JointCandidates

theorem _root_.solution {n k r : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F) (o q : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (Z Y : Fin n → Fin n → ℕ) (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (Ai Aj Gi Gj : Fin n) (hA : Ai ≤ Aj) (hG : Gj ≤ Gi)
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : tolerantFamily T label F Ai Gi q x = true)
    (hx' : tolerantFamily T label F Aj Gj q x = true) :
    jointSensitivityAt (tolerantFamily T label F Ai Gi q)
      (tolerantFamily T label F Aj Gj q) x ≤ r*Y Ai Aj+(o-q)*Z Gj Gi := by
  obtain ⟨i, hi'⟩ := (tolerantFamily_true T label F Aj Gj q x).mp hx'
  have hi := tolerantRow_nested T label F hF hA hG (le_refl q) x i hi'
  have hw := (tolerantRow_true T label F Ai Gi q x i).mp hi
  have hs := (tolerantRow_true T label F Aj Gj q x i).mp hi'
  let B := failedGuards T label F Gi x i
  let P := if B.card = q then (Finset.univ.filter (T.Adj i)) \ B else ∅
  let U := Finset.univ.biUnion fun c => childJointChanges F Ai Aj x i c
  let V := P.biUnion fun j => childJointChanges F Gj Gi x j (label i j)
  have hPcard : P.card ≤ o-q := by
    by_cases he : B.card = q
    · have hsub : B ⊆ Finset.univ.filter (T.Adj i) := by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ((mem_failedGuards T label F Gi x i j).mp hj).1⟩
      simp only [P, if_pos he, Finset.card_sdiff_of_subset hsub, ho i, he, le_refl]
    · simp only [P, if_neg he, Finset.card_empty, Nat.zero_le]
  have hPfalse : ∀ j ∈ P,
      F Gj (recursiveChild x j (label i j)) = false ∧
      F Gi (recursiveChild x j (label i j)) = false := by
    intro j hj
    by_cases he : B.card = q
    · have hh : j ∈ (Finset.univ.filter (T.Adj i)) \ B := by simpa only [P, if_pos he] using hj
      obtain ⟨hj, hjB⟩ := Finset.mem_sdiff.mp hh
      have hij := (Finset.mem_filter.mp hj).2
      have hset : B = failedGuards T label F Gj x i :=
        Finset.eq_of_subset_of_card_le (failedGuards_subset T label F hF hG x i) (by
          change (failedGuards T label F Gj x i).card ≤ B.card
          rw [he]
          exact hs.2)
      have hsnot : j ∉ failedGuards T label F Gj x i := by rw [← hset]; exact hjB
      constructor
      · simpa only [mem_failedGuards, hij, true_and, Bool.not_eq_true] using hsnot
      · simpa only [B, mem_failedGuards, hij, true_and, Bool.not_eq_true] using hjB
    · simp only [P, if_neg he, Finset.notMem_empty] at hj
  have hsub : (Finset.univ.filter fun p =>
      tolerantFamily T label F Ai Gi q (flip x {p}) ≠ tolerantFamily T label F Ai Gi q x ∧
      tolerantFamily T label F Aj Gj q (flip x {p}) ≠ tolerantFamily T label F Aj Gj q x) ⊆
      U ∪ V := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hf : tolerantFamily T label F Ai Gi q (flip x {((j,c),a)}) = false := by
      cases hy : tolerantFamily T label F Ai Gi q (flip x {((j,c),a)})
      · rfl
      · exact False.elim (hc.1 (hy.trans hx.symm))
    have hf' : tolerantFamily T label F Aj Gj q (flip x {((j,c),a)}) = false := by
      cases hy : tolerantFamily T label F Aj Gj q (flip x {((j,c),a)})
      · rfl
      · exact False.elim (hc.2 (hy.trans hx'.symm))
    have hif := (tolerantFamily_false T label F Ai Gi q _).mp hf i
    have hif' := (tolerantFamily_false T label F Aj Gj q _).mp hf' i
    rcases tolerant_loss_cases T label F Ai Gi q x i j c a hi hif with
      ⟨hji, hwon, hwoff⟩ | ⟨hcount, hij, hcl, hwoff, hwon⟩
    · rcases tolerant_loss_cases T label F Aj Gj q x i j c a hi' hif' with
        ⟨_, hson, hsoff⟩ | ⟨_, hij, _⟩
      · subst j
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨c, Finset.mem_univ _, ?_⟩
        have hn : F Ai (flip (recursiveChild x i c) {a}) ≠ F Ai (recursiveChild x i c) ∧
            F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
          simp [hwon, hwoff, hson, hsoff]
        simpa [childJointChanges] using hn
      · exact False.elim (T.ne_of_adj hij hji.symm)
    · rcases tolerant_loss_cases T label F Aj Gj q x i j c a hi' hif' with
        ⟨hji, _⟩ | ⟨_, _, _, hsoff, hson⟩
      · exact False.elim (T.ne_of_adj hij hji.symm)
      · subst c
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨j, ?_, ?_⟩
        · change j ∈ P
          simp only [P, show B.card = q from hcount, if_pos rfl]
          apply Finset.mem_sdiff.mpr
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, by
            simp only [B, mem_failedGuards, hwoff, Bool.false_eq_true, and_false, not_false_eq_true]⟩
        · have hn : F Gj (flip (recursiveChild x j (label i j)) {a}) ≠
                F Gj (recursiveChild x j (label i j)) ∧
              F Gi (flip (recursiveChild x j (label i j)) {a}) ≠
                F Gi (recursiveChild x j (label i j)) := by
              simp [hwon, hwoff, hson, hsoff]
          simpa [childJointChanges] using hn
  have hU : U.card ≤ r*Y Ai Aj := by
    simpa [U] using card_biUnion_le_mul Finset.univ
      (fun c => childJointChanges F Ai Aj x i c) (Y Ai Aj) (fun c _ => by
        rw [childJointChanges_card]
        exact hY _ _ hA _ (hw.1 c) (hs.1 c))
  have hV : V.card ≤ (o-q)*Z Gj Gi := by
    have hh : V.card ≤ P.card * Z Gj Gi := by
      apply card_biUnion_le_mul
      intro j hj
      rw [childJointChanges_card]
      exact hZ _ _ hG _ (hPfalse j hj).1 (hPfalse j hj).2
    exact hh.trans (Nat.mul_le_mul_right _ hPcard)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le U V).trans (Nat.add_le_add hU hV))



end Sensitivity2075
end
end z29
