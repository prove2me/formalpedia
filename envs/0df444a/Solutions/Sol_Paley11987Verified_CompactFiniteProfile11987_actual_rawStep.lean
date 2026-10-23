-- Prove2me | solution 1 for Paley11987Verified.CompactFiniteProfile11987.actual_rawStep
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T05:06:22.379474+00:00
-- url     : https://prove2.me/submissions/03b4e544-6ee8-48e9-a933-1bf47040fd26

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
import Theorems.Thm_Paley11987Verified_Sensitivity2075_tolerant_pair_one
import Theorems.Thm_Paley11987Verified_CompactBooleanTransfer_row_boundary_weighted
import Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_actual_rawA
import Theorems.Thm_Paley11987Verified_CompactBooleanTransfer_zero_union_of_row_boundary

set_option autoImplicit false
set_option Elab.async false
section z29

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open scoped Classical BigOperators
namespace OAI.Paper320



theorem NestedFamily.rejects_of_le {h : ℕ} {I : Type}
    {F : Fin h → (I → Bool) → Bool} (hF : NestedFamily F)
    {q q' : Fin h} {x} (hqq : q ≤ q') (hx : F q x = false) :
    F q' x = false := by
  cases h' : F q' x
  · rfl
  · have := hF.accepts_of_le hqq h'
    simp [hx] at this









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



theorem strict_tolerance_pair_one {n k r : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (Y : Fin n → Fin n → ℕ) (hY : PairBound F true Y)
    (Ai Aj Gi Gj : Fin n) (hA : Ai ≤ Aj) (hG : Gj ≤ Gi)
    (qi qj : ℕ) (hq : qj < qi)
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : tolerantFamily T label F Ai Gi qi x = true)
    (hx' : tolerantFamily T label F Aj Gj qj x = true) :
    jointSensitivityAt (tolerantFamily T label F Ai Gi qi)
      (tolerantFamily T label F Aj Gj qj) x ≤ r*Y Ai Aj := by
  obtain ⟨i, hi'⟩ := (tolerantFamily_true T label F Aj Gj qj x).mp hx'
  have hi := tolerantRow_nested T label F hF hA hG hq.le x i hi'
  have hw := (tolerantRow_true T label F Ai Gi qi x i).mp hi
  have hs := (tolerantRow_true T label F Aj Gj qj x i).mp hi'
  let U := Finset.univ.biUnion fun c => childJointChanges F Ai Aj x i c
  have hsub : (Finset.univ.filter fun p =>
      tolerantFamily T label F Ai Gi qi (flip x {p}) ≠ tolerantFamily T label F Ai Gi qi x ∧
      tolerantFamily T label F Aj Gj qj (flip x {p}) ≠ tolerantFamily T label F Aj Gj qj x) ⊆ U := by
    rintro ⟨⟨j,c⟩,a⟩ hp
    have hc := (Finset.mem_filter.mp hp).2
    have hf : tolerantFamily T label F Ai Gi qi (flip x {((j,c),a)}) = false := by
      cases hy : tolerantFamily T label F Ai Gi qi (flip x {((j,c),a)})
      · rfl
      · exact False.elim (hc.1 (hy.trans hx.symm))
    have hif := (tolerantFamily_false T label F Ai Gi qi _).mp hf i
    rcases tolerant_loss_cases T label F Ai Gi qi x i j c a hi hif with
      ⟨hji, hwon, hwoff⟩ | ⟨hcount, _⟩
    · subst j
      have hson := hs.1 c
      have hsoff := hF.rejects_of_le hA hwoff
      apply Finset.mem_biUnion.mpr
      refine ⟨c, Finset.mem_univ _, ?_⟩
      have hn : F Ai (flip (recursiveChild x i c) {a}) ≠ F Ai (recursiveChild x i c) ∧
          F Aj (flip (recursiveChild x i c) {a}) ≠ F Aj (recursiveChild x i c) := by
        simp [hwon, hwoff, hson, hsoff]
      simpa [childJointChanges] using hn
    · have hb := Finset.card_le_card (failedGuards_subset T label F hF hG x i)
      omega
  have hU : U.card ≤ r*Y Ai Aj := by
    simpa [U] using card_biUnion_le_mul Finset.univ
      (fun c => childJointChanges F Ai Aj x i c) (Y Ai Aj) (fun c _ => by
        rw [childJointChanges_card]
        exact hY _ _ hA _ (hw.1 c) (hs.1 c))
  exact (Finset.card_le_card hsub).trans hU

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











theorem flipsTo_false_card_eq_joint (f g : (I → Bool) → Bool)
    (hfg : ∀ x, g x = true → f x = true) (x : I → Bool) (hx : g x = true) :
    (flipsTo f false x).card = jointSensitivityAt f g x := by
  have hfx := hfg x hx
  unfold flipsTo jointSensitivityAt
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfx, hx, Bool.not_eq_true]
  constructor
  · intro ha
    refine ⟨ha, ?_⟩
    cases hb : g (flip x {a})
    · rfl
    · have hc := hfg (flip x {a}) hb
      simp [ha] at hc
  · exact And.left

theorem flipsTo_true_card_eq_joint (f g : (I → Bool) → Bool)
    (hfg : ∀ x, g x = true → f x = true) (x : I → Bool) (hx : f x = false) :
    (flipsTo g true x).card = jointSensitivityAt f g x := by
  have hgx : g x = false := by
    cases hg : g x
    · rfl
    · have hc := hfg x hg
      simp [hx] at hc
  unfold flipsTo jointSensitivityAt
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hx, hgx, Bool.not_eq_false]
  constructor
  · intro ha
    exact ⟨hfg _ ha, ha⟩
  · exact And.right

theorem pairBound_false {h : ℕ} (F : Fin h → (I → Bool) → Bool)
    (hF : NestedFamily F) (A : Fin h → Fin h → ℕ)
    (hA : ∀ i j, i ≤ j → ABound F i j (A i j)) : PairBound F false A := by
  intro i j hij x hix _
  rw [← flipsTo_true_card_eq_joint (F i) (F j) (fun _ => hF.accepts_of_le hij) x hix]
  exact hA i j hij x hix

theorem pairBound_true {h : ℕ} (F : Fin h → (I → Bool) → Bool)
    (hF : NestedFamily F) (B : Fin h → Fin h → ℕ)
    (hB : ∀ i j, i ≤ j → BBound F i j (B i j)) : PairBound F true B := by
  intro i j hij x _ hjx
  rw [← flipsTo_false_card_eq_joint (F i) (F j) (fun _ => hF.accepts_of_le hij) x hjx]
  exact hB i j hij x hjx

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

theorem ordinary_one {n k : ℕ}
    (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (d : ℕ) (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = d)
    (A B : Fin n → Fin n → ℕ)
    (hA : ∀ i j, i ≤ j → ABound F i j (A i j))
    (hB : ∀ i j, i ≤ j → BBound F i j (B i j))
    (ti tj gi gj : Fin n) (ht : ti ≤ tj) (hg : gj ≤ gi)
    (qi qj : ℕ) (hq : qj ≤ qi)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F tj gj qj x = true) :
    (flipsTo (tolerantFamily T label F ti gi qi) false x).card ≤
      2 * B ti tj + if qi = qj then (d-qj) * A gj gi else 0 := by
  have hw := family_nested T label F hF ht hg hq x hx
  rw [flipsTo_false_card_eq_joint _ _
    (fun y => family_nested T label F hF ht hg hq y) x hx]
  by_cases he : qi = qj
  · subst qi
    simpa only [if_pos rfl, ite_true] using _root_.Paley11987Verified.Sensitivity2075.tolerant_pair_one T label F hF d qj hd A B
      (pairBound_false F hF A hA) (pairBound_true F hF B hB) ti tj gi gj ht hg x hw hx
  · have hstrict : qj < qi := by omega
    simpa only [if_neg he, Nat.add_zero] using strict_tolerance_pair_one
      T label F hF B (pairBound_true F hF B hB) ti tj gi gj ht hg qi qj hstrict x hw hx

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









theorem criticalGuards_card (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (g : Fin n) (q d : ℕ)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = d)
    (x : ((Fin k × Fin r) × I) → Bool) (v : Fin k) :
    (criticalGuards T label F g q x v).card ≤ d-q := by
  by_cases he : (failedGuards T label F g x v).card = q
  · have hs : failedGuards T label F g x v ⊆ Finset.univ.filter (T.Adj v) := by
      intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_failedGuards T label F g x v w).mp hw |>.1⟩
    simp only [criticalGuards, if_pos he, Finset.card_sdiff_of_subset hs, hd v, he, ite_true, le_refl]
  · simp only [criticalGuards, if_neg he, Finset.card_empty, Nat.zero_le]

theorem criticalGuard_false_stronger (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (gi gj : Fin n) (hg : gj ≤ gi) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (v w : Fin k)
    (hj : (failedGuards T label F gj x v).card ≤ q)
    (hw : w ∈ criticalGuards T label F gi q x v) :
    F gj (recursiveChild x w (label v w)) = false := by
  by_cases he : (failedGuards T label F gi x v).card = q
  · have hs : failedGuards T label F gi x v = failedGuards T label F gj x v :=
      Finset.eq_of_subset_of_card_le (failedGuards_subset T label F hF hg x v) (by omega)
    have hwm : w ∈ (Finset.univ.filter (T.Adj v)) \ failedGuards T label F gi x v := by
      simpa only [criticalGuards, if_pos he] using hw
    obtain ⟨hwadj, hwnot⟩ := Finset.mem_sdiff.mp hwm
    have hadj := (Finset.mem_filter.mp hwadj).2
    rw [hs] at hwnot
    simpa only [mem_failedGuards, hadj, true_and, Bool.not_eq_true] using hwnot
  · simp only [criticalGuards, if_neg he, Finset.notMem_empty] at hw

theorem criticalGuards_empty_of_strict (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (gi gj : Fin n) (hg : gj ≤ gi) (qi qj : ℕ) (hq : qj < qi)
    (x : ((Fin k × Fin r) × I) → Bool) (v : Fin k)
    (hj : (failedGuards T label F gj x v).card ≤ qj) :
    criticalGuards T label F gi qi x v = ∅ := by
  have hs := Finset.card_le_card (failedGuards_subset T label F hF hg x v)
  have hn : (failedGuards T label F gi x v).card ≠ qi := by omega
  simp [criticalGuards, hn]



theorem parent_down_subset_row (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (v : Fin k) :
    flipsTo (tolerantFamily T label F t g q) false x ⊆
      flipsTo (fun y => tolerantRow T label F t g q y v) false x := by
  intro a ha
  apply (mem_flipsTo _ _ _ _).mpr
  exact (tolerantFamily_false T label F t g q _).mp ((mem_flipsTo _ _ _ _).mp ha) v

theorem sum_two_special (c₀ : Fin 2) (m b : ℕ) :
    (∑ c : Fin 2, if c = c₀ then m else b) = m+b := by
  fin_cases c₀ <;> simp [Fin.sum_univ_two, Nat.add_comm]

theorem row_boundary_target_equal (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ti tj tk gi gj : Fin n) (ht : ti ≤ tj) (hg : gj ≤ gi) (q d : ℕ)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = d)
    (b a m : ℕ) (hb : BBound F ti tj b) (ha : ABound F gj gi a)
    (hm : MBound F ti tj tk m)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k)
    (hv : tolerantRow T label F tj gj q x v = true)
    (c₀ : Fin 2) (hc : F tk (recursiveChild x v c₀) = false) :
    (flipsTo (fun y => tolerantRow T label F ti gi q y v) false x).card ≤
      b + (d-q)*a + m := by
  have hs := (tolerantRow_true T label F tj gj q x v).mp hv
  have hw := tolerantRow_nested T label F hF ht hg (le_refl q) x v hv
  have h := _root_.Paley11987Verified.CompactBooleanTransfer.row_boundary_weighted T label F ti gi q x v hw
    (fun c => if c = c₀ then m else b) (fun _ => a) (by
      intro c
      by_cases he : c = c₀
      · subst c
        simpa only [if_pos rfl, ite_true] using hm _ (hs.1 c₀) hc
      · simpa only [if_neg he] using hb _ (hs.1 c)) (by
      intro w hw
      exact ha _ (criticalGuard_false_stronger T label F hF gi gj hg q x v w hs.2 hw))
  rw [sum_two_special] at h
  have hcard := criticalGuards_card T label F gi q d hd x v
  simp only [Finset.sum_const, smul_eq_mul] at h
  have hh := Nat.mul_le_mul_right a hcard
  omega

end ZT
end
end z31

section z53


namespace CompactConditionalProfiles

noncomputable section
open scoped Classical

variable {X I : Type*} [Fintype I]













































theorem adjacent_band {F : ℕ → X → Bool} {x : X} {j k : ℕ}
    (hjk : j < k) (hj : F j x = true) (hk : F k x = false) :
    ∃ m, j ≤ m ∧ m < k ∧ F m x = true ∧ F (m + 1) x = false := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
      by_cases hmid : F k x = true
      · exact ⟨k, by omega, by omega, hmid, hk⟩
      · have hmidfalse : F k x = false := by
          cases h : F k x <;> simp_all
        have hlt : j < k := by
          have hne : j ≠ k := by
            intro heq
            subst j
            exact hmid hj
          omega
        obtain ⟨m, hmj, hmk, hm, hmnext⟩ := ih hlt hj hmidfalse
        exact ⟨m, hmj, by omega, hm, hmnext⟩







end
end CompactConditionalProfiles
end z53

section z54

set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
open OAI.Paper320 ZT

namespace CompactFiniteProfileClosures
variable {h : ℕ} {I : Type} [Fintype I]
variable {F : Fin h → (I → Bool) → Bool}

 
 
 
 
 

 
 

 
 
 theorem m_of_b {i j k : Fin h} {v : ℕ} (hv : BBound F i j v) : MBound F i j k v :=
  fun x hj _ => hv x hj
 theorem p_of_a {j k l : Fin h} {v : ℕ} (hv : ABound F k l v) : PBound F j k l v :=
  fun x _ hk => hv x hk
 
 
 
 theorem d_of_mp {i j k l : Fin h} {m p : ℕ}
    (hm : MBound F i j k m) (hp : PBound F j k l p) : DBound F i j k l (m+p) := by
  intro x hj hk
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hm x hj hk) (hp x hj hk))
 
 

 theorem adjacent {j k : Fin h} {x : I → Bool} (hjk : j < k)
    (hj : F j x = true) (hk : F k x = false) :
    ∃ (m : Fin h) (hm : m.val+1 < h), j ≤ m ∧ m < k ∧
      F m x = true ∧ F ⟨m.val+1, hm⟩ x = false := by
  let G : ℕ → (I → Bool) → Bool := fun i => if hi : i < h then F ⟨i,hi⟩ else fun _ => false
  have hj' : G j.val x = true := by simpa [G, j.isLt] using hj
  have hk' : G k.val x = false := by simpa [G, k.isLt] using hk
  obtain ⟨m, hmj, hmk, hm, hmnext⟩ :=
    CompactConditionalProfiles.adjacent_band (F := G) (show j.val < k.val from hjk) hj' hk'
  have hmH : m < h := hmk.trans k.isLt
  have hmnH : m+1 < h := by omega
  refine ⟨⟨m,hmH⟩,hmnH,hmj,hmk,?_,?_⟩
  · simpa [G, hmH] using hm
  · simpa [G, hmnH] using hmnext

 

 

end CompactFiniteProfileClosures
end
end z54

section z56

namespace ZP











theorem foldl_max_le (xs : List ℕ) (a b : ℕ) :
    xs.foldl max a ≤ b ↔ a ≤ b ∧ ∀ x ∈ xs, x ≤ b := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih, Nat.max_le, List.mem_cons, forall_eq_or_imp]
      tauto

theorem maximum_le_iff (xs : List ℕ) (b : ℕ) :
    maximum xs ≤ b ↔ ∀ x ∈ xs, x ≤ b := by
  simpa [maximum] using foldl_max_le xs 0 b

theorem le_maximum_of_mem {xs : List ℕ} {x : ℕ} (hx : x ∈ xs) : x ≤ maximum xs :=
  (maximum_le_iff xs (maximum xs)).mp le_rfl x hx















 

 

end ZP
end z56

section z57

set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 ZT
open CompactFiniteProfileClosures
namespace ZP
variable {I : Type} [Fintype I]

theorem mem_interval_of_le_lt {j k m : ℕ} (hjm : j ≤ m) (hmk : m < k) :
    m ∈ interval j k := by
  exact List.mem_map.mpr ⟨m-j,List.mem_range.mpr (by omega),Nat.add_sub_of_le hjm⟩

theorem ScaledBounds.minus {F : Fin 20 → (I → Bool) → Bool} {v : Profile} {c : ℕ}
    (hv : ScaledBounds F v c) (i j k : Fin 20) (hij : i ≤ j) (hjk : j ≤ k) :
    MBound F i j k (c*minus v i.val j.val k.val) := by
  intro x hj hk
  have hjk' : j < k := by
    apply lt_of_le_of_ne hjk
    intro he
    rw [he,hk] at hj
    contradiction
  obtain ⟨m,hn,hjm,hmk,hmt,hmf⟩ := adjacent hjk' hj hk
  have hb := hv.m i m (hij.trans hjm) hn x hmt hmf
  apply hb.trans
  apply Nat.mul_le_mul_left c
  rw [ZP.minus,if_pos (show i.val ≤ j.val ∧ j.val < k.val from ⟨hij,hjk'⟩)]
  exact le_maximum_of_mem (List.mem_map.mpr
    ⟨m.val,mem_interval_of_le_lt hjm hmk,rfl⟩)

theorem ScaledBounds.plus {F : Fin 20 → (I → Bool) → Bool} {v : Profile} {c : ℕ}
    (hv : ScaledBounds F v c) (i j k : Fin 20) (hij : i ≤ j) (hjk : j ≤ k) :
    PBound F i j k (c*plus v i.val j.val k.val) := by
  intro x hi hj
  have hij' : i < j := by
    apply lt_of_le_of_ne hij
    intro he
    rw [he,hj] at hi
    contradiction
  obtain ⟨m,hn,him,hmj,hmt,hmf⟩ := adjacent hij' hi hj
  have hb := hv.p m k (hmj.trans_le hjk) hn x hmt hmf
  apply hb.trans
  apply Nat.mul_le_mul_left c
  rw [ZP.plus,if_pos (show i.val < j.val ∧ j.val ≤ k.val from ⟨hij',hjk⟩)]
  exact le_maximum_of_mem (List.mem_map.mpr
    ⟨m.val,mem_interval_of_le_lt him hmj,rfl⟩)

theorem ScaledBounds.union {F : Fin 20 → (I → Bool) → Bool} {v : Profile} {c : ℕ}
    (hv : ScaledBounds F v c) (i j k l : Fin 20)
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    DBound F i j k l (c*union v i.val j.val k.val l.val) := by
  intro x hj hk
  have hjk' : j < k := by
    apply lt_of_le_of_ne hjk
    intro he
    rw [he,hk] at hj
    contradiction
  obtain ⟨m,hn,hjm,hmk,hmt,hmf⟩ := adjacent hjk' hj hk
  have hb := hv.d i m l (hij.trans hjm) (hmk.trans_le hkl) hn x hmt hmf
  apply hb.trans
  apply Nat.mul_le_mul_left c
  rw [ZP.union,if_pos (show i.val ≤ j.val ∧ j.val < k.val ∧ k.val ≤ l.val from ⟨hij,hjk',hkl⟩)]
  exact le_maximum_of_mem (List.mem_map.mpr
    ⟨m.val,mem_interval_of_le_lt hjm hmk,rfl⟩)











end ZP
end
end z57

section z66

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT

variable {n k : ℕ} {I : Type} [Fintype I]

theorem sum_special {J : Type} [DecidableEq J] (S : Finset J) (w₀ : J)
    (hw : w₀ ∈ S) (p a : ℕ) :
    (∑ w ∈ S, if w = w₀ then p else a) = (S.card-1)*a+p := by
  calc
    (∑ w ∈ S, if w = w₀ then p else a) =
        (∑ w ∈ S.erase w₀, if w = w₀ then p else a)+p := by
      simpa using (Finset.sum_erase_add S (fun w => if w = w₀ then p else a) hw).symm
    _ = (S.card-1)*a+p := by
      have he : (∑ w ∈ S.erase w₀, if w = w₀ then p else a) = ∑ _w ∈ S.erase w₀, a := by
        apply Finset.sum_congr rfl
        intro w hw
        exact if_neg (Finset.ne_of_mem_erase hw)
      rw [he]
      simp [Finset.card_erase_of_mem hw]

theorem row_boundary_guard_equal (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ti tj tk gi gj gk : Fin n) (ht : ti ≤ tj) (hg : gj ≤ gi)
    (q d : ℕ) (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = d)
    (b a p : ℕ) (hb : BBound F ti tk b) (ha : ABound F gj gi a)
    (hp : PBound F gk gj gi p)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k)
    (hv : tolerantRow T label F tj gj q x v = true)
    (htk : ∀ c, F tk (recursiveChild x v c) = true)
    (hk : q < (failedGuards T label F gk x v).card) :
    (flipsTo (fun y => tolerantRow T label F ti gi q y v) false x).card ≤
      2*b + (d-q-1)*a + p := by
  have hs := (tolerantRow_true T label F tj gj q x v).mp hv
  have hw := tolerantRow_nested T label F hF ht hg (le_refl q) x v hv
  by_cases he : (failedGuards T label F gi x v).card = q
  · have hlt : (failedGuards T label F gj x v).card <
        (failedGuards T label F gk x v).card := by omega
    obtain ⟨w₀, hwk, hwnj⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hwk' := (mem_failedGuards T label F gk x v w₀).mp hwk
    have hjoff : F gj (recursiveChild x w₀ (label v w₀)) = false := by
      simpa only [mem_failedGuards, hwk'.1, true_and, Bool.not_eq_true] using hwnj
    have hwcrit : w₀ ∈ criticalGuards T label F gi q x v := by
      simp only [criticalGuards, if_pos he]
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwk'.1⟩, ?_⟩
      intro hh
      exact hwnj (failedGuards_subset T label F hF hg x v hh)
    have h := _root_.Paley11987Verified.CompactBooleanTransfer.row_boundary_weighted T label F ti gi q x v hw (fun _ => b)
      (fun w => if w = w₀ then p else a) (fun c => hb _ (htk c)) (by
        intro w hw
        by_cases hww : w = w₀
        · subst w
          simpa only [if_pos rfl, ite_true] using hp _ hwk'.2 hjoff
        · simpa only [if_neg hww] using
            ha _ (criticalGuard_false_stronger T label F hF gi gj hg q x v w hs.2 hw))
    rw [sum_special _ _ hwcrit] at h
    have hc := criticalGuards_card T label F gi q d hd x v
    have hh := Nat.mul_le_mul_right a (Nat.sub_le_sub_right hc 1)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    omega
  · have hnone : criticalGuards T label F gi q x v = ∅ := by simp [criticalGuards, he]
    have h := _root_.Paley11987Verified.CompactBooleanTransfer.row_boundary_weighted T label F ti gi q x v hw (fun _ => b)
      (fun _ => 0) (fun c => hb _ (htk c)) (by simp [hnone])
    simp only [hnone, Finset.sum_const_zero, Nat.add_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    omega

theorem row_boundary_strict (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ti tj gi gj : Fin n) (ht : ti ≤ tj) (hg : gj ≤ gi)
    (qi q : ℕ) (hq : q < qi)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k)
    (hv : tolerantRow T label F tj gj q x v = true)
    (W : Fin 2 → ℕ)
    (hW : ∀ c, (flipsTo (F ti) false (recursiveChild x v c)).card ≤ W c) :
    (flipsTo (fun y => tolerantRow T label F ti gi qi y v) false x).card ≤ ∑ c, W c := by
  have hs := (tolerantRow_true T label F tj gj q x v).mp hv
  have hw := tolerantRow_nested T label F hF ht hg hq.le x v hv
  have hn := criticalGuards_empty_of_strict T label F hF gi gj hg qi q hq x v hs.2
  have h := _root_.Paley11987Verified.CompactBooleanTransfer.row_boundary_weighted T label F ti gi qi x v hw W (fun _ => 0) hW (by simp [hn])
  simpa [hn] using h

theorem row_boundary_target (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ti tj tk gi gj : Fin n) (ht : ti ≤ tj) (hg : gj ≤ gi) (qi q d : ℕ) (hq : q ≤ qi)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = d)
    (b a m : ℕ) (hb : BBound F ti tj b) (ha : ABound F gj gi a)
    (hm : MBound F ti tj tk m)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k)
    (hv : tolerantRow T label F tj gj q x v = true)
    (c₀ : Fin 2) (hc : F tk (recursiveChild x v c₀) = false) :
    (flipsTo (fun y => tolerantRow T label F ti gi qi y v) false x).card ≤
      b + (if qi = q then (d-q)*a else 0) + m := by
  by_cases he : qi = q
  · subst qi
    simpa using row_boundary_target_equal T label F hF ti tj tk gi gj ht hg q d hd b a m
      hb ha hm x v hv c₀ hc
  · have hs := (tolerantRow_true T label F tj gj q x v).mp hv
    have hstrict : q < qi := by omega
    have h := row_boundary_strict T label F hF ti tj gi gj ht hg qi q hstrict x v hv
      (fun c => if c = c₀ then m else b) (by
        intro c
        by_cases hcc : c = c₀
        · subst c
          simpa using hm _ (hs.1 c₀) hc
        · simpa [hcc] using hb _ (hs.1 c))
    rw [sum_two_special] at h
    simpa [he, Nat.add_comm] using h

theorem row_boundary_guard (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ti tj tk gi gj gk : Fin n) (ht : ti ≤ tj) (hg : gj ≤ gi)
    (qi q d : ℕ) (hq : q ≤ qi)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = d)
    (b a p : ℕ) (hb : BBound F ti tk b) (ha : ABound F gj gi a)
    (hp : PBound F gk gj gi p)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k)
    (hv : tolerantRow T label F tj gj q x v = true)
    (htk : ∀ c, F tk (recursiveChild x v c) = true)
    (hk : q < (failedGuards T label F gk x v).card) :
    (flipsTo (fun y => tolerantRow T label F ti gi qi y v) false x).card ≤
      2*b + if qi = q then (d-q-1)*a+p else 0 := by
  by_cases he : qi = q
  · subst qi
    simpa [Nat.add_assoc] using row_boundary_guard_equal T label F hF ti tj tk gi gj gk ht hg q d hd
      b a p hb ha hp x v hv htk hk
  · have hstrict : q < qi := by omega
    have h := row_boundary_strict T label F hF ti tj gi gj ht hg qi q hstrict x v hv
      (fun _ => b) (fun c => hb _ (htk c))
    simpa [he] using h

theorem conditional_down (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ti tj tk gi gj gk : Fin n) (htij : ti ≤ tj) (htjk : tj ≤ tk)
    (hgjgi : gj ≤ gi) (hgkgj : gk ≤ gj)
    (qi q d : ℕ) (hq : q ≤ qi)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = d)
    (b₁ b₂ a m p : ℕ)
    (hb₁ : BBound F ti tj b₁) (hb₂ : BBound F ti tk b₂)
    (ha : ABound F gj gi a) (hm : MBound F ti tj tk m) (hp : PBound F gk gj gi p)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hxj : tolerantFamily T label F tj gj q x = true)
    (hxk : tolerantFamily T label F tk gk q x = false) :
    (flipsTo (tolerantFamily T label F ti gi qi) false x).card ≤
      max (if tj < tk then b₁ + (if qi = q then (d-q)*a else 0) + m else 0)
          (if gk < gj then 2*b₂ + (if qi = q then (d-q-1)*a+p else 0) else 0) := by
  obtain ⟨v, hv⟩ := (tolerantFamily_true T label F tj gj q x).mp hxj
  have hvk := (tolerantFamily_false T label F tk gk q x).mp hxk v
  have hs := (tolerantRow_true T label F tj gj q x v).mp hv
  apply (Finset.card_le_card (parent_down_subset_row T label F ti gi qi x v)).trans
  by_cases htarg : ∃ c, F tk (recursiveChild x v c) = false
  · obtain ⟨c, hc⟩ := htarg
    have hlt : tj < tk := by
      apply lt_of_le_of_ne htjk
      intro he
      have hh := hs.1 c
      rw [he, hc] at hh
      contradiction
    exact (row_boundary_target T label F hF ti tj tk gi gj htij hgjgi qi q d hq hd
      b₁ a m hb₁ ha hm x v hv c hc).trans
        (by simp only [if_pos hlt]; exact le_max_left _ _)
  · have htk : ∀ c, F tk (recursiveChild x v c) = true := by
      intro c
      cases hh : F tk (recursiveChild x v c)
      · exact False.elim (htarg ⟨c,hh⟩)
      · rfl
    have hcount : q < (failedGuards T label F gk x v).card := by
      by_contra hn
      have hh := (tolerantRow_true T label F tk gk q x v).mpr ⟨htk, by omega⟩
      simp [hvk] at hh
    have hlt : gk < gj := by
      apply lt_of_le_of_ne hgkgj
      intro he
      rw [he] at hcount
      omega
    exact (row_boundary_guard T label F hF ti tj tk gi gj gk htij hgjgi qi q d hq hd
      b₂ a p hb₂ ha hp x v hv htk hcount).trans
        (by simp only [if_pos hlt]; exact le_max_right _ _)

end ZT
end
end z66

section z67

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 ZT
open CompactFiniteProfileClosures
namespace ZP
variable {I : Type} [Fintype I]

 theorem actual_rawB {k : ℕ} (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = 5993)
    (F : Fin 20 → (I → Bool) → Bool) (hF : NestedFamily F)
    (v : Profile) (c : ℕ) (hv : ScaledBounds F v c)
    (r : Recipe) (hr : RecipeValid r) (i j : Fin 20) (hij : i ≤ j) :
    BBound (stageFamily T label F r hr) i j (c*rawB v r i.val j.val) := by
  intro x hx
  have hh := ordinary_one T label F hF 5993 hd
    (fun a b => c*A v a.val b.val) (fun a b => c*B v a.val b.val)
    hv.a hv.b (targetIndex r hr i) (targetIndex r hr j)
    (guardIndex r hr i) (guardIndex r hr j)
    (hr.target_mono i j hij) (hr.guard_antitone i j hij)
    (tolerance r i) (tolerance r j) (hr.tol_antitone i j hij) x hx
  simpa only [stageFamily,targetIndex,guardIndex,tolerance,rawB,
    mul_ite,Nat.mul_zero,Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm _ c] using hh

 theorem actual_rawM {k : ℕ} (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = 5993)
    (F : Fin 20 → (I → Bool) → Bool) (hF : NestedFamily F)
    (v : Profile) (c : ℕ) (hv : ScaledBounds F v c)
    (r : Recipe) (hr : RecipeValid r) (i j : Fin 20) (hij : i ≤ j)
    (hn : j.val+1 < 20) :
    MBound (stageFamily T label F r hr) i j ⟨j.val+1,hn⟩ (c*rawM v r i.val j.val) := by
  let l : Fin 20 := ⟨j.val+1,hn⟩
  let ti := targetIndex r hr i
  let tj := targetIndex r hr j
  let tk := targetIndex r hr l
  let gi := guardIndex r hr i
  let gj := guardIndex r hr j
  let gk := guardIndex r hr l
  let qi := tolerance r i
  let qj := tolerance r j
  let qk := tolerance r l
  have hjl : j ≤ l := by change j.val ≤ j.val+1; omega
  have htil : ti ≤ tk := hr.target_mono i l (hij.trans hjl)
  have htij : ti ≤ tj := hr.target_mono i j hij
  have htjk : tj ≤ tk := hr.target_mono j l hjl
  have hgjgi : gj ≤ gi := hr.guard_antitone i j hij
  have hgkgj : gk ≤ gj := hr.guard_antitone j l hjl
  by_cases he : qj=qk
  · intro x hxj hxk
    have hh := conditional_down T label F hF ti tj tk gi gj gk
      htij htjk hgjgi hgkgj qi qj 5993 (hr.tol_antitone i j hij) hd
      (c*B v ti.val tj.val) (c*B v ti.val tk.val) (c*A v gj.val gi.val)
      (c*minus v ti.val tj.val tk.val) (c*plus v gk.val gj.val gi.val)
      (hv.b ti tj htij) (hv.b ti tk htil) (hv.a gj gi hgjgi)
      (hv.minus ti tj tk htij htjk) (hv.plus gk gj gi hgkgj hgjgi)
      x hxj (by
        change tolerantFamily T label F tk gk qk x = false at hxk
        rw [← he] at hxk
        exact hxk)
    change (flipsTo (tolerantFamily T label F ti gi qi) false x).card ≤ _
    have he' : (r[j.val]?.getD default).tol = (r[j.val+1]?.getD default).tol := he
    simpa only [rawM,if_pos he',ti,tj,tk,gi,gj,gk,qi,qj,l,targetIndex,guardIndex,tolerance,
      mul_ite,Nat.mul_zero,Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm _ c,
      ← Nat.mul_max_mul_left,Fin.mk_lt_mk] using hh
  · have he' : (r[j.val]?.getD default).tol ≠ (r[j.val+1]?.getD default).tol := he
    have hh := m_of_b (k := ⟨j.val+1,hn⟩) (actual_rawB T label hd F hF v c hv r hr i j hij)
    simpa only [rawM,if_neg he'] using (hh : MBound (stageFamily T label F r hr)
      i j ⟨j.val+1,hn⟩ (c*rawB v r i.val j.val))

end ZP
end
end z67

section z68

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

theorem row_conditional_down (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ti tj tk gi gj gk : Fin n) (htij : ti ≤ tj) (htjk : tj ≤ tk)
    (hgjgi : gj ≤ gi) (hgkgj : gk ≤ gj)
    (qi q d : ℕ) (hq : q ≤ qi)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = d)
    (b₁ b₂ a m p : ℕ)
    (hb₁ : BBound F ti tj b₁) (hb₂ : BBound F ti tk b₂)
    (ha : ABound F gj gi a) (hm : MBound F ti tj tk m) (hp : PBound F gk gj gi p)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (v : Fin k) (hv : tolerantRow T label F tj gj q x v = true)
    (hvk : tolerantRow T label F tk gk q x v = false) :
    (flipsTo (fun y => tolerantRow T label F ti gi qi y v) false x).card ≤
      max (if tj < tk then b₁ + (if qi = q then (d-q)*a else 0) + m else 0)
          (if gk < gj then 2*b₂ + (if qi = q then (d-q-1)*a+p else 0) else 0) := by
  have hs := (tolerantRow_true T label F tj gj q x v).mp hv
  by_cases htarg : ∃ c, F tk (recursiveChild x v c) = false
  · obtain ⟨c, hc⟩ := htarg
    have hlt : tj < tk := by
      apply lt_of_le_of_ne htjk
      intro he
      have hh := hs.1 c
      rw [he, hc] at hh
      contradiction
    exact (row_boundary_target T label F hF ti tj tk gi gj htij hgjgi qi q d hq hd
      b₁ a m hb₁ ha hm x v hv c hc).trans
        (by simp only [if_pos hlt]; exact le_max_left _ _)
  · have htk : ∀ c, F tk (recursiveChild x v c) = true := by
      intro c
      cases hh : F tk (recursiveChild x v c)
      · exact False.elim (htarg ⟨c,hh⟩)
      · rfl
    have hcount : q < (failedGuards T label F gk x v).card := by
      by_contra hn
      have hh := (tolerantRow_true T label F tk gk q x v).mpr ⟨htk, by omega⟩
      simp [hvk] at hh
    have hlt : gk < gj := by
      apply lt_of_le_of_ne hgkgj
      intro he
      rw [he] at hcount
      omega
    exact (row_boundary_guard T label F hF ti tj tk gi gj gk htij hgjgi qi q d hq hd
      b₂ a p hb₂ ha hp x v hv htk hcount).trans
        (by simp only [if_pos hlt]; exact le_max_right _ _)







end ZT
end
end z68

section z71

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



theorem zero_union (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ti tj tk tl gi gj gk gl : Fin n)
    (htij : ti ≤ tj) (htjk : tj ≤ tk) (htkl : tk ≤ tl)
    (hgjgi : gj ≤ gi) (hgkgj : gk ≤ gj) (hglgk : gl ≤ gk)
    (hgil : gi ≤ tl) (hgli : gl ≤ ti)
    (d : ℕ) (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = d)
    (b₁ b₂ a₀ m p b a dt dg : ℕ)
    (hb₁ : BBound F ti tj b₁) (hb₂ : BBound F ti tk b₂)
    (ha₀ : ABound F gj gi a₀) (hm : MBound F ti tj tk m) (hp : PBound F gk gj gi p)
    (hb : BBound F ti tl b) (ha : ABound F gl gi a)
    (hdt : DBound F ti tj tk tl dt) (hdg : DBound F gl gk gj gi dg)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hxj : tolerantFamily T label F tj gj 0 x = true)
    (hxk : tolerantFamily T label F tk gk 0 x = false) :
    (flipsTo (tolerantFamily T label F ti gi 0) false x ∪
      flipsTo (tolerantFamily T label F tl gl 0) true x).card ≤
      max (max (if tj < tk then b₁+d*a₀+m else 0)
               (if gk < gj then 2*b₂+(d-1)*a₀+p else 0))
          (max (if tj < tk then b+d*a+dt else 0)
               (if gk < gj then 2*b+(d-1)*a+dg else 0)) := by
  apply _root_.Paley11987Verified.CompactBooleanTransfer.zero_union_of_row_boundary T label F hF ti tj tk tl gi gj gk gl
    htij htjk htkl hgjgi hgkgj hglgk hgil hgli d hd b a dt dg
    _ hb ha hdt hdg x hxj hxk
  intro v hvj hvk
  simpa [Nat.add_assoc] using row_conditional_down T label F hF ti tj tk gi gj gk
    htij htjk hgjgi hgkgj 0 0 d (le_refl 0) hd b₁ b₂ a₀ m p
    hb₁ hb₂ ha₀ hm hp x v hvj hvk

end ZT
end
end z71

section z72

set_option maxHeartbeats 4000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 ZT
open CompactFiniteProfileClosures
namespace ZP
variable {I : Type} [Fintype I]

 theorem actual_rawD {k : ℕ} (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = 5993)
    (F : Fin 20 → (I → Bool) → Bool) (hF : NestedFamily F)
    (v : Profile) (c : ℕ) (hv : ScaledBounds F v c)
    (r : Recipe) (hr : RecipeValid r) (i j l : Fin 20)
    (hij : i ≤ j) (hjl : j < l) (hn : j.val+1 < 20)
    (hm : MBound (stageFamily T label F r hr) i j ⟨j.val+1,hn⟩ (c*rawM v r i.val j.val))
    (hp : PBound (stageFamily T label F r hr) j ⟨j.val+1,hn⟩ l (c*rawP v r j.val l.val)) :
    DBound (stageFamily T label F r hr) i j ⟨j.val+1,hn⟩ l (c*rawD v r i.val j.val l.val) := by
  let jj : Fin 20 := ⟨j.val+1,hn⟩
  let ti := targetIndex r hr i
  let tj := targetIndex r hr j
  let tk := targetIndex r hr jj
  let tl := targetIndex r hr l
  let gi := guardIndex r hr i
  let gj := guardIndex r hr j
  let gk := guardIndex r hr jj
  let gl := guardIndex r hr l
  have hjk : j ≤ jj := by change j.val ≤ j.val+1; omega
  have hkl : jj ≤ l := by change j.val+1 ≤ l.val; exact hjl
  have htil : ti ≤ tl := hr.target_mono i l (hij.trans hjl.le)
  have htij : ti ≤ tj := hr.target_mono i j hij
  have htjk : tj ≤ tk := hr.target_mono j jj hjk
  have htkl : tk ≤ tl := hr.target_mono jj l hkl
  have hgjgi : gj ≤ gi := hr.guard_antitone i j hij
  have hgkgj : gk ≤ gj := hr.guard_antitone j jj hjk
  have hglgk : gl ≤ gk := hr.guard_antitone jj l hkl
  have hgiti : gi ≤ ti := hr.guard_target i
  have hglgi : gl ≤ gi := hglgk.trans (hgkgj.trans hgjgi)
  by_cases hz : (r[i.val]?.getD default).tol=0 ∧ (r[l.val]?.getD default).tol=0
  · have hqj : (r[j.val]?.getD default).tol=0 := by
      have hh := hr.tol_antitone i j hij
      omega
    have hqk : (r[j.val+1]?.getD default).tol=0 := by
      have hh := hr.tol_antitone i jj (hij.trans hjk)
      change (r[j.val+1]?.getD default).tol ≤ (r[i.val]?.getD default).tol at hh
      omega
    by_cases he : (r[j.val]?.getD default).target=(r[j.val+1]?.getD default).target ∧
        (r[j.val]?.getD default).guard=(r[j.val+1]?.getD default).guard
    · intro x hxj hxk
      have ht : tj=tk := Fin.ext he.1
      have hg : gj=gk := Fin.ext he.2
      change tolerantFamily T label F tj gj (r[j.val]?.getD default).tol x=true at hxj
      change tolerantFamily T label F tk gk (r[j.val+1]?.getD default).tol x=false at hxk
      rw [hqj,ht,hg] at hxj
      rw [hqk] at hxk
      simp [hxk] at hxj
    · intro x hxj hxk
      have hh := zero_union T label F hF ti tj tk tl gi gj gk gl
        htij htjk htkl hgjgi hgkgj hglgk (hgiti.trans htil) (hglgi.trans hgiti)
        5993 hd
        (c*B v ti.val tj.val) (c*B v ti.val tk.val) (c*A v gj.val gi.val)
        (c*minus v ti.val tj.val tk.val) (c*plus v gk.val gj.val gi.val)
        (c*B v ti.val tl.val) (c*A v gl.val gi.val)
        (c*union v ti.val tj.val tk.val tl.val) (c*union v gl.val gk.val gj.val gi.val)
        (hv.b ti tj htij) (hv.b ti tk (htij.trans htjk)) (hv.a gj gi hgjgi)
        (hv.minus ti tj tk htij htjk) (hv.plus gk gj gi hgkgj hgjgi)
        (hv.b ti tl htil) (hv.a gl gi hglgi)
        (hv.union ti tj tk tl htij htjk htkl) (hv.union gl gk gj gi hglgk hgkgj hgjgi)
        x (by
          change tolerantFamily T label F tj gj (r[j.val]?.getD default).tol x = true at hxj
          simpa only [hqj] using hxj)
        (by
          change tolerantFamily T label F tk gk (r[j.val+1]?.getD default).tol x = false at hxk
          simpa only [hqk] using hxk)
      have h5992 : 5993-1=5992 := by decide
      convert hh using 1
      · congr 1
        ext a
        simp only [Finset.mem_union, mem_flipsTo, stageFamily, tolerance,
          hz.1, hz.2, ti, tl, gi, gl]
      · simp only [stageFamily,targetIndex,guardIndex,tolerance,rawD,rawM,
        if_pos hz,if_neg he,hz.1,hz.2,hqj,hqk,ite_true,Nat.sub_zero,
        ti,tj,tk,tl,gi,gj,gk,gl,jj,
        mul_ite,Nat.mul_zero,Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm _ c,
        ← Nat.mul_max_mul_left,Fin.mk_lt_mk,Nat.max_assoc,Nat.add_assoc,
        and_self,h5992]
  · have hh := d_of_mp hm hp
    simpa only [rawD,if_neg hz,Nat.mul_add] using hh

end ZP
end
end z72

section z73

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 ZT
open CompactFiniteProfileClosures
namespace ZP
variable {I : Type} [Fintype I]



theorem _root_.solution {k : ℕ} (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (hCaps : LabelCaps T label)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = 5993)
    (F : Fin 20 → (I → Bool) → Bool) (hF : NestedFamily F)
    (v : Profile) (c : ℕ) (hv : ScaledBounds F v c)
    (r : Recipe) (hr : RecipeValid r) (hcost : GuardCostOrder v r) :
    RawStepBounds (stageFamily T label F r hr) v r c := by
  have ha : ∀ i j : Fin 20, i ≤ j →
      ABound (stageFamily T label F r hr) i j (c*rawA v r i.val j.val) :=
    fun i j hij => _root_.Paley11987Verified.CompactFiniteProfile11987.actual_rawA T label hCaps F hF v c hv r hr i j hij (hcost i j hij)
  have hb : ∀ i j : Fin 20, i ≤ j →
      BBound (stageFamily T label F r hr) i j (c*rawB v r i.val j.val) :=
    fun i j hij => actual_rawB T label hd F hF v c hv r hr i j hij
  have hm : ∀ i j : Fin 20, i ≤ j → ∀ hn : j.val+1 < 20,
      MBound (stageFamily T label F r hr) i j ⟨j.val+1,hn⟩ (c*rawM v r i.val j.val) :=
    fun i j hij hn => actual_rawM T label hd F hF v c hv r hr i j hij hn
  have hp : ∀ j l : Fin 20, j < l → ∀ hn : j.val+1 < 20,
      PBound (stageFamily T label F r hr) j ⟨j.val+1,hn⟩ l (c*rawP v r j.val l.val) := by
    intro j l hjl hn
    exact p_of_a (ha ⟨j.val+1,hn⟩ l hjl)
  refine ⟨ha,hb,hm,hp,?_⟩
  intro i j l hij hjl hn
  exact actual_rawD T label hd F hF v c hv r hr i j l hij hjl hn
    (hm i j hij hn) (hp j l hjl hn)



end ZP
end
end z73
