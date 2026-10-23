-- Prove2me | solution 1 for Paley11987Verified.CompactBooleanTransfer.row_boundary_weighted
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T04:41:02.99561+00:00
-- url     : https://prove2.me/submissions/fd28786a-d418-4232-909a-89ab27d4d8f1

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






end Nesting











section JointCandidates








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









theorem _root_.solution (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (v : Fin k)
    (hv : tolerantRow T label F t g q x v = true)
    (W : Fin r → ℕ) (V : Fin k → ℕ)
    (ht : ∀ c, (flipsTo (F t) false (recursiveChild x v c)).card ≤ W c)
    (hg : ∀ w ∈ criticalGuards T label F g q x v,
      (flipsTo (F g) true (recursiveChild x w (label v w))).card ≤ V w) :
    (flipsTo (fun y => tolerantRow T label F t g q y v) false x).card ≤
      (∑ c, W c) + ∑ w ∈ criticalGuards T label F g q x v, V w := by
  let U := Finset.univ.biUnion fun c => childFlipsTo F t false x v c
  let Q := criticalGuards T label F g q x v
  let Z := Q.biUnion fun w => childFlipsTo F g true x w (label v w)
  have hsub : flipsTo (fun y => tolerantRow T label F t g q y v) false x ⊆ U ∪ Z := by
    rintro ⟨⟨w,c⟩,a⟩ hp
    have hoff := (mem_flipsTo _ _ _ _).mp hp
    rcases tolerant_loss_cases T label F t g q x v w c a hv hoff with
      ⟨hwv, hon, hoff⟩ | ⟨hcount, hadj, hc, hoff, hon⟩
    · subst w
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨c, Finset.mem_univ _, (mem_childFlipsTo_same _ _ _ _ _ _ _).mpr hoff⟩)
    · subst c
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨w, ?_, (mem_childFlipsTo_same _ _ _ _ _ _ _).mpr hon⟩
      change w ∈ criticalGuards T label F g q x v
      simp only [criticalGuards, if_pos hcount]
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, ?_⟩
      simp [mem_failedGuards, hoff]
  have hU : U.card ≤ ∑ c, W c := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro c _
    simpa only [childFlipsTo_card] using ht c
  have hZ : Z.card ≤ ∑ w ∈ Q, V w := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro w hw
    simpa only [childFlipsTo_card] using hg w hw
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le U Z).trans (Nat.add_le_add hU hZ))







end ZT
end
end z31
