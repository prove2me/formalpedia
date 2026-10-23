-- Prove2me | solution 1 for Paley11987Verified.CompactBooleanTransfer.zero_union_of_row_boundary
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T05:03:27.877425+00:00
-- url     : https://prove2.me/submissions/82384bbf-8434-4a53-aaf9-cb63b0dee3c4

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



end ZT
end
end z31

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











end ZT
end
end z66

section z68

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



theorem zero_row_guard_false (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k)
    (hv : tolerantRow T label F t g 0 x v = true) (w : Fin k) (hw : T.Adj v w) :
    F g (recursiveChild x w (label v w)) = false := by
  have hs := (tolerantRow_true T label F t g 0 x v).mp hv
  have he : failedGuards T label F g x v = ∅ := Finset.card_eq_zero.mp (by omega)
  have hn : w ∉ failedGuards T label F g x v := by rw [he]; simp
  simpa only [mem_failedGuards, hw, true_and, Bool.not_eq_true] using hn

theorem zero_rows_incompatible (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (hab : ga ≤ tb) (hba : gb ≤ ta)
    (x : ((Fin k × Fin 2) × I) → Bool) (v w : Fin k) (hvw : v ≠ w)
    (hv : tolerantRow T label F ta ga 0 x v = true)
    (hw : tolerantRow T label F tb gb 0 x w = true) : False := by
  rcases T.adj_or_reverse hvw with he | he
  · have hz := zero_row_guard_false T label F ta ga x v hv w he
    have ho := hF.accepts_of_le hab (((tolerantRow_true T label F tb gb 0 x w).mp hw).1 (label v w))
    simp [hz] at ho
  · have hz := zero_row_guard_false T label F tb gb x w hw v he
    have ho := hF.accepts_of_le hba (((tolerantRow_true T label F ta ga 0 x v).mp hv).1 (label w v))
    simp [hz] at ho

theorem parent_exits_subset_chosen_rows (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ti tl gi gl : Fin n) (hil : gi ≤ tl) (hli : gl ≤ ti)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k) :
    flipsTo (tolerantFamily T label F ti gi 0) false x ∪
      flipsTo (tolerantFamily T label F tl gl 0) true x ⊆
      flipsTo (fun y => tolerantRow T label F ti gi 0 y v) false x ∪
        flipsTo (fun y => tolerantRow T label F tl gl 0 y v) true x := by
  intro a ha
  rcases Finset.mem_union.mp ha with hd | hu
  · exact Finset.mem_union_left _ (parent_down_subset_row T label F ti gi 0 x v hd)
  · have hparent := (mem_flipsTo _ _ _ _).mp hu
    obtain ⟨w, hw⟩ := (tolerantFamily_true T label F tl gl 0 _).mp hparent
    by_cases he : w = v
    · subst w
      exact Finset.mem_union_right _ ((mem_flipsTo _ _ _ _).mpr hw)
    · apply Finset.mem_union_left
      apply (mem_flipsTo _ _ _ _).mpr
      cases hh : tolerantRow T label F ti gi 0 (flip x {a}) v
      · rfl
      · exact False.elim (zero_rows_incompatible T label F hF ti tl gi gl hil hli
          (flip x {a}) v w (Ne.symm he) hh hw)

end ZT
end
end z68

section z69

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

theorem row_union_weighted (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k)
    (hv : tolerantRow T label F t g 0 x v = true)
    (U : Fin 2 → Finset ((Fin k × Fin 2) × I))
    (V : Fin k → Finset ((Fin k × Fin 2) × I))
    (Extra : Finset ((Fin k × Fin 2) × I))
    (ht : ∀ c, childFlipsTo F t false x v c ⊆ U c)
    (hg : ∀ w ∈ criticalGuards T label F g 0 x v,
      childFlipsTo F g true x w (label v w) ⊆ V w)
    (he : Extra ⊆ (Finset.univ.biUnion U) ∪
      ((criticalGuards T label F g 0 x v).biUnion V))
    (u : Fin 2 → ℕ) (z : Fin k → ℕ)
    (hU : ∀ c, (U c).card ≤ u c)
    (hV : ∀ w ∈ criticalGuards T label F g 0 x v, (V w).card ≤ z w) :
    ((flipsTo (fun y => tolerantRow T label F t g 0 y v) false x) ∪ Extra).card ≤
      (∑ c, u c) + ∑ w ∈ criticalGuards T label F g 0 x v, z w := by
  let Q := criticalGuards T label F g 0 x v
  have hsub : flipsTo (fun y => tolerantRow T label F t g 0 y v) false x ∪ Extra ⊆
      (Finset.univ.biUnion U) ∪ (Q.biUnion V) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases p with ⟨⟨w,c⟩,a⟩
      rcases tolerant_loss_cases T label F t g 0 x v w c a hv ((mem_flipsTo _ _ _ _).mp hp) with
        ⟨hwv, hon, hoff⟩ | ⟨hcount, hadj, hc, hoff, hon⟩
      · subst w
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨c, Finset.mem_univ _, ht c ((mem_childFlipsTo_same _ _ _ _ _ _ _).mpr hoff)⟩)
      · subst c
        have hqw : w ∈ Q := by
          change w ∈ criticalGuards T label F g 0 x v
          simp only [criticalGuards, if_pos hcount]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj⟩,
            by simp [mem_failedGuards, hoff]⟩
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨w, hqw, hg w hqw ((mem_childFlipsTo_same _ _ _ _ _ _ _).mpr hon)⟩)
    · exact he hp
  have huc : (Finset.univ.biUnion U).card ≤ ∑ c, u c :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun c _ => hU c))
  have hvc : (Q.biUnion V).card ≤ ∑ w ∈ Q, z w :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun w hw => hV w hw))
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add huc hvc))

theorem same_row_target_repair (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k) (c₀ : Fin 2)
    (hm : missingTargets F t x v = {c₀}) (hg : failedGuards T label F g x v = ∅) :
    flipsTo (fun y => tolerantRow T label F t g 0 y v) true x ⊆
      childFlipsTo F t true x v c₀ := by
  have hoff : tolerantRow T label F t g 0 x v = false := by
    cases hh : tolerantRow T label F t g 0 x v
    · rfl
    · have hc := ((tolerantRow_true T label F t g 0 x v).mp hh).1 c₀
      have hf : F t (recursiveChild x v c₀) = false := by
        apply (mem_missingTargets F t x v c₀).mp
        rw [hm]
        simp
      simp [hf] at hc
  rintro ⟨⟨w,c⟩,a⟩ hp
  rcases _root_.Paley11987Verified.Sensitivity2075.tolerant_repair_cases T label F t g 0 x v w c a hoff ((mem_flipsTo _ _ _ _).mp hp) with
    ⟨_, hwv, hfalse, htrue⟩ | ⟨hcand, _⟩
  · subst w
    have hc : c = c₀ := by
      have hmem := (mem_missingTargets F t x v c).mpr hfalse
      rwa [hm, Finset.mem_singleton] at hmem
    subst c
    exact (mem_childFlipsTo_same _ _ _ _ _ _ _).mpr htrue
  · have hh := (Finset.mem_filter.mp hcand).2.2
    simp [hg] at hh

theorem row_union_target_bound (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (ti tl gi gl : Fin n)
    (d : ℕ) (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = d)
    (b a u : ℕ) (hb : BBound F ti tl b) (ha : ABound F gl gi a)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k) (c₀ : Fin 2)
    (hvi : tolerantRow T label F ti gi 0 x v = true)
    (hm : missingTargets F tl x v = {c₀}) (hgl : failedGuards T label F gl x v = ∅)
    (hu : (flipsTo (F ti) false (recursiveChild x v c₀) ∪
      flipsTo (F tl) true (recursiveChild x v c₀)).card ≤ u) :
    (flipsTo (fun y => tolerantRow T label F ti gi 0 y v) false x ∪
      flipsTo (fun y => tolerantRow T label F tl gl 0 y v) true x).card ≤ b+d*a+u := by
  let U := fun c : Fin 2 => childLift (v,c)
    (flipsTo (F ti) false (recursiveChild x v c) ∪
      (if c = c₀ then flipsTo (F tl) true (recursiveChild x v c) else ∅))
  let V := fun w : Fin k => childFlipsTo F gi true x w (label v w)
  have huc : ∀ c, (U c).card ≤ if c = c₀ then u else b := by
    intro c
    by_cases hc : c = c₀
    · subst c
      simpa [U] using hu
    · have htl : F tl (recursiveChild x v c) = true := by
        cases hh : F tl (recursiveChild x v c)
        · have hmem := (mem_missingTargets F tl x v c).mpr hh
          rw [hm, Finset.mem_singleton] at hmem
          exact False.elim (hc hmem)
        · rfl
      simpa [U, hc] using hb _ htl
  have hvc : ∀ w ∈ criticalGuards T label F gi 0 x v, (V w).card ≤ a := by
    intro w hw
    have he : (failedGuards T label F gi x v).card = 0 := by
      have h := (tolerantRow_true T label F ti gi 0 x v).mp hvi |>.2
      omega
    have hws : w ∈ Finset.univ.filter (T.Adj v) := by
      have hh : w ∈ (Finset.univ.filter (T.Adj v)) \ failedGuards T label F gi x v := by
        simpa only [criticalGuards, if_pos he] using hw
      exact (Finset.mem_sdiff.mp hh).1
    have hadj := (Finset.mem_filter.mp hws).2
    have hz : F gl (recursiveChild x w (label v w)) = false := by
      have hn : w ∉ failedGuards T label F gl x v := by rw [hgl]; simp
      simpa only [mem_failedGuards, hadj, true_and, Bool.not_eq_true] using hn
    simpa [V] using ha _ hz
  have h := row_union_weighted T label F ti gi x v hvi U V
    (flipsTo (fun y => tolerantRow T label F tl gl 0 y v) true x)
    (by
      intro c p hp
      obtain ⟨hpc,hpa⟩ := (mem_childLift _ _ _).mp hp
      exact (mem_childLift _ _ _).mpr ⟨hpc, Finset.mem_union_left _ hpa⟩)
    (by intro w _; exact Finset.Subset.refl _)
    (by
      intro p hp
      have hh := same_row_target_repair T label F tl gl x v c₀ hm hgl hp
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨c₀, Finset.mem_univ _, ?_⟩
      obtain ⟨hpc,hpa⟩ := (mem_childLift _ _ _).mp hh
      apply (mem_childLift _ _ _).mpr
      refine ⟨hpc, Finset.mem_union_right _ ?_⟩
      simpa using hpa)
    (fun c => if c = c₀ then u else b) (fun _ => a) huc hvc
  rw [sum_two_special] at h
  have hc := criticalGuards_card T label F gi 0 d hd x v
  have hmul := Nat.mul_le_mul_right a hc
  simp only [Finset.sum_const, smul_eq_mul, Nat.sub_zero] at h hc hmul
  omega

end ZT
end
end z69

section z70

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

theorem same_row_guard_repair (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n)
    (x : ((Fin k × Fin 2) × I) → Bool) (v w₀ : Fin k)
    (hm : missingTargets F t x v = ∅) (hg : failedGuards T label F g x v = {w₀}) :
    flipsTo (fun y => tolerantRow T label F t g 0 y v) true x ⊆
      childFlipsTo F g false x w₀ (label v w₀) := by
  have hoff : tolerantRow T label F t g 0 x v = false := by
    cases hh : tolerantRow T label F t g 0 x v
    · rfl
    · have hc := ((tolerantRow_true T label F t g 0 x v).mp hh).2
      simp [hg] at hc
  rintro ⟨⟨w,c⟩,a⟩ hp
  rcases _root_.Paley11987Verified.Sensitivity2075.tolerant_repair_cases T label F t g 0 x v w c a hoff ((mem_flipsTo _ _ _ _).mp hp) with
    ⟨hcand, _⟩ | ⟨_, hadj, hc, htrue, hfalse⟩
  · have hh := (Finset.mem_filter.mp hcand).2.1
    simp [hm] at hh
  · subst c
    have hw : w = w₀ := by
      have hmem := (mem_failedGuards T label F g x v w).mpr ⟨hadj,htrue⟩
      rwa [hg, Finset.mem_singleton] at hmem
    subst w
    exact (mem_childFlipsTo_same _ _ _ _ _ _ _).mpr hfalse

theorem row_union_guard_bound (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (ti tl gi gl : Fin n)
    (d : ℕ) (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = d)
    (b a u : ℕ) (hb : BBound F ti tl b) (ha : ABound F gl gi a)
    (x : ((Fin k × Fin 2) × I) → Bool) (v w₀ : Fin k)
    (hvi : tolerantRow T label F ti gi 0 x v = true)
    (hm : missingTargets F tl x v = ∅) (hgl : failedGuards T label F gl x v = {w₀})
    (hu : (flipsTo (F gi) true (recursiveChild x w₀ (label v w₀)) ∪
      flipsTo (F gl) false (recursiveChild x w₀ (label v w₀))).card ≤ u) :
    (flipsTo (fun y => tolerantRow T label F ti gi 0 y v) false x ∪
      flipsTo (fun y => tolerantRow T label F tl gl 0 y v) true x).card ≤
      2*b+(d-1)*a+u := by
  let U := fun c : Fin 2 => childFlipsTo F ti false x v c
  let V := fun w : Fin k => childLift (w,label v w)
    (flipsTo (F gi) true (recursiveChild x w (label v w)) ∪
      (if w = w₀ then flipsTo (F gl) false (recursiveChild x w (label v w)) else ∅))
  have htargets := (missingTargets_empty F tl x v).mp hm
  have hfailed : failedGuards T label F gi x v = ∅ := by
    apply Finset.card_eq_zero.mp
    have hh := ((tolerantRow_true T label F ti gi 0 x v).mp hvi).2
    omega
  have hcritical : criticalGuards T label F gi 0 x v = Finset.univ.filter (T.Adj v) := by
    simp [criticalGuards, hfailed]
  have hw₀ : w₀ ∈ criticalGuards T label F gi 0 x v := by
    have hm : w₀ ∈ failedGuards T label F gl x v := by rw [hgl]; simp
    rw [hcritical]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((mem_failedGuards T label F gl x v w₀).mp hm).1⟩
  have huc : ∀ c, (U c).card ≤ b := by
    intro c
    simpa [U] using hb _ (htargets c)
  have hvc : ∀ w ∈ criticalGuards T label F gi 0 x v, (V w).card ≤ if w = w₀ then u else a := by
    intro w hw
    by_cases he : w = w₀
    · subst w
      simpa [V] using hu
    · have hadj : T.Adj v w := by
        rw [hcritical] at hw
        exact (Finset.mem_filter.mp hw).2
      have hz : F gl (recursiveChild x w (label v w)) = false := by
        have hn : w ∉ failedGuards T label F gl x v := by simpa [hgl] using he
        simpa only [mem_failedGuards, hadj, true_and, Bool.not_eq_true] using hn
      simpa [V, he] using ha _ hz
  have h := row_union_weighted T label F ti gi x v hvi U V
    (flipsTo (fun y => tolerantRow T label F tl gl 0 y v) true x)
    (by intro c; exact Finset.Subset.refl _)
    (by
      intro w _ p hp
      obtain ⟨hpc,hpa⟩ := (mem_childLift _ _ _).mp hp
      exact (mem_childLift _ _ _).mpr ⟨hpc, Finset.mem_union_left _ hpa⟩)
    (by
      intro p hp
      have hh := same_row_guard_repair T label F tl gl x v w₀ hm hgl hp
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨w₀, hw₀, ?_⟩
      obtain ⟨hpc,hpa⟩ := (mem_childLift _ _ _).mp hh
      apply (mem_childLift _ _ _).mpr
      refine ⟨hpc, Finset.mem_union_right _ ?_⟩
      simpa using hpa)
    (fun _ => b) (fun w => if w = w₀ then u else a) huc hvc
  rw [sum_special _ _ hw₀, hcritical, hd v] at h
  simpa [Nat.add_assoc] using h

end ZT
end
end z70

section z71

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

theorem _root_.solution (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ti tj tk tl gi gj gk gl : Fin n)
    (htij : ti ≤ tj) (htjk : tj ≤ tk) (htkl : tk ≤ tl)
    (hgjgi : gj ≤ gi) (hgkgj : gk ≤ gj) (hglgk : gl ≤ gk)
    (hgil : gi ≤ tl) (hgli : gl ≤ ti)
    (d : ℕ) (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = d)
    (b a dt dg R : ℕ) (hb : BBound F ti tl b) (ha : ABound F gl gi a)
    (hdt : DBound F ti tj tk tl dt) (hdg : DBound F gl gk gj gi dg)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hxj : tolerantFamily T label F tj gj 0 x = true)
    (hxk : tolerantFamily T label F tk gk 0 x = false)
    (hR : ∀ v, tolerantRow T label F tj gj 0 x v = true →
      tolerantRow T label F tk gk 0 x v = false →
      (flipsTo (fun y => tolerantRow T label F ti gi 0 y v) false x).card ≤ R) :
    (flipsTo (tolerantFamily T label F ti gi 0) false x ∪
      flipsTo (tolerantFamily T label F tl gl 0) true x).card ≤
      max R (max (if tj < tk then b+d*a+dt else 0)
        (if gk < gj then 2*b+(d-1)*a+dg else 0)) := by
  obtain ⟨v, hvj⟩ := (tolerantFamily_true T label F tj gj 0 x).mp hxj
  have hvk := (tolerantFamily_false T label F tk gk 0 x).mp hxk v
  have hvi := tolerantRow_nested T label F hF htij hgjgi (le_refl 0) x v hvj
  have hvl : tolerantRow T label F tl gl 0 x v = false := by
    cases hh : tolerantRow T label F tl gl 0 x v
    · rfl
    · have hk := tolerantRow_nested T label F hF htkl hglgk (le_refl 0) x v hh
      simp [hvk] at hk
  have hsj := (tolerantRow_true T label F tj gj 0 x v).mp hvj
  apply (Finset.card_le_card
    (parent_exits_subset_chosen_rows T label F hF ti tl gi gl hgil hgli x v)).trans
  by_cases hcT : v ∈ tolerantTargets T label F tl gl 0 x
  · have hcT' := (Finset.mem_filter.mp hcT).2
    obtain ⟨c₀, hm⟩ := Finset.card_eq_one.mp hcT'.1
    have hgl : failedGuards T label F gl x v = ∅ := Finset.card_eq_zero.mp (by omega)
    have hglk : failedGuards T label F gk x v = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr (by
        intro w hw
        have hh := failedGuards_subset T label F hF hglgk x v hw
        simp [hgl] at hh)
    have hkt : F tk (recursiveChild x v c₀) = false := by
      cases hh : F tk (recursiveChild x v c₀)
      · rfl
      · have hrow : tolerantRow T label F tk gk 0 x v = true := by
          apply (tolerantRow_true T label F tk gk 0 x v).mpr
          refine ⟨?_, by simp [hglk]⟩
          intro c
          by_cases he : c = c₀
          · simpa [he] using hh
          · have hl : F tl (recursiveChild x v c) = true := by
              cases hl : F tl (recursiveChild x v c)
              · have hm' := (mem_missingTargets F tl x v c).mpr hl
                rw [hm, Finset.mem_singleton] at hm'
                exact False.elim (he hm')
              · rfl
            exact hF.accepts_of_le htkl hl
        simp [hvk] at hrow
    have hlt : tj < tk := by
      apply lt_of_le_of_ne htjk
      intro he
      have hh := hsj.1 c₀
      rw [he,hkt] at hh
      contradiction
    have hbound := row_union_target_bound T label F ti tl gi gl d hd b a dt hb ha x v c₀
      hvi hm hgl (hdt _ (hsj.1 c₀) hkt)
    apply hbound.trans
    have hh : b+d*a+dt ≤ max (if tj < tk then b+d*a+dt else 0)
        (if gk < gj then 2*b+(d-1)*a+dg else 0) := by
      rw [if_pos hlt]
      exact le_max_left _ _
    exact hh.trans (le_max_right _ _)
  · by_cases hcG : v ∈ tolerantGuards T label F tl gl 0 x
    · have hcG' := (Finset.mem_filter.mp hcG).2
      have hcount : (failedGuards T label F gl x v).card = 1 := by simpa using hcG'.2
      obtain ⟨w₀,hgl⟩ := Finset.card_eq_one.mp hcount
      have hwmem : w₀ ∈ failedGuards T label F gl x v := by rw [hgl]; simp
      have hadj := ((mem_failedGuards T label F gl x v w₀).mp hwmem).1
      have hjoff := zero_row_guard_false T label F tj gj x v hvj w₀ hadj
      have hkon : F gk (recursiveChild x w₀ (label v w₀)) = true := by
        cases hh : F gk (recursiveChild x w₀ (label v w₀))
        · have hglk : failedGuards T label F gk x v = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro w hw
            have hhgl := failedGuards_subset T label F hF hglgk x v hw
            rw [hgl,Finset.mem_singleton] at hhgl
            subst w
            have hon := ((mem_failedGuards T label F gk x v w₀).mp hw).2
            simp [hh] at hon
          have hrow : tolerantRow T label F tk gk 0 x v = true := by
            apply (tolerantRow_true T label F tk gk 0 x v).mpr
            exact ⟨fun c => hF.accepts_of_le htkl ((missingTargets_empty F tl x v).mp hcG'.1 c),
              by simp [hglk]⟩
          simp [hvk] at hrow
        · rfl
      have hlt : gk < gj := by
        apply lt_of_le_of_ne hgkgj
        intro he
        rw [he,hjoff] at hkon
        contradiction
      have hlocal : (flipsTo (F gi) true (recursiveChild x w₀ (label v w₀)) ∪
          flipsTo (F gl) false (recursiveChild x w₀ (label v w₀))).card ≤ dg := by
        simpa only [Finset.union_comm] using hdg _ hkon hjoff
      have hbound := row_union_guard_bound T label F ti tl gi gl d hd b a dg hb ha x v w₀
        hvi hcG'.1 hgl hlocal
      apply hbound.trans
      have hh : 2*b+(d-1)*a+dg ≤ max (if tj < tk then b+d*a+dt else 0)
          (if gk < gj then 2*b+(d-1)*a+dg else 0) := by
        rw [if_pos hlt]
        exact le_max_right _ _
      exact hh.trans (le_max_right _ _)
    · have hnone : flipsTo (fun y => tolerantRow T label F tl gl 0 y v) true x = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        rintro ⟨⟨w,c⟩,a⟩ hp
        rcases _root_.Paley11987Verified.Sensitivity2075.tolerant_repair_cases T label F tl gl 0 x v w c a hvl ((mem_flipsTo _ _ _ _).mp hp) with
          ⟨hc,_⟩ | ⟨hc,_⟩
        · exact hcT hc
        · exact hcG hc
      rw [hnone,Finset.union_empty]
      exact (hR v hvj hvk).trans (le_max_left _ _)



end ZT
end
end z71
