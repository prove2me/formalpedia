-- Prove2me | solution 1 for X25519Dalek.fnOk_basepointTable_mul_base_v2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T20:26:10.331079+00:00
-- url     : https://prove2.me/submissions/3153fc41-a54c-4499-8772-7c070db03f71

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.BitVec
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_X25519Dalek_Spec
import Theorems.Thm_X25519Dalek_steps_keepsFrozen_v2
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_X25519Dalek_fnOk_edwardsPoint_mul_by_pow_2_four_v2
import Theorems.Thm_X25519Dalek_basepointTable_mul_base_odd_iter
import Theorems.Thm_X25519Dalek_basepointTable_mul_base_even_iter
import Theorems.Thm_X25519Dalek_basepointTable_mul_base_prologue

set_option linter.all false

section
/-! # Separation-logic heap algebra

Ported from google-deepmind/code-verification @ 8c8d371f (Apache-2.0),
`arm64-semantics/ProofLib/CoreLemmas.lean` and `ProofLib/SepLogic/Model.lean`: the plain lemmas
about `Heap.Disjoint`, `Heap.union`, `Heap.Matches` and `sepConj`, with ProofLib's custom simp
attributes removed. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace Arm64

namespace SepProp
theorem satisfies_iff {P : SepProp} {m : Memory} :
    (m ⊨ P) ↔ ∃ h : Heap, P.holds h ∧ h.Matches m := Iff.rfl
theorem entails_iff {P Q : SepProp} : (P ⊢ Q) ↔ ∀ h : Heap, P.holds h → Q.holds h := Iff.rfl
theorem holds_emp_iff {h : Heap} : (emp : SepProp).holds h ↔ h = Heap.empty := Iff.rfl
theorem holds_sepConj_iff {P Q : SepProp} {h : Heap} :
    (P ∗ Q).holds h ↔
      ∃ h₁ h₂ : Heap, h₁.Disjoint h₂ ∧ h = h₁.union h₂ ∧ P.holds h₁ ∧ Q.holds h₂ := Iff.rfl
theorem holds_sepExists_iff {α : Sort _} {P : α → SepProp} {h : Heap} :
    (sepExists P).holds h ↔ ∃ x, (P x).holds h := Iff.rfl
end SepProp

theorem holds_pointsTo8_iff {a : BitVec 64} {v : BitVec 8} {h : Heap} :
    (pointsTo8 a v).holds h ↔ h = Heap.singleton a v := Iff.rfl

namespace Heap

theorem Disjoint.symm {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) : h₂.Disjoint h₁ := by
  refine ⟨fun a => ?_, fun γ k => (hd.2.1 γ k).symm, fun γ k => (hd.2.2.1 γ k).symm,
    fun γ k oa v h => hd.2.2.2.1 γ k oa v h.symm, fun a => (hd.2.2.2.2 a).symm⟩
  rcases hd.1 a with h1 | h2 | ⟨b, h1, h2⟩
  · exact Or.inr (Or.inl h1)
  · exact Or.inl h2
  · exact Or.inr (Or.inr ⟨b, h2, h1⟩)

theorem Disjoint.of_phys_left {h₁ h₂ : Heap}
    (ha : h₁.auth = fun _ _ => none := by rfl)
    (hf : h₁.frag = fun _ _ => none := by rfl)
    (hp : ∀ a, h₁.phys a = none ∨ h₂.phys a = none ∨
      ∃ b, h₁.phys a = some (.ro b) ∧ h₂.phys a = some (.ro b))
    (hm : h₁.mapped = fun _ => false := by rfl) :
    h₁.Disjoint h₂ := by
  refine ⟨hp, fun γ k => Or.inl (congrFun (congrFun ha γ) k),
    fun γ k => Or.inl (congrFun (congrFun hf γ) k), fun γ k oa v h => ?_,
    fun a => Or.inl (congrFun hm a)⟩
  rcases h with ⟨h1, _⟩ | ⟨_, h1⟩
  · rw [congrFun (congrFun ha γ) k] at h1; contradiction
  · rw [congrFun (congrFun hf γ) k] at h1; contradiction

@[simp]
theorem disjoint_empty_left (h : Heap) : Heap.empty.Disjoint h :=
  Disjoint.of_phys_left rfl rfl (fun _ => Or.inl rfl)

@[simp]
theorem disjoint_empty_right (h : Heap) : h.Disjoint Heap.empty :=
  (disjoint_empty_left h).symm

@[simp]
theorem union_empty_left (h : Heap) : Heap.empty.union h = h := by
  cases h; rfl

@[simp]
theorem union_empty_right (h : Heap) : h.union Heap.empty = h := by
  apply Heap.ext
  · funext a; dsimp [union, empty]; cases h.phys a <;> rfl
  · funext γ k; dsimp [union, empty]; cases h.auth γ k <;> rfl
  · funext γ k; dsimp [union, empty]; cases h.frag γ k <;> rfl
  · funext a; dsimp [union, empty]; cases h.mapped a <;> rfl

theorem union_comm_of_disjoint {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) :
    h₁.union h₂ = h₂.union h₁ := by
  apply Heap.ext
  · funext a; dsimp [union]
    rcases hd.1 a with h1 | h2 | ⟨b, h1, h2⟩
    · rw [h1]; cases h₂.phys a <;> rfl
    · rw [h2]; cases h₁.phys a <;> rfl
    · rw [h1, h2]
  · funext γ k; dsimp [union]
    rcases hd.2.1 γ k with h1 | h2
    · rw [h1]; cases h₂.auth γ k <;> rfl
    · rw [h2]; cases h₁.auth γ k <;> rfl
  · funext γ k; dsimp [union]
    rcases hd.2.2.1 γ k with h1 | h2
    · rw [h1]; cases h₂.frag γ k <;> rfl
    · rw [h2]; cases h₁.frag γ k <;> rfl
  · funext a; dsimp [union]
    rcases hd.2.2.2.2 a with h1 | h2
    · rw [h1]; cases h₂.mapped a <;> rfl
    · rw [h2]; cases h₁.mapped a <;> rfl

theorem union_assoc (h₁ h₂ h₃ : Heap) :
    (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃) := by
  apply Heap.ext
  · funext a; dsimp [union]; cases h₁.phys a <;> rfl
  · funext γ k; dsimp [union]; cases h₁.auth γ k <;> rfl
  · funext γ k; dsimp [union]; cases h₁.frag γ k <;> rfl
  · funext a; dsimp [union]; cases h₁.mapped a <;> rfl

theorem disjoint_union_left {h₁ h₂ h₃ : Heap} (hd12 : h₁.Disjoint h₂) :
    (h₁.union h₂).Disjoint h₃ ↔ h₁.Disjoint h₃ ∧ h₂.Disjoint h₃ := by
  constructor
  · intro hd
    have hphys1 : ∀ a, h₁.phys a = none ∨ h₃.phys a = none ∨
        ∃ b, h₁.phys a = some (.ro b) ∧ h₃.phys a = some (.ro b) := by
      intro a
      rcases hd.1 a with hu | h3 | ⟨b, hu, h3⟩
      · dsimp [union] at hu; cases h : h₁.phys a <;> simp_all
      · exact Or.inr (Or.inl h3)
      · dsimp [union] at hu
        cases h : h₁.phys a with
        | none => exact Or.inl rfl
        | some c => rw [h] at hu; exact Or.inr (Or.inr ⟨b, hu, h3⟩)
    have hphys2 : ∀ a, h₂.phys a = none ∨ h₃.phys a = none ∨
        ∃ b, h₂.phys a = some (.ro b) ∧ h₃.phys a = some (.ro b) := by
      intro a
      rcases hd.1 a with hu | h3 | ⟨b, hu, h3⟩
      · dsimp [union] at hu; cases h : h₁.phys a <;> simp_all
      · exact Or.inr (Or.inl h3)
      · dsimp [union] at hu
        cases h : h₁.phys a with
        | none => rw [h] at hu; exact Or.inr (Or.inr ⟨b, hu, h3⟩)
        | some c =>
          rw [h] at hu
          rcases hd12.1 a with h1 | h2 | ⟨b', h1, h2⟩
          · rw [h] at h1; contradiction
          · exact Or.inl h2
          · rw [h1] at h; cases h; cases hu; exact Or.inr (Or.inr ⟨b, h2, h3⟩)
    have hauth1 : ∀ γ k, h₁.auth γ k = none ∨ h₃.auth γ k = none := by
      intro γ k
      rcases hd.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.auth γ k <;> simp_all
      · exact Or.inr h3
    have hauth2 : ∀ γ k, h₂.auth γ k = none ∨ h₃.auth γ k = none := by
      intro γ k
      rcases hd.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.auth γ k <;> simp_all
      · exact Or.inr h3
    have hfrag1 : ∀ γ k, h₁.frag γ k = none ∨ h₃.frag γ k = none := by
      intro γ k
      rcases hd.2.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.frag γ k <;> simp_all
      · exact Or.inr h3
    have hfrag2 : ∀ γ k, h₂.frag γ k = none ∨ h₃.frag γ k = none := by
      intro γ k
      rcases hd.2.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.frag γ k <;> simp_all
      · exact Or.inr h3
    have hcompat1 : ∀ γ k oa v,
        ((h₁.auth γ k = some oa ∧ h₃.frag γ k = some v) ∨
         (h₃.auth γ k = some oa ∧ h₁.frag γ k = some v)) → oa = some v := by
      intro γ k oa v h
      apply hd.2.2.2.1 γ k oa v
      rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      ·exact Or.inl ⟨by dsimp [union]; rw [ha], hf⟩
      · exact Or.inr ⟨ha, by dsimp [union]; rw [hf]⟩
    have hcompat2 : ∀ γ k oa v,
        ((h₂.auth γ k = some oa ∧ h₃.frag γ k = some v) ∨
         (h₃.auth γ k = some oa ∧ h₂.frag γ k = some v)) → oa = some v := by
      intro γ k oa v h
      apply hd.2.2.2.1 γ k oa v
      rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      · rcases hd12.2.1 γ k with h1 | h2
        · exact Or.inl ⟨by dsimp [union]; rw [h1, ha], hf⟩
        · rw [ha] at h2; contradiction
      · rcases hd12.2.2.1 γ k with h1 | h2
        · exact Or.inr ⟨ha, by dsimp [union]; rw [h1, hf]⟩
        · rw [hf] at h2; contradiction
    have hmapped1 : ∀ a, h₁.mapped a = false ∨ h₃.mapped a = false := by
      intro a
      rcases hd.2.2.2.2 a with hu | h3
      · dsimp [union] at hu; cases h : h₁.mapped a <;> simp_all
      · exact Or.inr h3
    have hmapped2 : ∀ a, h₂.mapped a = false ∨ h₃.mapped a = false := by
      intro a
      rcases hd.2.2.2.2 a with hu | h3
      · dsimp [union] at hu; cases h : h₁.mapped a <;> simp_all
      · exact Or.inr h3
    exact ⟨⟨hphys1, hauth1, hfrag1, hcompat1, hmapped1⟩, ⟨hphys2, hauth2, hfrag2, hcompat2, hmapped2⟩⟩
  · rintro ⟨hd1, hd2⟩
    refine ⟨fun a => ?_, fun γ k => ?_, fun γ k => ?_, fun γ k oa v h => ?_, fun a => ?_⟩
    · dsimp [union]
      cases h : h₁.phys a with
      | none => exact hd2.1 a
      | some c =>
        rcases hd1.1 a with h1 | h3 | ⟨b, h1, h3⟩
        · rw [h] at h1; contradiction
        · exact Or.inr (Or.inl h3)
        · rw [h] at h1; exact Or.inr (Or.inr ⟨b, h1, h3⟩)
    · dsimp [union]
      cases h : h₁.auth γ k with
      | none => exact hd2.2.1 γ k
      | some oa =>
        rcases hd1.2.1 γ k with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3
    · dsimp [union]
      cases h : h₁.frag γ k with
      | none => exact hd2.2.2.1 γ k
      | some v =>
        rcases hd1.2.2.1 γ k with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3
    · rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      · dsimp [union] at ha
        cases h1 : h₁.auth γ k with
        | none =>
          rw [h1] at ha
          exact hd2.2.2.2.1 γ k oa v (Or.inl ⟨ha, hf⟩)
        | some oa' =>
          rw [h1] at ha; cases ha
          exact hd1.2.2.2.1 γ k oa v (Or.inl ⟨h1, hf⟩)
      · dsimp [union] at hf
        cases h1 : h₁.frag γ k with
        | none =>
          rw [h1] at hf
          exact hd2.2.2.2.1 γ k oa v (Or.inr ⟨ha, hf⟩)
        | some v' =>
          rw [h1] at hf; cases hf
          exact hd1.2.2.2.1 γ k oa v (Or.inr ⟨ha, h1⟩)
    · dsimp [union]
      cases h : h₁.mapped a with
      | false => exact hd2.2.2.2.2 a
      | true =>
        rcases hd1.2.2.2.2 a with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3

theorem disjoint_union_right {h₁ h₂ h₃ : Heap} (hd23 : h₂.Disjoint h₃) :
    h₁.Disjoint (h₂.union h₃) ↔ h₁.Disjoint h₂ ∧ h₁.Disjoint h₃ := by
  constructor
  · intro hd
    have hd' := (disjoint_union_left hd23).mp hd.symm
    exact ⟨hd'.1.symm, hd'.2.symm⟩
  · rintro ⟨hd1, hd2⟩
    exact ((disjoint_union_left hd23).mpr ⟨hd1.symm, hd2.symm⟩).symm

theorem GhostValid.of_union_left {h₁ h₂ : Heap} (hv : (h₁.union h₂).GhostValid) :
    h₁.GhostValid := by
  rcases hv with ⟨b, hb⟩
  refine ⟨b, fun γ hγ k => ?_⟩
  have ⟨hau, hfu⟩ := hb γ hγ k
  dsimp [Heap.union] at hau hfu
  constructor
  · cases h : h₁.auth γ k with
    | none => rfl
    | some _ => rw [h] at hau; contradiction
  · cases h : h₁.frag γ k with
    | none => rfl
    | some _ => rw [h] at hfu; contradiction

theorem Matches.of_union_left {h₁ h₂ : Heap} {m : Memory}
    (hm : (h₁.union h₂).Matches m) :
    h₁.Matches m :=
  ⟨fun a c h1 => hm.1 a c (by dsimp [Heap.union]; rw [h1]),
    GhostValid.of_union_left hm.2.1,
    fun a h1 => hm.2.2 a (by dsimp [Heap.union]; rw [h1, Bool.true_or])⟩

end Heap

theorem Entails.refl (P : SepProp) : P ⊢ P := SepProp.entails_iff.mpr fun _ h => h

theorem Satisfies.mono {P Q : SepProp} (h : P ⊢ Q) {m : Memory} (hm : m ⊨ P) : m ⊨ Q := by
  rcases SepProp.satisfies_iff.mp hm with ⟨hp, hP, hM⟩
  exact SepProp.satisfies_iff.mpr ⟨hp, SepProp.entails_iff.mp h hp hP, hM⟩











theorem sepConj_comm (P Q : SepProp) : (P ∗ Q) = (Q ∗ P) := by
  ext h
  simp only [SepProp.holds_sepConj_iff]
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, hp, hq⟩
    exact ⟨h₂, h₁, hd.symm, Heap.union_comm_of_disjoint hd, hq, hp⟩
  · rintro ⟨h₁, h₂, hd, rfl, hq, hp⟩
    exact ⟨h₂, h₁, hd.symm, Heap.union_comm_of_disjoint hd, hp, hq⟩



@[simp]
theorem sepConj_assoc (P Q R : SepProp) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) := by
  ext h
  simp only [SepProp.holds_sepConj_iff]
  constructor
  · rintro ⟨h₁₂, h₃, hd12_3, rfl, ⟨h₁, h₂, hd1_2, rfl, hp, hq⟩, hr⟩
    have ⟨hd1_3, hd2_3⟩ := (Heap.disjoint_union_left hd1_2).mp hd12_3
    exact ⟨h₁, h₂.union h₃, (Heap.disjoint_union_right hd2_3).mpr ⟨hd1_2, hd1_3⟩,
      Heap.union_assoc h₁ h₂ h₃, hp, ⟨h₂, h₃, hd2_3, rfl, hq, hr⟩⟩
  · rintro ⟨h₁, h₂₃, hd1_23, rfl, hp, ⟨h₂, h₃, hd2_3, rfl, hq, hr⟩⟩
    have ⟨hd1_2, hd1_3⟩ := (Heap.disjoint_union_right hd2_3).mp hd1_23
    exact ⟨h₁.union h₂, h₃, (Heap.disjoint_union_left hd1_2).mpr ⟨hd1_3, hd2_3⟩,
      (Heap.union_assoc h₁ h₂ h₃).symm, ⟨h₁, h₂, hd1_2, rfl, hp, hq⟩, hr⟩

/-- Left commutativity of separating conjunction: `P ∗ (Q ∗ R) = Q ∗ (P ∗ R)`. -/
theorem sepConj_left_comm (P Q R : SepProp) : (P ∗ (Q ∗ R)) = (Q ∗ (P ∗ R)) := by
  rw [← sepConj_assoc, sepConj_comm P Q, sepConj_assoc]

instance instAssociativeSepConj : Std.Associative SepProp.sepConj where
  assoc := sepConj_assoc

instance instCommutativeSepConj : Std.Commutative SepProp.sepConj where
  comm := sepConj_comm

theorem Satisfies.of_eq {P Q : SepProp} {m : Memory}
    (h : m ⊨ P) (heq : P = Q := by ac_rfl) : m ⊨ Q :=
  heq ▸ h

@[simp]
theorem emp_sepConj (P : SepProp) : (SepProp.emp ∗ P) = P := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_emp_iff]
  constructor
  · rintro ⟨h₁, h₂, _, rfl, rfl, hp⟩
    simpa using hp
  · intro hp
    exact ⟨Heap.empty, h, Heap.disjoint_empty_left h, (Heap.union_empty_left h).symm, rfl, hp⟩

@[simp]
theorem sepConj_emp (P : SepProp) : (P ∗ SepProp.emp) = P := by
  rw [sepConj_comm, emp_sepConj]


end Arm64
end

section
/-! # Byte-slice ownership: reads, writes, splits

Plain-Lean replacements for the parts of DeepMind's ProofLib (google-deepmind/code-verification
@ 8c8d371f, Apache-2.0, `ProofLib/SepLogic/Bytes.lean`) that the x25519 ladder proofs use:
`a ↦ₛ bs` owns `bs` at `a`; a store to an owned byte updates the list; `pointsTo64` and `memRegion`
are byte slices. -/

set_option autoImplicit false

namespace Arm64

theorem pointsToBytes_cons (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    (a ↦ₛ (b :: bs)) = (a ↦₈ b) ∗ ((a + 1#64) ↦ₛ bs) := rfl
theorem pointsToBytes_nil (a : BitVec 64) : (a ↦ₛ ([] : List (BitVec 8))) = emp := rfl

namespace Heap

/-- `h` with the cell at `x` replaced by `c`. -/
def upd (h : Heap) (x : BitVec 64) (c : HeapCell) : Heap :=
  { h with phys := fun y => if y = x then some c else h.phys y }

theorem upd_union_left (h₁ h₂ : Heap) (x : BitVec 64) (c : HeapCell) :
    (h₁.union h₂).upd x c = (h₁.upd x c).union h₂ := by
  apply Heap.ext
  · funext y; by_cases hy : y = x <;> simp [upd, union, hy]
  · rfl
  · rfl
  · rfl

theorem upd_union_right (h₁ h₂ : Heap) (x : BitVec 64) (c : HeapCell) (hx : h₁.phys x = none) :
    (h₁.union h₂).upd x c = h₁.union (h₂.upd x c) := by
  apply Heap.ext
  · funext y; by_cases hy : y = x
    · subst hy; simp [upd, union, hx]
    · simp [upd, union, hy]
  · rfl
  · rfl
  · rfl

theorem Disjoint.upd_left {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} (c : HeapCell)
    (hx : h₂.phys x = none) : (h₁.upd x c).Disjoint h₂ := by
  refine ⟨fun y => ?_, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩
  by_cases hy : y = x
  · subst hy; exact Or.inr (Or.inl hx)
  · simp only [upd, hy, if_false]; exact hd.1 y

theorem Disjoint.upd_right {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} (c : HeapCell)
    (hx : h₁.phys x = none) : h₁.Disjoint (h₂.upd x c) :=
  (hd.symm.upd_left c hx).symm

theorem rw_phys_right_none {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} {b : BitVec 8}
    (hx : h₁.phys x = some (.rw b)) : h₂.phys x = none := by
  rcases hd.1 x with h | h | ⟨b', h1, _⟩
  · rw [hx] at h; cases h
  · exact h
  · rw [hx] at h1; cases h1

theorem rw_phys_left_none {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} {b : BitVec 8}
    (hx : h₂.phys x = some (.rw b)) : h₁.phys x = none :=
  rw_phys_right_none hd.symm hx

end Heap

/-! ## Memory facts about `write8` -/

namespace Memory

theorem read8_write8_same' (m : Memory) (x : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).read8 x = v := by
  simp [write8, read8]

theorem read8_write8_ne' (m : Memory) {x y : BitVec 64} (v : BitVec 8) (h : y ≠ x) :
    (m.write8 x v).read8 y = m.read8 y := by
  simp [write8, read8, h]

theorem perm_write8' (m : Memory) (x y : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).perm y = m.perm y := by
  by_cases h : y = x
  · subst h; simp only [write8, perm, rawPerm, if_true]
    cases hc : m.cells y with
    | none => rfl
    | some c => obtain ⟨p, b⟩ := c; cases p <;> rfl
  · simp [write8, perm, h]

theorem isAnon_write8' (m : Memory) (x y : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).isAnon y = m.isAnon y := by
  by_cases h : y = x
  · subst h; simp only [write8, isAnon, rawPerm, if_true]
    cases hc : m.cells y with
    | none => rfl
    | some c => obtain ⟨p, b⟩ := c; cases p <;> rfl
  · simp [write8, isAnon, h]

theorem isLazyFree_write8_same' (m : Memory) (x : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).isLazyFree x = false := by
  simp only [write8, isLazyFree, rawPerm, if_true]
  cases hc : m.cells x with
  | none => rfl
  | some c => obtain ⟨p, b⟩ := c; cases p <;> rfl

theorem isLazyFree_write8_ne' (m : Memory) {x y : BitVec 64} (v : BitVec 8) (h : y ≠ x) :
    (m.write8 x v).isLazyFree y = m.isLazyFree y := by
  simp [write8, isLazyFree, h]

end Memory

namespace Memory

theorem KeepsFrozen.refl (m : Memory) : m.KeepsFrozen m := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

theorem KeepsFrozen.trans {m₁ m₂ m₃ : Memory} (h₁ : m₁.KeepsFrozen m₂) (h₂ : m₂.KeepsFrozen m₃) :
    m₁.KeepsFrozen m₃ := by
  intro a ha
  obtain ⟨hb₁, hp₁, hlf₁, ha₁⟩ := h₁ a ha
  have ha₂ : m₂.Frozen a := by unfold Frozen at *; rw [hp₁]; exact ha
  obtain ⟨hb₂, hp₂, hlf₂, ha₂'⟩ := h₂ a ha₂
  exact ⟨hb₂.trans hb₁, hp₂.trans hp₁, hlf₂.trans hlf₁, ha₂'.trans ha₁⟩

theorem keepsFrozen_write8 {m : Memory} {x : BitVec 64} (h : m.canWrite x 1 = true) (v : BitVec 8) :
    m.KeepsFrozen (m.write8 x v) := by
  intro a ha
  have hw : (m.perm x).w = true := by
    simp only [canWrite, allPerm, Bool.and_true, Bool.and_eq_true] at h; exact h.1
  have hne : a ≠ x := by
    intro e; subst e
    unfold Frozen at ha
    cases hp : m.perm a with
    | none => rw [hp] at hw; simp at hw
    | some p =>
      rw [hp] at hw ha; simp [Option.frozen, Perm.frozen] at hw ha; simp_all
  exact ⟨read8_write8_ne' _ _ hne, perm_write8' _ _ _ _, isLazyFree_write8_ne' _ _ hne, isAnon_write8' _ _ _ _⟩

end Memory

namespace Heap

theorem Matches.upd_write {h : Heap} {m : Memory} (hm : h.Matches m) {x : BitVec 64} {b : BitVec 8}
    (hx : h.phys x = some (.rw b)) (v : BitVec 8) :
    (h.upd x (.rw v)).Matches (m.write8 x v) := by
  refine ⟨fun y c hy => ?_, hm.2.1, fun y hy => ?_⟩
  · by_cases hyx : y = x
    · subst hyx
      simp only [upd, if_true, Option.some.injEq] at hy
      subst hy
      have h0 := hm.1 y _ hx
      simp only at h0
      refine ⟨Memory.read8_write8_same' _ _ _, ?_, Memory.isLazyFree_write8_same' _ _ _⟩
      rw [Memory.perm_write8']; exact h0.2.1
    · simp only [upd, hyx, if_false] at hy
      have h0 := hm.1 y c hy
      rw [Memory.read8_write8_ne' _ _ hyx, Memory.perm_write8', Memory.isLazyFree_write8_ne' _ _ hyx]
      exact h0
  · have h0 := hm.2.2 y hy
    rw [Memory.perm_write8', Memory.isAnon_write8']; exact h0

end Heap

/-! ## Byte slices as heaps -/

theorem bytes_phys : ∀ {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap},
    (a ↦ₛ bs).holds h → ∀ (j : Nat) (hj : j < bs.length),
      h.phys (a + BitVec.ofNat 64 j) = some (.rw bs[j])
  | _, [], _, _, j, hj => by simp at hj
  | a, b :: bs, h, hh, j, hj => by
    obtain ⟨h1, h2, hd, rfl, h1e, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
    rw [holds_pointsTo8_iff] at h1e; subst h1e
    cases j with
    | zero => simp [Heap.union, Heap.singleton]
    | succ j =>
      have ih := bytes_phys h2h j (by simp at hj; omega)
      have ha : a + BitVec.ofNat 64 (j + 1) = a + 1#64 + BitVec.ofNat 64 j := by
        rw [BitVec.add_assoc]; congr 1; bv_omega
      have hne : a + 1#64 + BitVec.ofNat 64 j ≠ a := by
        intro he
        have := Heap.rw_phys_left_none hd ih
        rw [he] at this; simp [Heap.singleton] at this
      rw [ha]
      simp only [Heap.union, Heap.singleton, hne, if_false, ih, List.getElem_cons_succ]

theorem bytes_upd : ∀ {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap},
    (a ↦ₛ bs).holds h → ∀ (j : Nat) (hj : j < bs.length) (v : BitVec 8),
      (a ↦ₛ bs.set j v).holds (h.upd (a + BitVec.ofNat 64 j) (.rw v))
  | _, [], _, _, j, hj, _ => by simp at hj
  | a, b :: bs, h, hh, j, hj, v => by
    obtain ⟨h1, h2, hd, rfl, h1e, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
    rw [holds_pointsTo8_iff] at h1e; subst h1e
    have h2a : h2.phys a = none :=
      Heap.rw_phys_right_none hd (b := b) (by simp [Heap.singleton])
    cases j with
    | zero =>
      simp only [List.set_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      rw [Heap.upd_union_left]
      refine SepProp.holds_sepConj_iff.mpr ⟨Heap.singleton a v, h2, ?_, ?_, rfl, h2h⟩
      · exact Heap.Disjoint.of_phys_left rfl rfl (fun y => by
          by_cases hy : y = a
          · subst hy; exact Or.inr (Or.inl h2a)
          · exact Or.inl (by simp [Heap.singleton, hy])) rfl
      · apply Heap.ext
        · funext y; by_cases hy : y = a <;> simp [Heap.upd, Heap.union, Heap.singleton, hy]
        · rfl
        · rfl
        · rfl
    | succ j =>
      have hj' : j < bs.length := by simp at hj; omega
      have ih := bytes_upd h2h j hj' v
      have ha : a + BitVec.ofNat 64 (j + 1) = a + 1#64 + BitVec.ofNat 64 j := by
        rw [BitVec.add_assoc]; congr 1; bv_omega
      have hph := bytes_phys h2h j hj'
      have hne : a + 1#64 + BitVec.ofNat 64 j ≠ a := by
        intro he; rw [he] at hph; rw [h2a] at hph; cases hph
      have h1x : (Heap.singleton a b).phys (a + 1#64 + BitVec.ofNat 64 j) = none := by
        simp [Heap.singleton, hne]
      rw [ha, Heap.upd_union_right _ _ _ _ h1x, List.set_cons_succ]
      exact SepProp.holds_sepConj_iff.mpr ⟨_, _, hd.upd_right _ h1x, rfl, rfl, ih⟩

/-! ## Satisfaction-level reads and writes -/

theorem sat_bytes_read {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (j : Nat) (hj : j < bs.length) :
    m.read8 (a + BitVec.ofNat 64 j) = bs[j] ∧ m.perm (a + BitVec.ofNat 64 j) = some Perm.rw ∧
      m.isLazyFree (a + BitVec.ofNat 64 j) = false := by
  obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
  obtain ⟨h1, h2, hd, rfl, h1h, _⟩ := SepProp.holds_sepConj_iff.mp hh
  have hp := bytes_phys h1h j hj
  have := (Heap.Matches.of_union_left hm).1 _ _ hp
  exact this

theorem sat_bytes_write {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (j : Nat) (hj : j < bs.length) (v : BitVec 8) :
    (m.write8 (a + BitVec.ofNat 64 j) v) ⊨ (a ↦ₛ bs.set j v) ∗ F := by
  obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
  obtain ⟨h1, h2, hd, rfl, h1h, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
  have hp := bytes_phys h1h j hj
  refine SepProp.satisfies_iff.mpr ⟨(h1.upd (a + BitVec.ofNat 64 j) (.rw v)).union h2, ?_, ?_⟩
  · exact SepProp.holds_sepConj_iff.mpr ⟨_, _, hd.upd_left _ (Heap.rw_phys_right_none hd hp), rfl,
      bytes_upd h1h j hj v, h2h⟩
  · rw [← Heap.upd_union_left]
    exact hm.upd_write (b := bs[j]) (by simp [Heap.union, hp]) v

/-! ## Splitting byte slices -/

theorem pointsToBytes_append (a : BitVec 64) (xs ys : List (BitVec 8)) :
    (a ↦ₛ (xs ++ ys)) = (a ↦ₛ xs) ∗ ((a + BitVec.ofNat 64 xs.length) ↦ₛ ys) := by
  induction xs generalizing a with
  | nil => simp [pointsToBytes_nil]
  | cons x xs ih =>
    rw [List.cons_append, pointsToBytes_cons, pointsToBytes_cons, ih, sepConj_assoc]
    have e : a + 1#64 + BitVec.ofNat 64 xs.length = a + BitVec.ofNat 64 (x :: xs).length := by
      simp only [List.length_cons]; rw [BitVec.add_assoc]; congr 1; bv_omega
    rw [e]

theorem pointsToBytes_split (a : BitVec 64) (bs : List (BitVec 8)) (n : Nat) (hn : n ≤ bs.length) :
    (a ↦ₛ bs) = (a ↦ₛ bs.take n) ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bs.drop n) := by
  have h := pointsToBytes_append a (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take_of_le hn] at h
  exact h

/-- Unpack a 64-bit word into its 8 little-endian bytes. -/
def unpack64 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]

@[simp] theorem unpack64_length (v : BitVec 64) : (unpack64 v).length = 8 := rfl

theorem pointsTo64_eq_bytes (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦ₛ unpack64 v) := by
  simp only [pointsTo64, unpack64, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_zero]
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_omega
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_omega
  have h4 : a + 3#64 + 1#64 = a + 4#64 := by bv_omega
  have h5 : a + 4#64 + 1#64 = a + 5#64 := by bv_omega
  have h6 : a + 5#64 + 1#64 = a + 6#64 := by bv_omega
  have h7 : a + 6#64 + 1#64 = a + 7#64 := by bv_omega
  rw [h2, h3, h4, h5, h6, h7]

end Arm64
end

section
/-! # Regions, existentials and pure facts

`memRegion a n` (a stack frame) is a byte slice of length `n` with unknown contents; pure
assertions and separating existentials move in and out of `⊨`. -/

set_option autoImplicit false

namespace Arm64

theorem sepConj_mono {P P' Q Q' : SepProp} (h1 : P ⊢ P') (h2 : Q ⊢ Q') : (P ∗ Q) ⊢ (P' ∗ Q') := by
  intro h hh
  obtain ⟨h₁, h₂, hd, rfl, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  exact SepProp.holds_sepConj_iff.mpr ⟨h₁, h₂, hd, rfl, h1 _ hp, h2 _ hq⟩

theorem sat_sep_mono {m : Memory} {P P' Q : SepProp} (hs : m ⊨ P ∗ Q) (h1 : P ⊢ P') :
    m ⊨ P' ∗ Q :=
  Satisfies.mono (sepConj_mono h1 (Entails.refl Q)) hs

theorem pure_sepConj_holds {φ : Prop} {P : SepProp} {h : Heap} :
    (⌜φ⌝ ∗ P).holds h ↔ φ ∧ P.holds h := by
  constructor
  · intro hh
    obtain ⟨h₁, h₂, _, rfl, ⟨rfl, hφ⟩, hp⟩ := SepProp.holds_sepConj_iff.mp hh
    exact ⟨hφ, by rw [Heap.union_empty_left]; exact hp⟩
  · rintro ⟨hφ, hp⟩
    exact SepProp.holds_sepConj_iff.mpr ⟨Heap.empty, h, Heap.disjoint_empty_left h,
      (Heap.union_empty_left h).symm, ⟨rfl, hφ⟩, hp⟩

theorem sat_pure_sep {m : Memory} {φ : Prop} {P : SepProp} : (m ⊨ ⌜φ⌝ ∗ P) ↔ φ ∧ (m ⊨ P) := by
  constructor
  · intro hs
    obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
    have := pure_sepConj_holds.mp hh
    exact ⟨this.1, SepProp.satisfies_iff.mpr ⟨h, this.2, hm⟩⟩
  · rintro ⟨hφ, hs⟩
    obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
    exact SepProp.satisfies_iff.mpr ⟨h, pure_sepConj_holds.mpr ⟨hφ, hh⟩, hm⟩

theorem sepExists_sepConj {α : Sort _} (P : α → SepProp) (Q : SepProp) :
    ((∃∗ x, P x) ∗ Q) = ∃∗ x, (P x ∗ Q) := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_sepExists_iff]
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, ⟨x, hp⟩, hq⟩; exact ⟨x, h₁, h₂, hd, rfl, hp, hq⟩
  · rintro ⟨x, h₁, h₂, hd, rfl, hp, hq⟩; exact ⟨h₁, h₂, hd, rfl, ⟨x, hp⟩, hq⟩

theorem sat_sepExists {m : Memory} {α : Sort _} {P : α → SepProp} :
    (m ⊨ ∃∗ x, P x) ↔ ∃ x, m ⊨ P x := by
  constructor
  · intro hs
    obtain ⟨h, ⟨x, hp⟩, hm⟩ := SepProp.satisfies_iff.mp hs
    exact ⟨x, SepProp.satisfies_iff.mpr ⟨h, hp, hm⟩⟩
  · rintro ⟨x, hs⟩
    obtain ⟨h, hp, hm⟩ := SepProp.satisfies_iff.mp hs
    exact SepProp.satisfies_iff.mpr ⟨h, ⟨x, hp⟩, hm⟩

theorem regionHeap_phys (base : BitVec 64) (len : Nat) (m : Memory) (y : BitVec 64) :
    (regionHeap base len m).phys y =
      if (y - base).toNat < len then some (.rw (m.read8 y)) else none := by
  unfold regionHeap InRegion; exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

/-! ## Byte-slice heaps carry no ghost state and nothing outside the slice -/

theorem bytes_shape : ∀ {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap},
    (a ↦ₛ bs).holds h →
      h.auth = (fun _ _ => none) ∧ h.frag = (fun _ _ => none) ∧ h.mapped = (fun _ => false) ∧
      ∀ y, bs.length ≤ (y - a).toNat → h.phys y = none
  | a, [], h, hh => by
    rw [pointsToBytes_nil, SepProp.holds_emp_iff] at hh; subst hh
    exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  | a, b :: bs, h, hh => by
    obtain ⟨h1, h2, _, rfl, h1e, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
    rw [holds_pointsTo8_iff] at h1e; subst h1e
    obtain ⟨ha, hf, hm, hp⟩ := bytes_shape h2h
    refine ⟨?_, ?_, ?_, fun y hy => ?_⟩
    · funext γ k; simp [Heap.union, Heap.singleton, ha]
    · funext γ k; simp [Heap.union, Heap.singleton, hf]
    · funext y; simp [Heap.union, Heap.singleton, hm]
    · have hya : y ≠ a := by
        intro he; subst he; simp at hy
      have : bs.length ≤ (y - (a + 1#64)).toNat := by
        simp only [List.length_cons] at hy; bv_omega
      simp [Heap.union, Heap.singleton, hya, hp y this]

theorem bytes_entails_memRegion (a : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦ₛ bs) ⊢ memRegion a bs.length := by
  intro h hh
  obtain ⟨ha, hf, hm, hp⟩ := bytes_shape hh
  refine ⟨Memory.ofFn (fun y => bs.getD (y - a).toNat 0), ?_⟩
  show h = regionHeap a bs.length _
  apply Heap.ext
  · funext y
    rw [regionHeap_phys]
    split
    · rename_i hy
      have := bytes_phys hh (y - a).toNat hy
      rw [show a + BitVec.ofNat 64 (y - a).toNat = y by bv_omega] at this
      rw [this]
      simp only [Memory.read8, Memory.ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy,
        Option.getD_some]
    · rename_i hy; exact hp y (by omega)
  · exact ha
  · exact hf
  · exact hm

theorem regionHeap_holds_bytes : ∀ (n : Nat) (a : BitVec 64) (m : Memory), n < 2 ^ 64 →
    (a ↦ₛ m.readBytes a n).holds (regionHeap a n m)
  | 0, a, m, _ => by
    show _ = _
    apply Heap.ext
    · funext y; simp [regionHeap, InRegion, Heap.empty]
    · rfl
    · rfl
    · rfl
  | n + 1, a, m, hn => by
    have ih := regionHeap_holds_bytes n (a + 1#64) m (by omega)
    refine SepProp.holds_sepConj_iff.mpr ⟨Heap.singleton a (m.read8 a), regionHeap (a + 1#64) n m,
      ?_, ?_, rfl, ih⟩
    · exact Heap.Disjoint.of_phys_left rfl rfl (fun y => by
        by_cases hy : y = a
        · subst hy; right; left
          rw [regionHeap_phys, if_neg]; bv_omega
        · left; simp [Heap.singleton, hy]) rfl
    · apply Heap.ext
      · funext y
        by_cases hy : y = a
        · subst hy
          simp only [Heap.union, Heap.singleton, if_true, regionHeap_phys]
          rw [if_pos (by bv_omega)]
        · simp only [Heap.union, Heap.singleton, hy, if_false, regionHeap_phys]
          have e : ((y - a).toNat < n + 1) ↔ ((y - (a + 1#64)).toNat < n) := by
            constructor <;> intro h <;> bv_omega
          by_cases hc : (y - (a + 1#64)).toNat < n
          · rw [if_pos (e.mpr hc), if_pos hc]
          · rw [if_neg (fun h => hc (e.mp h)), if_neg hc]
      · rfl
      · rfl
      · rfl

theorem readBytes_length (m : Memory) : ∀ (a : BitVec 64) (n : Nat), (m.readBytes a n).length = n
  | _, 0 => rfl
  | a, n + 1 => by simp [Memory.readBytes, readBytes_length m (a + 1#64) n]

theorem memRegion_entails_bytes (a : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    memRegion a n ⊢ ∃∗ bs, ⌜bs.length = n⌝ ∗ (a ↦ₛ bs) := by
  intro h hh
  obtain ⟨m, hm⟩ := hh
  change h = regionHeap a n m at hm
  subst hm
  exact ⟨m.readBytes a n, pure_sepConj_holds.mpr ⟨readBytes_length m a n,
    regionHeap_holds_bytes n a m hn⟩⟩

end Arm64
end

section
/-! # 64-bit cells and byte reads: values and permissions from ownership -/

set_option autoImplicit false

namespace Arm64

theorem dand {P : Prop} [Decidable P] (h : P) (a : Bool) : (decide P && a) = a := by simp [h]

theorem concat8_extract (v : BitVec 64) :
    v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 32 8 ++
      v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> simp <;> first | (intro; omega) | (rw [dand] <;> first | omega | (congr 1; omega))

theorem canRead_of {m : Memory} : ∀ {x : BitVec 64} {n : Nat},
    (∀ i < n, (m.perm (x + BitVec.ofNat 64 i)).r = true ∧
      m.isLazyFree (x + BitVec.ofNat 64 i) = false) → m.canRead x n = true
  | _, 0, _ => rfl
  | x, n + 1, h => by
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    have ih := canRead_of (x := x + 1#64) (n := n) (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show x + BitVec.ofNat 64 (i + 1) = x + 1#64 + BitVec.ofNat 64 i by
        rw [BitVec.add_assoc]; congr 1; bv_omega] at this)
    simp only [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree] at ih ⊢
    simp only [Bool.and_eq_true] at ih
    simp [h0.1, h0.2, ih.1, ih.2]

theorem canWrite_of {m : Memory} : ∀ {x : BitVec 64} {n : Nat},
    (∀ i < n, m.perm (x + BitVec.ofNat 64 i) = some Perm.rw) → m.canWrite x n = true
  | _, 0, _ => rfl
  | x, n + 1, h => by
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    have ih := canWrite_of (x := x + 1#64) (n := n) (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show x + BitVec.ofNat 64 (i + 1) = x + 1#64 + BitVec.ofNat 64 i by
        rw [BitVec.add_assoc]; congr 1; bv_omega] at this)
    simp only [Memory.canWrite, Memory.allPerm] at ih ⊢
    simp [h0, ih, Perm.rw]

/-- Byte `i` of `unpack64 v`. -/
theorem unpack64_getElem (v : BitVec 64) (i : Nat) (hi : i < 8) :
    (unpack64 v)[i]'(by simp; omega) = v.extractLsb' (8 * i) 8 := by
  interval_cases i <;> rfl

theorem sat64_byte {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F)
    (i : Nat) (hi : i < 8) :
    m.read8 (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 ∧
      m.perm (a + BitVec.ofNat 64 i) = some Perm.rw ∧
      m.isLazyFree (a + BitVec.ofNat 64 i) = false := by
  rw [pointsTo64_eq_bytes] at hs
  have := sat_bytes_read hs i (by simp; omega)
  rwa [unpack64_getElem v i hi] at this

theorem sat64_read {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F) :
    m.read64 a = v ∧ m.canRead a 8 = true ∧ m.canWrite a 8 = true := by
  refine ⟨?_, canRead_of (fun i hi => ?_), canWrite_of (fun i hi => (sat64_byte hs i hi).2.1)⟩
  · have h0 := (sat64_byte hs 0 (by omega)).1
    have h1 := (sat64_byte hs 1 (by omega)).1
    have h2 := (sat64_byte hs 2 (by omega)).1
    have h3 := (sat64_byte hs 3 (by omega)).1
    have h4 := (sat64_byte hs 4 (by omega)).1
    have h5 := (sat64_byte hs 5 (by omega)).1
    have h6 := (sat64_byte hs 6 (by omega)).1
    have h7 := (sat64_byte hs 7 (by omega)).1
    simp only [BitVec.ofNat_eq_ofNat, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
    simp only [Memory.read64]
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
    exact concat8_extract v
  · have := sat64_byte hs i hi
    rw [this.2.1]; exact ⟨rfl, this.2.2⟩

theorem keepsFrozen_write8_of_rw {m : Memory} {x : BitVec 64} (h : m.perm x = some Perm.rw) (v : BitVec 8) :
    m.KeepsFrozen (m.write8 x v) :=
  Memory.keepsFrozen_write8 (canWrite_of (n := 1) (fun i hi => by
    have : i = 0 := by omega
    subst this; simpa using h)) v

theorem keepsFrozen_write64_of_rw {m : Memory} {a : BitVec 64}
    (h : ∀ i < 8, m.perm (a + BitVec.ofNat 64 i) = some Perm.rw) (w : BitVec 64) :
    m.KeepsFrozen (m.write64 a w) := by
  have p : ∀ (m' : Memory) (i : Nat), i < 8 → (∀ y, m'.perm y = m.perm y) →
      m'.perm (a + BitVec.ofNat 64 i) = some Perm.rw := fun m' i hi hm => (hm _).trans (h i hi)
  have pw : ∀ (m' : Memory) (x : BitVec 64) (v : BitVec 8), (∀ y, m'.perm y = m.perm y) →
      ∀ y, (m'.write8 x v).perm y = m.perm y := fun m' x v hm y => (Memory.perm_write8' _ _ _ _).trans (hm y)
  simp only [Memory.write64]
  have st : ∀ (m' : Memory) (k : Nat), k < 8 → (∀ y, m'.perm y = m.perm y) → ∀ v : BitVec 8,
      m'.KeepsFrozen (m'.write8 (a + BitVec.ofNat 64 k) v) ∧
      ∀ y, (m'.write8 (a + BitVec.ofNat 64 k) v).perm y = m.perm y :=
    fun m' k hk hm v => ⟨keepsFrozen_write8_of_rw (p m' k hk hm) v, pw m' _ v hm⟩
  obtain ⟨k0, q0⟩ := st m 0 (by omega) (fun _ => rfl) (w.extractLsb' 0 8)
  obtain ⟨k1, q1⟩ := st _ 1 (by omega) q0 (w.extractLsb' 8 8)
  obtain ⟨k2, q2⟩ := st _ 2 (by omega) q1 (w.extractLsb' 16 8)
  obtain ⟨k3, q3⟩ := st _ 3 (by omega) q2 (w.extractLsb' 24 8)
  obtain ⟨k4, q4⟩ := st _ 4 (by omega) q3 (w.extractLsb' 32 8)
  obtain ⟨k5, q5⟩ := st _ 5 (by omega) q4 (w.extractLsb' 40 8)
  obtain ⟨k6, q6⟩ := st _ 6 (by omega) q5 (w.extractLsb' 48 8)
  obtain ⟨k7, _⟩ := st _ 7 (by omega) q6 (w.extractLsb' 56 8)
  exact k0.trans (k1.trans (k2.trans (k3.trans (k4.trans (k5.trans (k6.trans k7))))))

theorem sat64_write {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F)
    (w : BitVec 64) : m.write64 a w ⊨ (a ↦₆₄ w) ∗ F := by
  rw [pointsTo64_eq_bytes] at hs ⊢
  have e : ∀ i : Nat, a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 i := fun _ => rfl
  have s0 := sat_bytes_write hs 0 (by simp) (w.extractLsb' 0 8)
  have s1 := sat_bytes_write s0 1 (by simp) (w.extractLsb' 8 8)
  have s2 := sat_bytes_write s1 2 (by simp) (w.extractLsb' 16 8)
  have s3 := sat_bytes_write s2 3 (by simp) (w.extractLsb' 24 8)
  have s4 := sat_bytes_write s3 4 (by simp) (w.extractLsb' 32 8)
  have s5 := sat_bytes_write s4 5 (by simp) (w.extractLsb' 40 8)
  have s6 := sat_bytes_write s5 6 (by simp) (w.extractLsb' 48 8)
  have s7 := sat_bytes_write s6 7 (by simp) (w.extractLsb' 56 8)
  clear e
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at s7
  simp only [Memory.write64, BitVec.add_zero]
  convert s7 using 3
  simp [unpack64]

end Arm64
end

section
/-! # Instruction fetch in the placed x25519 library, and execution by backward chaining

`Step` does not depend on which block's program runs it when no hooks are installed, so a callee's
contract (stated for its own block) is usable from the caller's block. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

/-- Block `i` of the library. -/
def blk (i : Nat) : CodeBlock := x25519CliMultiLib.blocks.getD i { code := [] }

/-- Block `i`'s placed program, as in `fnOk`. -/
abbrev bprog (mpl : MultiPlacement) (i : Nat) : Program := x25519CliMultiLib.blockProgram mpl i

theorem hook_none (mpl : MultiPlacement) (i : Nat) (pc : BitVec 64) : (bprog mpl i).externAt? pc = none := by
  simp only [bprog, Program.externAt?, Program.hookAtOff?, MultiPlacedLib.blockProgram, PlacedLib.program]
  simp

theorem step_transfer {p q : Program} (hp : ∀ pc, p.externAt? pc = none)
    (hq : ∀ pc, q.externAt? pc = none) (hs : p.svc = q.svc) {s s' : State}
    (h : Step p s s') : Step q s s' := by
  have hf : ∀ m pc, p.fetchMem m pc = q.fetchMem m pc := by
    intro m pc; simp only [Program.fetchMem, hp, hq]
  cases h with
  | exec hrun hfe =>
    have := Step.exec (prog := q) hrun (by rw [← hf]; exact hfe)
    simpa only [Program.evalInst, hs] using this
  | halt_unmapped hrun hfe _ =>
    exact Step.halt_unmapped hrun (by rw [← hf]; exact hfe) (hq _)
  | externHook _ he _ _ => rw [hp] at he; cases he
  | extern_fault _ he _ => rw [hp] at he; cases he

theorem steps_transfer {p q : Program} (hp : ∀ pc, p.externAt? pc = none)
    (hq : ∀ pc, q.externAt? pc = none) (hs : p.svc = q.svc) {s s' : State}
    (h : Steps p s s') : Steps q s s' := by
  induction h with
  | refl => exact Steps.refl _
  | step h1 _ ih => exact Steps.step (step_transfer hp hq hs h1) ih

theorem Steps.trans' {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Steps p b c) :
    Steps p a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

theorem bsteps_transfer {mpl : MultiPlacement} {i j : Nat} {s s' : State}
    (h : Steps (bprog mpl i) s s') : Steps (bprog mpl j) s s' :=
  steps_transfer (hook_none mpl i) (hook_none mpl j) rfl h

/-! ## Reaching a final state -/

def Reach (p : Program) (s : State) (Q : State → Prop) : Prop := ∃ sf, Steps p s sf ∧ Q sf

theorem Reach.done {p : Program} {s : State} {Q : State → Prop} (h : Q s) : Reach p s Q :=
  ⟨s, Steps.refl s, h⟩

theorem Reach.exec {p : Program} {s : State} {Q : State → Prop} {i : Instr}
    (hrun : s.status = .Running) (hf : p.fetchMem s.mem s.pc = some i)
    (h : Reach p (execInstWithSvc (evalSvc p.svc) i s) Q) : Reach p s Q := by
  obtain ⟨sf, hst, hq⟩ := h
  exact ⟨sf, Steps.step (Step.exec hrun hf) hst, hq⟩

theorem Reach.steps {p : Program} {s s' : State} {Q : State → Prop} (h1 : Steps p s s')
    (h : Reach p s' Q) : Reach p s Q := by
  obtain ⟨sf, hst, hq⟩ := h
  exact ⟨sf, Steps.trans' h1 hst, hq⟩

/-! ## Fetching from the loaded code -/

theorem length_bytesOfWordLE (w : BitVec 32) : (bytesOfWordLE w).length = 4 := by
  simp [bytesOfWordLE, bytesLE]

theorem drop_take_flatMap_bytesOfWordLE {α : Type} (g : α → BitVec 32) :
    ∀ (L : List α) (j : Nat) (hj : j < L.length),
      ((L.flatMap fun a => bytesOfWordLE (g a)).drop (4 * j)).take 4 =
        bytesOfWordLE (g (L[j]'hj))
  | [], _, hj => by simp at hj
  | a :: L, 0, _ => by
    simp only [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.getElem_cons_zero]
    rw [List.take_append_of_le_length (by simp [length_bytesOfWordLE])]
    exact List.take_of_length_le (by simp [length_bytesOfWordLE])
  | a :: L, j + 1, hj => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [show 4 * (j + 1) = (bytesOfWordLE (g a)).length + 4 * j by
          simp [length_bytesOfWordLE]; omega,
      ← List.drop_drop, List.drop_left]
    exact drop_take_flatMap_bytesOfWordLE g L j (by simp at hj; omega)

theorem take4_drop_patched {b : CodeBlock} {pl : Placement} {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ b.code.length) :
    ((b.patched pl).drop off).take 4 = bytesOfWordLE (b.patchedWord pl off) := by
  have hj : off / 4 < (List.range (b.code.length / 4)).length := by
    simp only [List.length_range]; omega
  have h := drop_take_flatMap_bytesOfWordLE (fun j => b.patchedWord pl (4 * j))
    (List.range (b.code.length / 4)) (off / 4) hj
  rw [List.getElem_range, show 4 * (off / 4) = off by omega] at h
  exact h

theorem sum_replicate' (n k : Nat) : (List.replicate n k).sum = n * k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

theorem patched_length (b : CodeBlock) (pl : Placement) (h4 : b.code.length % 4 = 0) :
    (b.patched pl).length = b.code.length := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE, List.map_const', List.length_range, sum_replicate']
  omega

theorem codeLoaded_cell {p : Program} {m : Memory} (h : p.CodeLoaded m) (i : Nat)
    (hi : i < p.code.length) :
    m.read8 (p.base + BitVec.ofNat 64 i) = p.code[i] ∧
    m.perm (p.base + BitVec.ofNat 64 i) = some Perm.rx := by
  unfold Program.CodeLoaded at h
  exact ⟨(h.2.2 i hi).1, (h.2.2 i hi).2.1⟩

theorem blocks_length : x25519CliMultiLib.blocks.length = 19 := rfl

theorem blk_placeable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {i : Nat}
    (hi : i < 19) : (blk i).Placeable (x25519CliMultiLib.blockPlacement mpl i) := by
  have := hP.blocks_ok i (by rw [blocks_length]; exact hi)
  simpa [blk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [blocks_length]; exact hi)]
    using this

theorem read8_code {mpl : MultiPlacement} {m : Memory} {i : Nat}
    (hCL : (bprog mpl i).CodeLoaded m) (h4 : (blk i).code.length % 4 = 0) {off k : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ (blk i).code.length) (hk : k < 4) :
    m.read8 (mpl.base i + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      ((blk i).patchedWord (x25519CliMultiLib.blockPlacement mpl i) off).extractLsb' (8 * k) 8 ∧
    m.perm (mpl.base i + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (bprog mpl i).code.length = (blk i).code.length := patched_length _ _ h4
  have h := codeLoaded_cell hCL (off + k) (by omega)
  have ha : mpl.base i + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
      (bprog mpl i).base + BitVec.ofNat 64 (off + k) := by
    show _ = mpl.base i + _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  refine ⟨?_, h.2⟩
  rw [h.1]
  have ht := take4_drop_patched (b := blk i) (pl := x25519CliMultiLib.blockPlacement mpl i) hal hlen
  have hlp : ((blk i).patched (x25519CliMultiLib.blockPlacement mpl i)).length = (blk i).code.length :=
    patched_length _ _ h4
  have e1 : (bprog mpl i).code[off + k]'(by omega) =
      ((((blk i).patched (x25519CliMultiLib.blockPlacement mpl i)).drop off).take 4)[k]'(by
        simp only [List.length_take, List.length_drop, hlp]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + j < 32 := by omega
  simp [hj, this]; omega

theorem concat_bytes32 (w : BitVec 32) :
    (w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8) = w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> simp <;> first | (intro; omega) | (rw [dand] <;> first | omega | (congr 1; omega))

/-- The instruction fetched at offset `off` of block `i`, by any hook-free program. -/
theorem fetch_word {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m : Memory}
    {i : Nat} (hi : i < 19) (hCL : (bprog mpl i).CodeLoaded m) {off : Nat} (hal : off % 4 = 0)
    (hlen : off + 4 ≤ (blk i).code.length) (p : Program) (hp : ∀ pc, p.externAt? pc = none) :
    p.fetchMem m (mpl.base i + BitVec.ofNat 64 off) =
      decode ((blk i).patchedWord (x25519CliMultiLib.blockPlacement mpl i) off) := by
  have hPl := blk_placeable hP hi
  have h4 : (blk i).code.length % 4 = 0 := hPl.len_aligned
  have hb4 : (mpl.base i).toNat % 4 = 0 := by
    have h1 := hPl.base_aligned; have h2 := hPl.align_pos
    simp only [MultiPlacedLib.blockPlacement] at h1
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h2.2) (Nat.dvd_of_mod_eq_zero h1))
  have hnw : (mpl.base i).toNat + (blk i).code.length ≤ 2 ^ 64 := hPl.no_wrap
  have hpc : (mpl.base i + BitVec.ofNat 64 off).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
    have h2 : ((mpl.base i).toNat + off) % 2 ^ 64 = (mpl.base i).toNat + off :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]; omega
  have r0 := read8_code hCL h4 hal hlen (k := 0) (by omega)
  have r1 := read8_code hCL h4 hal hlen (k := 1) (by omega)
  have r2 := read8_code hCL h4 hal hlen (k := 2) (by omega)
  have r3 := read8_code hCL h4 hal hlen (k := 3) (by omega)
  simp only [Program.fetchMem, hp, Option.isSome_none, Bool.false_eq_true, if_false, hpc,
    ne_eq, not_true_eq_false]
  generalize mpl.base i + BitVec.ofNat 64 off = a at *
  generalize (blk i).patchedWord (x25519CliMultiLib.blockPlacement mpl i) off = w at *
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at r0 r1 r2 r3
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at r0
  have hx : m.canExec a 4 = true := by
    simp only [Memory.canExec, Memory.allPerm, BitVec.add_assoc, BitVec.reduceAdd]
    simp [r0.2, r1.2, r2.2, r3.2, Perm.rx]
  simp only [hx, Bool.not_true, Bool.false_eq_true, if_false]
  congr 1
  simp only [Memory.read32, BitVec.add_zero]
  rw [r0.1, r1.1, r2.1, r3.1]
  exact concat_bytes32 w

theorem patchedWord_plain (b : CodeBlock) (pl : Placement) {off : Nat} (h : b.relocAt? off = none) :
    b.patchedWord pl off = b.wordAt off := by
  simp [CodeBlock.patchedWord, h]

end X25519Dalek.EMulB
end

section
/-! # Abstract machine states

Every state inside a block proof is `mkS s0 pc r sp ps m v`: the state `s0` with the program
counter, the general registers, the stack pointer, the flags, the memory and the vector registers
replaced. The instruction evaluators map such states to such states, and these lemmas let `simp`
compute the result without unfolding `State`. -/

set_option autoImplicit false

namespace X25519Dalek.EMulB

open Arm64

def upd {α : Type} (r : BitVec 5 → α) (i : BitVec 5) (v : α) : BitVec 5 → α :=
  fun j => if j = i then v else r j

@[simp] theorem upd_same {α : Type} (r : BitVec 5 → α) (i : BitVec 5) (v : α) : upd r i v i = v := by
  simp [upd]

theorem upd_ne {α : Type} (r : BitVec 5 → α) {i j : BitVec 5} (v : α) (h : j ≠ i) :
    upd r i v j = r j := by
  simp [upd, h]

/-- `upd` at literal indices: `simp` decides the index comparison. -/
@[simp] theorem upd_apply {α : Type} (r : BitVec 5 → α) (i j : BitVec 5) (v : α) :
    upd r i v j = if j = i then v else r j := rfl

def mkS (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64) (ps : PState)
    (m : Memory) (v : BitVec 5 → BitVec 128) : State :=
  { s0 with pc := pc, regs := ⟨r⟩, sp := sp, pstate := ps, mem := m, vregs := ⟨v⟩ }

section
variable (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64) (ps : PState)
  (m : Memory) (v : BitVec 5 → BitVec 128)

@[simp] theorem mkS_pc : (mkS s0 pc r sp ps m v).pc = pc := rfl
@[simp] theorem mkS_sp : (mkS s0 pc r sp ps m v).sp = sp := rfl
@[simp] theorem mkS_mem : (mkS s0 pc r sp ps m v).mem = m := rfl
@[simp] theorem mkS_pstate : (mkS s0 pc r sp ps m v).pstate = ps := rfl
@[simp] theorem mkS_status : (mkS s0 pc r sp ps m v).status = s0.status := rfl
@[simp] theorem mkS_spAligned : (mkS s0 pc r sp ps m v).spAligned = ((sp &&& 0b1111#64) == 0#64) := rfl

@[simp] theorem mkS_readGpr (i : BitVec 5) :
    (mkS s0 pc r sp ps m v).readReg64 (.gpr i) = if i = 31#5 then 0#64 else r i := by
  simp [mkS, State.readReg64, RegFile.read]
@[simp] theorem mkS_readSp : (mkS s0 pc r sp ps m v).readReg64 .sp = sp := rfl
@[simp] theorem mkS_readXzr : (mkS s0 pc r sp ps m v).readReg64 .xzr = 0#64 := rfl

@[simp] theorem mkS_writeGpr (i : BitVec 5) (x : BitVec 64) :
    (mkS s0 pc r sp ps m v).writeReg64 (.gpr i) x =
      mkS s0 pc (if i = 31#5 then r else upd r i x) sp ps m v := by
  by_cases h : i = 31#5
  · simp [mkS, State.writeReg64, h]
  · simp [mkS, State.writeReg64, h, RegFile.write]; rfl
@[simp] theorem mkS_writeSp (x : BitVec 64) :
    (mkS s0 pc r sp ps m v).writeReg64 .sp x = mkS s0 pc r x ps m v := rfl
@[simp] theorem mkS_writeXzr (x : BitVec 64) :
    (mkS s0 pc r sp ps m v).writeReg64 .xzr x = mkS s0 pc r sp ps m v := rfl

@[simp] theorem mkS_advancePC : (mkS s0 pc r sp ps m v).advancePC = mkS s0 (pc + 4#64) r sp ps m v := rfl
@[simp] theorem mkS_setPC (q : BitVec 64) : (mkS s0 pc r sp ps m v).setPC q = mkS s0 q r sp ps m v := rfl
@[simp] theorem mkS_setPState (q : PState) :
    (mkS s0 pc r sp ps m v).setPState q = mkS s0 pc r sp q m v := rfl
@[simp] theorem mkS_setMem (q : Memory) : (mkS s0 pc r sp ps m v).setMem q = mkS s0 pc r sp ps q v := rfl

@[simp] theorem mkS_readV (i : BitVec 5) : (mkS s0 pc r sp ps m v).readVReg128 i = v i := rfl
@[simp] theorem mkS_writeV (i : BitVec 5) (x : BitVec 128) :
    (mkS s0 pc r sp ps m v).writeVReg128 i x = mkS s0 pc r sp ps m (upd v i x) := by
  simp only [mkS, State.writeVReg128, VRegFile.write]; rfl

end

/-- Register reads of the entry state, as `mkS` sees them. -/
theorem readGpr_eq (s : State) (i : BitVec 5) (h : i ≠ 31#5) :
    s.readReg64 (.gpr i) = s.regs.regs i := by
  simp [State.readReg64, RegFile.read, h]

end X25519Dalek.EMulB
end

section
/-! # Code stays loaded; stepping on abstract states; small stack frames -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem codeLoaded_keepsFrozen {p : Program} {m m' : Memory} (h : p.CodeLoaded m)
    (hk : m.KeepsFrozen m') : p.CodeLoaded m' := by
  unfold Program.CodeLoaded at h ⊢
  refine ⟨h.1, h.2.1, fun i hi => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2.2 i hi
  have hf : m.Frozen (p.base + BitVec.ofNat 64 i) := by
    simp [Memory.Frozen, h2, Perm.rx, Perm.frozen, Perm.rwx]
  obtain ⟨k1, k2, k3, _⟩ := hk _ hf
  exact ⟨k1.trans h1, k2.trans h2, k3.trans h3⟩

theorem libCodeLoaded_keepsFrozen {mpl : MultiPlacement} {m m' : Memory}
    (h : x25519CliMultiLib.CodeLoaded mpl m) (hk : m.KeepsFrozen m') :
    x25519CliMultiLib.CodeLoaded mpl m' :=
  fun i hi => codeLoaded_keepsFrozen (h i hi) hk

/-- Fetch at offset `off` of block `i` from any memory that kept the frozen bytes of `m0`. -/
theorem fetch_at {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {i : Nat} (hi : i < 19) (j : Nat) {off : Nat}
    {inst : Instr}
    (h : (off % 4 = 0 ∧ off + 4 ≤ (blk i).code.length) ∧ (blk i).relocAt? off = none ∧
      decode ((blk i).wordAt off) = some inst)
    {m : Memory} (hk : m0.KeepsFrozen m) :
    (bprog mpl j).fetchMem m (mpl.base i + BitVec.ofNat 64 off) = some inst := by
  have hCL' := libCodeLoaded_keepsFrozen hCL hk i (by rw [blocks_length]; exact hi)
  rw [fetch_word hP hi hCL' h.1.1 h.1.2 _ (hook_none mpl j), patchedWord_plain _ _ h.2.1]
  exact h.2.2

theorem fetch_at' {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {i : Nat} (hi : i < 19) (j : Nat) {b : CodeBlock}
    (hb : blk i = b) {L : Nat} (hL : b.code.length = L) {off : Nat} {inst : Instr}
    (h4 : off % 4 = 0 ∧ off + 4 ≤ L)
    (hr : b.relocAt? off = none) (hd : decode (b.wordAt off) = some inst)
    {m : Memory} (hk : m0.KeepsFrozen m) :
    (bprog mpl j).fetchMem m (mpl.base i + BitVec.ofNat 64 off) = some inst :=
  fetch_at hP hCL hi j (by subst hb hL; exact ⟨h4, hr, hd⟩) hk

theorem Reach.mk {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {i : Instr} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some i)
    (h : Reach p (execInstWithSvc (evalSvc p.svc) i (mkS s0 pc r sp ps m v)) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q :=
  Reach.exec hrun hf h

theorem pc_add (b : BitVec 64) (k j : Nat) :
    b + BitVec.ofNat 64 k + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (k + j) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-! ## Byte lists of length 8 are words -/

def pack64 (l : List (BitVec 8)) : BitVec 64 :=
  l.getD 7 0 ++ l.getD 6 0 ++ l.getD 5 0 ++ l.getD 4 0 ++ l.getD 3 0 ++ l.getD 2 0 ++
    l.getD 1 0 ++ l.getD 0 0

theorem unpack64_cat8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    unpack64 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  simp only [unpack64, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp (disch := omega) only [hi, decide_eq_true, if_pos, if_neg, Nat.sub_sub, Nat.reduceAdd,
      Bool.true_and, Nat.add_sub_cancel_left, Nat.zero_add, decide_true, ite_true]
    try (congr 1; omega)

theorem unpack64_pack64 (l : List (BitVec 8)) (h : l.length = 8) : unpack64 (pack64 l) = l := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    simp only [pack64, List.getD_cons_zero, List.getD_cons_succ]
    exact unpack64_cat8 b0 b1 b2 b3 b4 b5 b6 b7

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

/-- Focus-free consequences of owning one 64-bit cell at the head. -/
theorem cell_write {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F)
    (w : BitVec 64) :
    m.canWrite a 8 = true ∧ m.KeepsFrozen (m.write64 a w) ∧ (m.write64 a w ⊨ (a ↦₆₄ w) ∗ F) := by
  have h := sat64_read hs
  exact ⟨h.2.2, keepsFrozen_write64_of_rw (fun i hi => (sat64_byte hs i hi).2.1) w, sat64_write hs w⟩

end X25519Dalek.EMulB
end

section
/-! # Arithmetic facts for the instruction evaluators and byte encodings -/

set_option autoImplicit false

namespace X25519Dalek.EMulB

open Arm64

@[simp] theorem awc_false_fst (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]
  omega

@[simp] theorem awc_true_fst (x y : BitVec 64) : (AddWithCarry64 x y true).1 = x + y + 1#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]
  omega

@[simp] theorem add_not_add_one (x y : BitVec 64) : x + ~~~y + 1#64 = x - y := by
  bv_omega

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem and15_toNat (x : BitVec 64) : (x &&& 15#64).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and]
  have : (15#64 : BitVec 64).toNat = 2 ^ 4 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- Alignment of `sp - k` for `k` a multiple of 16, from alignment of `sp`. -/
theorem aligned_sub {x : BitVec 64} (h : (x &&& 15#64 == 0#64) = true) (k : Nat) (hk : k % 16 = 0)
    (hk' : k < 2 ^ 64) : (x - BitVec.ofNat 64 k &&& 15#64) = 0#64 := by
  have h0 : x &&& 15#64 = 0#64 := by simpa using h
  have h1 := congrArg BitVec.toNat h0
  rw [and15_toNat] at h1
  apply BitVec.eq_of_toNat_eq
  rw [and15_toNat]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_zero] at h1 ⊢
  rw [Nat.mod_eq_of_lt hk'] 
  omega

theorem aligned_add {x : BitVec 64} (h : (x &&& 15#64 == 0#64) = true) (k : Nat) (hk : k % 16 = 0) :
    (x + BitVec.ofNat 64 k &&& 15#64) = 0#64 := by
  have h0 : x &&& 15#64 = 0#64 := by simpa using h
  have h1 := congrArg BitVec.toNat h0
  rw [and15_toNat] at h1
  apply BitVec.eq_of_toNat_eq
  rw [and15_toNat]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_zero] at h1 ⊢
  omega

end X25519Dalek.EMulB
end

section
/-! # Relocated `BL` words and calls to other blocks -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem beq_false_of_mask {w K A M C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A &&& M) :
    (w &&& M == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, ← hK, BitVec.and_assoc, BitVec.and_comm M K, ← BitVec.and_assoc]

theorem beq_false_of_mask' {w K A C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A) :
    (w == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, hK]

theorem decode_bl_class (w : BitVec 32) (hK : w &&& 0xfc000000#32 = 0x94000000#32) :
    decode w = some (.bl ((w.extractLsb' 0 26).signExtend 64 <<< 2)) := by
  have h7c : (w &&& 0x7c000000#32 == 0x14000000#32) = true := by
    have : w &&& 0x7c000000#32 = (w &&& 0xfc000000#32) &&& 0x7c000000#32 := by
      rw [BitVec.and_assoc]; rfl
    rw [this, hK]; rfl
  have h31 : w.getLsbD 31 = true := by
    have := congrArg (fun x => x.getLsbD 31) hK
    simp only [BitVec.getLsbD_and] at this
    simpa using this
  rw [decode]
  simp only [beq_false_of_mask' hK (C := 0xd503201f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4000001#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4200000#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd503201f#32) (M := 0xfffff01f#32) (by decide),
    beq_false_of_mask hK (C := 0#32) (M := 0xffff0000#32) (by decide),
    beq_false_of_mask hK (C := 0xd50b7420#32) (M := 0xffffffe0#32) (by decide),
    beq_false_of_mask hK (C := 0x10000000#32) (M := 0x1f000000#32) (by decide),
    beq_false_of_mask hK (C := 0x11000000#32) (M := 0x1f800000#32) (by decide),
    beq_false_of_mask hK (C := 0x12000000#32) (M := 0x1f800000#32) (by decide),
    beq_false_of_mask hK (C := 0x12800000#32) (M := 0x1f800000#32) (by decide),
    beq_false_of_mask hK (C := 0x13000000#32) (M := 0x1f800000#32) (by decide),
    beq_false_of_mask hK (C := 0x13800000#32) (M := 0x7f800000#32) (by decide), h7c, h31]
  simp

theorem hi_bits27 (D : BitVec 64) (h1 : -(2^27:Int) ≤ D.toInt) (h2 : D.toInt < 2^27) :
    ∀ i, 27 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 27 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  by_cases hs : 2 * D.toNat < 2 ^ 64
  · rw [if_pos hs] at h2
    have hD : D.toNat < 2 ^ 27 := by omega
    have g : ∀ j, 27 ≤ j → D.getLsbD j = false := fun j hj =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hD (Nat.pow_le_pow_right (by norm_num) hj))
    rw [g i hi1, g 27 le_rfl]
  · rw [if_neg hs] at h1
    have hE : (~~~D).toNat < 2 ^ 27 := by rw [BitVec.toNat_not]; omega
    have g : ∀ j, 27 ≤ j → j < 64 → D.getLsbD j = true := by
      intro j hj1 hj2
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hE (Nat.pow_le_pow_right (by norm_num) hj1))
      have e : (~~~D).getLsbD j = false := this
      rw [BitVec.getLsbD_not] at e
      simpa [hj2] using e
    rw [g i hi1 hi2, g 27 le_rfl (by norm_num)]

theorem lo_bits2 (D : BitVec 64) (h : D.toNat % 4 = 0) : ∀ i, i < 2 → D.getLsbD i = false := by
  intro i hi
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize D.toNat = n at h ⊢
  interval_cases i <;> simp <;> omega

theorem bw_mask (D : BitVec 64) :
    ((0x94000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32)) &&&
      0xfc000000#32 = 0x94000000#32 := by
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc ((D >>> 2).setWidth 32)]
  simp

theorem cbits (j : Nat) (hj : j < 26) : (0x94000000#32 : BitVec 32).getLsbD j = false ∧
    (0x03ffffff#32 : BitVec 32).getLsbD j = true := by
  interval_cases j <;> decide

theorem bw_off (D : BitVec 64) (hlo : ∀ i, i < 2 → D.getLsbD i = false)
    (hhi : ∀ i, 27 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 27) :
    ((((0x94000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32))).extractLsb' 0 26).signExtend 64 <<< 2 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.msb_eq_getLsbD_last]
  rcases (show i < 2 ∨ (2 ≤ i ∧ i < 28) ∨ 28 ≤ i by omega) with h | ⟨h1, h2⟩ | h
  · simp [h, hlo i h]
  · have c := cbits (i - 2) (by omega)
    simp [hi, show ¬ i < 2 by omega, show i - 2 < 26 by omega, show i - 2 < 32 by omega]
    simp only [← BitVec.getLsbD_eq_getElem, c.1, c.2, Bool.false_and, Bool.false_or, Bool.and_true]
    simp [show i - 2 < 64 by omega]; congr 1; omega
  · have c := cbits 25 (by omega)
    simp [hi, show ¬ i < 2 by omega, show ¬ i - 2 < 26 by omega, c.1, c.2]
    simp only [← BitVec.getLsbD_eq_getElem]
    rw [hhi i (by omega) hi]
    simp [show i - 2 < 64 by omega]

/-- A relocated `bl` decodes to a branch-with-link whose offset reaches the target, when the
target is in range. -/
theorem decode_branchWord (place target : BitVec 64) (h : BranchInRange place target) :
    decode (branchWord 0x94000000#32 place target) = some (.bl (target - place)) := by
  unfold branchWord
  rw [decode_bl_class _ (bw_mask _)]
  congr 2
  exact bw_off _ (lo_bits2 _ h.1) (hi_bits27 _ h.2.1 h.2.2)

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

/-- The patched word of a `bl` to another block's function: a branch word to that function. -/
theorem patchedWord_call (i : Nat) (mpl : MultiPlacement) {off j offj : Nat} {name : String}
    (h : (blk i).relocAt? off = some { off := off, kind := .call26, sym := name } ∧
      (blk i).relaxableAt off = false ∧ (off < 4 ∨ (blk i).relaxableAt (off - 4) = false) ∧
      lookup name (blk i).symbols = none ∧ (blk i).weakRefs = [] ∧
      (blk i).wordAt off = 0x94000000#32)
    (hlk : lookupBlockSym name x25519CliMultiLib.blocks = some (j, offj)) :
    (blk i).patchedWord (x25519CliMultiLib.blockPlacement mpl i) off =
      branchWord 0x94000000#32 (mpl.base i + BitVec.ofNat 64 off) (mpl.base j + BitVec.ofNat 64 offj) := by
  obtain ⟨hr, hra, hra4, hsym, hweak, hw⟩ := h
  have h4 : (4 ≤ off && (blk i).relaxedAt (x25519CliMultiLib.blockPlacement mpl i) (off - 4)) = false := by
    rcases hra4 with h | h
    · simp; omega
    · simp [CodeBlock.relaxedAt, h]
  simp only [CodeBlock.patchedWord, hr, CodeBlock.relaxedAt, hra, Bool.false_and, Bool.false_eq_true,
    if_false]
  simp only [CodeBlock.relaxedAt] at h4
  rw [if_neg (by simp [h4])]
  simp only [RelocKind.isGotOrTlsIe, Bool.false_and, Bool.false_eq_true, if_false,
    CodeBlock.undefWeakBranch, hweak, List.contains_nil, CodeBlock.relocTarget, CodeBlock.b2bNext?,
    hsym, CodeBlock.target, CodeBlock.resolve, addSignedAddr, patchRelocWord, hw,
    MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hlk]
  split
  · rename_i heq; split at heq <;> simp at heq
  · simp

/-- Fetching the relocated `bl` at offset `off` of block `i`, calling the function at offset
`offj` of block `j`. -/
theorem fetch_bl {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {i : Nat} (hi : i < 19) (k : Nat) {off j offj : Nat}
    {name : String}
    (hoff : off % 4 = 0 ∧ off + 4 ≤ (blk i).code.length)
    (h : (blk i).relocAt? off = some { off := off, kind := .call26, sym := name } ∧
      (blk i).relaxableAt off = false ∧ (off < 4 ∨ (blk i).relaxableAt (off - 4) = false) ∧
      lookup name (blk i).symbols = none ∧ (blk i).weakRefs = [] ∧
      (blk i).wordAt off = 0x94000000#32)
    (hlk : lookupBlockSym name x25519CliMultiLib.blocks = some (j, offj))
    {m : Memory} (hk : m0.KeepsFrozen m) :
    (bprog mpl k).fetchMem m (mpl.base i + BitVec.ofNat 64 off) =
      some (.bl ((mpl.base j + BitVec.ofNat 64 offj) - (mpl.base i + BitVec.ofNat 64 off))) := by
  have hCL' := libCodeLoaded_keepsFrozen hCL hk i (by rw [blocks_length]; exact hi)
  rw [fetch_word hP hi hCL' hoff.1 hoff.2 _ (hook_none mpl k), patchedWord_call i mpl h hlk]
  apply decode_branchWord
  have hPl := blk_placeable hP hi
  have hmem : ({ off := off, kind := .call26, sym := name } : RelocEntry) ∈ (blk i).relocs := by
    have := h.1
    simp only [CodeBlock.relocAt?] at this
    exact List.mem_of_find?_eq_some this
  have := (hPl.relocs_ok _ hmem).2.2
  simp only [CodeBlock.relocInRange, CodeRelocInRange] at this
  have ht : (blk i).relocTarget (x25519CliMultiLib.blockPlacement mpl i) off
      { off := off, kind := .call26, sym := name } = mpl.base j + BitVec.ofNat 64 offj := by
    obtain ⟨_, _, _, hsym, _, _⟩ := h
    simp only [CodeBlock.relocTarget, CodeBlock.b2bNext?, hsym, CodeBlock.target, CodeBlock.resolve,
      addSignedAddr, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hlk]
    split
    · rename_i heq; split at heq <;> simp at heq
    · simp
  rw [ht] at this
  exact this

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

/-- Running a call to another function of the library, from its contract `fnOk`: the caller
continues from any state the callee may return in. -/
theorem Reach.call {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat)
    {S α : Type} [ToBaseSpec S α] {name : String} {spec : MultiPlacement → S} {j offj : Nat}
    (hok : fnOk name spec) (hlk : lookupBlockSym name x25519CliMultiLib.blocks = some (j, offj))
    (hj : j < 19) {s : State} {Q : State → Prop} (x : α) (R' : SepProp)
    (hpc : s.pc = mpl.base j + BitVec.ofNat 64 offj) (hrun : s.status = .Running)
    (hal : s.spAligned = true) (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem)
    (hpre : s.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).pre x s ∗ R')
    (hpanic : ∀ sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onPanic x s sf ∗ R'))
    (hexit : ∀ c sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onExit x c s sf ∗ R'))
    (hoom : ∀ sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onOom x s sf ∗ R'))
    (hcont : ∀ sf, sf.pc = s.readReg64 Reg.lr → sf.sp = s.sp → sf.status = .Running →
      CalleeSavedPreserved s sf →
      (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).post x s sf ∗ R') →
      s.mem.KeepsFrozen sf.mem → Reach (bprog mpl k) sf Q) :
    Reach (bprog mpl k) s Q := by
  obtain ⟨j', off', hlk', hall⟩ := hok
  rw [hlk] at hlk'
  cases hlk'
  have hfa : x25519CliMultiLib.fnAddr mpl name = mpl.base j + BitVec.ofNat 64 offj := by
    simp [MultiPlacedLib.fnAddr, hlk]
  have hpre' : s.mem ⊨ (x25519CliMultiLib.withCodeLoaded mpl
      (ToBaseSpec.toSpec (spec mpl) (mpl.base j))).pre x s ∗ R' := by
    simp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, sat_pure_sep]
    exact ⟨hCL, hpre⟩
  obtain ⟨sf, hst, hout⟩ := hall mpl hP x R' s (by rw [hpc, hfa]) hrun hpre' hal
    (hCL j (by rw [blocks_length]; exact hj))
  have hkf := X25519Dalek.steps_keepsFrozen_v2 hst
  have hst' : Steps (bprog mpl k) s sf := bsteps_transfer (i := j) hst
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨_, hp⟩ | ⟨c, _, hp⟩ | ⟨_, hp⟩
  · exact Reach.steps hst' (hcont sf hpcf hspf hrunf hcs hpost hkf)
  · exact absurd hp (hpanic sf)
  · exact absurd hp (hexit c sf)
  · exact absurd hp (hoom sf)

theorem not_sat_false {m : Memory} {R : SepProp} : ¬ (m ⊨ (⌜False⌝ : SepProp) ∗ R) := by
  rw [sat_pure_sep]; exact fun h => h.1

end X25519Dalek.EMulB
end

section
/-! # Stack frames as lists of 64-bit words

`a ↦₆₄* ws` owns the words `ws` at `a, a + 8, …`; indexed reads and writes; conversions to and
from byte slices and `memRegion`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64

theorem words_cons (a w : BitVec 64) (ws : List (BitVec 64)) :
    (a ↦₆₄* (w :: ws)) = (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄* ws) := rfl

theorem words_nil (a : BitVec 64) : (a ↦₆₄* ([] : List (BitVec 64))) = emp := rfl

theorem words_eq_bytes : ∀ (a : BitVec 64) (ws : List (BitVec 64)),
    (a ↦₆₄* ws) = (a ↦ₛ ws.flatMap unpack64)
  | a, [] => by rw [words_nil]; rfl
  | a, w :: ws => by
    rw [words_cons, words_eq_bytes (a + 8#64) ws, List.flatMap_cons, pointsToBytes_append,
      pointsTo64_eq_bytes]
    rfl

theorem flatMap_unpack64_length (ws : List (BitVec 64)) :
    (ws.flatMap unpack64).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [List.flatMap_cons, ih]; omega

theorem addr8 (a : BitVec 64) (i : Nat) :
    a + 8#64 + BitVec.ofNat 64 (8 * i) = a + BitVec.ofNat 64 (8 * (i + 1)) := by
  rw [BitVec.add_assoc]; congr 1; bv_omega

theorem sat_words_read : ∀ {m : Memory} {a : BitVec 64} {ws : List (BitVec 64)} {F : SepProp},
    (m ⊨ (a ↦₆₄* ws) ∗ F) → ∀ (i : Nat) (hi : i < ws.length),
      m.read64 (a + BitVec.ofNat 64 (8 * i)) = ws[i] ∧
      m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true ∧
      m.canWrite (a + BitVec.ofNat 64 (8 * i)) 8 = true
  | _, _, [], _, _, i, hi => by simp at hi
  | m, a, w :: ws, F, hs, 0, _ => by
    rw [words_cons, sepConj_assoc] at hs
    simpa using sat64_read hs
  | m, a, w :: ws, F, hs, i + 1, hi => by
    rw [words_cons, sepConj_assoc, sepConj_left_comm] at hs
    have := sat_words_read hs i (by simp at hi; omega)
    rw [addr8] at this
    simpa using this

theorem sat_words_write : ∀ {m : Memory} {a : BitVec 64} {ws : List (BitVec 64)} {F : SepProp},
    (m ⊨ (a ↦₆₄* ws) ∗ F) → ∀ (i : Nat) (hi : i < ws.length) (w : BitVec 64),
      (m.write64 (a + BitVec.ofNat 64 (8 * i)) w ⊨ (a ↦₆₄* ws.set i w) ∗ F) ∧
      m.KeepsFrozen (m.write64 (a + BitVec.ofNat 64 (8 * i)) w)
  | _, _, [], _, _, i, hi, _ => by simp at hi
  | m, a, v :: ws, F, hs, 0, _, w => by
    rw [words_cons, sepConj_assoc] at hs
    have h := cell_write hs w
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.set_cons_zero]
    rw [words_cons, sepConj_assoc]
    exact ⟨h.2.2, h.2.1⟩
  | m, a, v :: ws, F, hs, i + 1, hi, w => by
    rw [words_cons, sepConj_assoc, sepConj_left_comm] at hs
    have := sat_words_write hs i (by simp at hi; omega) w
    rw [addr8] at this
    rw [List.set_cons_succ, words_cons, sepConj_assoc, sepConj_left_comm]
    exact this

/-- The 64-bit little-endian words of a byte list, eight bytes at a time. -/
def chunks64 : List (BitVec 8) → Nat → List (BitVec 64)
  | _, 0 => []
  | bs, k + 1 => pack64 (bs.take 8) :: chunks64 (bs.drop 8) k

theorem chunks64_length (bs : List (BitVec 8)) (k : Nat) : (chunks64 bs k).length = k := by
  induction k generalizing bs with
  | zero => rfl
  | succ k ih => simp [chunks64, ih]

theorem chunks64_flat : ∀ (k : Nat) (bs : List (BitVec 8)), bs.length = 8 * k →
    (chunks64 bs k).flatMap unpack64 = bs
  | 0, bs, h => by simp at h; simp [chunks64, h]
  | k + 1, bs, h => by
    simp only [chunks64, List.flatMap_cons]
    rw [unpack64_pack64 _ (by simp; omega), chunks64_flat k (bs.drop 8) (by simp; omega),
      List.take_append_drop]

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

@[simp] theorem extract_lo128 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi']

@[simp] theorem extract_hi128 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have : ¬ (64 + i < 64) := by omega
  simp [hi', this]

theorem memRegion_append (a : BitVec 64) (n : Nat) (bs : List (BitVec 8)) (hn : n < 2 ^ 64) :
    (memRegion a n ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bs)) ⊢ memRegion a (n + bs.length) := by
  intro h hh
  obtain ⟨h1, h2, hd, rfl, hm, hb⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨b0, hb0⟩ := memRegion_entails_bytes a n hn h1 hm
  obtain ⟨hl, hb0⟩ := pure_sepConj_holds.mp hb0
  have : (a ↦ₛ (b0 ++ bs)).holds (h1.union h2) := by
    rw [pointsToBytes_append, hl]
    exact SepProp.holds_sepConj_iff.mpr ⟨h1, h2, hd, rfl, hb0, hb⟩
  have := bytes_entails_memRegion a _ _ this
  simpa [hl] using this

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem zext12_lit (n : Nat) : BitVec.zeroExtend 64 (BitVec.ofNat 12 n) = BitVec.ofNat 64 (n % 4096) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

theorem zext16_lit (n : Nat) : BitVec.zeroExtend 64 (BitVec.ofNat 16 n) = BitVec.ofNat 64 (n % 65536) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

@[simp] theorem bf_beq_1 : (BitfieldOp.BFM == BitfieldOp.UBFM) = false := by decide
@[simp] theorem bf_beq_2 : (BitfieldOp.BFM == BitfieldOp.SBFM) = false := by decide
@[simp] theorem bf_beq_3 : (BitfieldOp.UBFM == BitfieldOp.SBFM) = false := by decide
@[simp] theorem bf_beq_4 : (BitfieldOp.SBFM == BitfieldOp.UBFM) = false := by decide
@[simp] theorem bf_beq_5 : (BitfieldOp.UBFM == BitfieldOp.UBFM) = true := by decide
@[simp] theorem bf_beq_6 : (BitfieldOp.SBFM == BitfieldOp.SBFM) = true := by decide

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

/-- After a 64-bit store into an owned word list, continue from an abstract memory. -/
theorem Reach.wr64 {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {vr : BitVec 5 → BitVec 128} {Q : State → Prop}
    {base a : BitVec 64} {ws : List (BitVec 64)} {F : SepProp} {v : BitVec 64} (i : Nat)
    (hs : m ⊨ (base ↦₆₄* ws) ∗ F) (ha : a = base + BitVec.ofNat 64 (8 * i)) (hi : i < ws.length)
    (h : ∀ m', (m' ⊨ (base ↦₆₄* ws.set i v) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc r sp ps m' vr) Q) :
    Reach p (mkS s0 pc r sp ps (m.write64 a v) vr) Q := by
  subst ha
  obtain ⟨h1, h2⟩ := sat_words_write hs i hi v
  exact h _ h1 h2

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem add_sub_cancel' (a b : BitVec 64) : a + (b - a) = b := by bv_omega
theorem sub_add_cancel' (a : BitVec 64) (k : Nat) : a - BitVec.ofNat 64 k + BitVec.ofNat 64 k = a := by
  bv_omega

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem memRegion_split (a : BitVec 64) (n k : Nat) (h : n + k < 2 ^ 64) :
    memRegion a (n + k) ⊢ memRegion a n ∗ memRegion (a + BitVec.ofNat 64 n) k := by
  intro hp hh
  obtain ⟨bs, hb⟩ := memRegion_entails_bytes a (n + k) h hp hh
  obtain ⟨hl, hb⟩ := pure_sepConj_holds.mp hb
  rw [pointsToBytes_split a bs n (by omega)] at hb
  obtain ⟨h1, h2, hd, rfl, hb1, hb2⟩ := SepProp.holds_sepConj_iff.mp hb
  refine SepProp.holds_sepConj_iff.mpr ⟨h1, h2, hd, rfl, ?_, ?_⟩
  · have := bytes_entails_memRegion a (bs.take n) h1 hb1; simpa [hl, show n ≤ n + k by omega] using this
  · have := bytes_entails_memRegion _ (bs.drop n) h2 hb2; simpa [hl] using this

theorem memRegion_bytes (a : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) {m : Memory} {F : SepProp}
    (hs : m ⊨ memRegion a n ∗ F) : ∃ bs, bs.length = n ∧ (m ⊨ (a ↦ₛ bs) ∗ F) := by
  have h := sat_sep_mono hs (memRegion_entails_bytes a n hn)
  rw [sepExists_sepConj, sat_sepExists] at h
  obtain ⟨bs, h⟩ := h
  rw [sepConj_assoc, sat_pure_sep] at h
  exact ⟨bs, h.1, h.2⟩

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem sat_mr_split {m : Memory} {a : BitVec 64} {F : SepProp} (n k : Nat) (h : n + k < 2 ^ 64)
    (b : BitVec 64) (hb : a + BitVec.ofNat 64 n = b) (hs : m ⊨ memRegion a (n + k) ∗ F) :
    m ⊨ memRegion a n ∗ memRegion b k ∗ F := by
  have := sat_sep_mono hs (memRegion_split a n k h)
  rw [sepConj_assoc, hb] at this; exact this

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem Reach.wr64x2 {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {vr : BitVec 5 → BitVec 128} {Q : State → Prop}
    {base a b : BitVec 64} {ws : List (BitVec 64)} {F : SepProp} {v w : BitVec 64} (i : Nat)
    (hs : m ⊨ (base ↦₆₄* ws) ∗ F) (ha : a = base + BitVec.ofNat 64 (8 * i))
    (hb : b = base + BitVec.ofNat 64 (8 * (i + 1))) (hi : i + 1 < ws.length)
    (h : ∀ m', (m' ⊨ (base ↦₆₄* (ws.set i v).set (i + 1) w) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc r sp ps m' vr) Q) :
    Reach p (mkS s0 pc r sp ps ((m.write64 a v).write64 b w) vr) Q := by
  subst ha
  obtain ⟨h1, k1⟩ := sat_words_write hs i (by omega) v
  exact Reach.wr64 (i + 1) h1 hb (by simp; omega) (fun m' h' k' => h m' h' (k1.trans k'))

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64 Arm64.Obj

/-- Callee-saved general registers of `sf` agree with the register function `rf`. -/
def CSRegs (sf : State) (rf : BitVec 5 → BitVec 64) : Prop :=
  sf.regs.regs 19#5 = rf 19#5 ∧ sf.regs.regs 20#5 = rf 20#5 ∧ sf.regs.regs 21#5 = rf 21#5 ∧
  sf.regs.regs 22#5 = rf 22#5 ∧ sf.regs.regs 23#5 = rf 23#5 ∧ sf.regs.regs 24#5 = rf 24#5 ∧
  sf.regs.regs 25#5 = rf 25#5 ∧ sf.regs.regs 26#5 = rf 26#5 ∧ sf.regs.regs 27#5 = rf 27#5 ∧
  sf.regs.regs 28#5 = rf 28#5 ∧ sf.regs.regs 29#5 = rf 29#5

/-- A call from an abstract state: the caller continues from the callee's return state. -/
theorem Reach.callS {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat)
    {S α : Type} [ToBaseSpec S α] {name : String} {spec : MultiPlacement → S} {j offj : Nat}
    (hok : fnOk name spec) (hlk : lookupBlockSym name x25519CliMultiLib.blocks = some (j, offj))
    (hj : j < 19) {s0 : State} {pc : BitVec 64} {rf : BitVec 5 → BitVec 64} {sp : BitVec 64}
    {ps : PState} {m : Memory} {vf : BitVec 5 → BitVec 128} {Q : State → Prop} (x : α) (R' : SepProp)
    (hpc : pc = mpl.base j + BitVec.ofNat 64 offj) (hrun : s0.status = .Running)
    (hal : (sp &&& 15#64) = 0#64) (hCL : x25519CliMultiLib.CodeLoaded mpl m)
    (hpre : m ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).pre x (mkS s0 pc rf sp ps m vf) ∗ R')
    (hpanic : ∀ sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onPanic x
      (mkS s0 pc rf sp ps m vf) sf ∗ R'))
    (hexit : ∀ c sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onExit x c
      (mkS s0 pc rf sp ps m vf) sf ∗ R'))
    (hoom : ∀ sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onOom x
      (mkS s0 pc rf sp ps m vf) sf ∗ R'))
    (hcont : ∀ sf, sf.status = .Running → sf.sp = sp → CSRegs sf rf →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨vf⟩ →
      (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).post x (mkS s0 pc rf sp ps m vf) sf ∗ R') →
      m.KeepsFrozen sf.mem →
      Reach (bprog mpl k) (mkS sf (rf 30#5) sf.regs.regs sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl k) (mkS s0 pc rf sp ps m vf) Q := by
  refine Reach.call hP k hok hlk hj x R' hpc hrun (by simp [hal]) hCL hpre hpanic hexit hoom ?_
  intro sf hpcf hspf hrunf hcs hpost hkf
  have hpc' : sf.pc = rf 30#5 := by rw [hpcf]; simp [Reg.lr]
  have hsp' : sf.sp = sp := by rw [hspf]; rfl
  have e : sf = mkS sf (rf 30#5) sf.regs.regs sp sf.pstate sf.mem sf.vregs.regs := by
    rw [← hpc', ← hsp']; rfl
  rw [e]
  obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, cfp, cv⟩ := hcs
  simp only [mkS_readGpr, Reg.fp, BitVec.reduceEq, ite_false] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 cfp
  rw [readGpr_eq sf _ (by decide)] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 cfp
  exact hcont sf hrunf hsp' ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, cfp⟩ cv hpost hkf

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem sat_pre3 {m : Memory} {φ : Prop} {A B C F : SepProp} (hφ : φ) (hs : m ⊨ A ∗ B ∗ C ∗ F) :
    m ⊨ (⌜φ⌝ ∗ A ∗ B ∗ C) ∗ F := by
  rw [sepConj_assoc, sat_pure_sep]; exact ⟨hφ, by simpa only [sepConj_assoc] using hs⟩

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem Reach.wr64x4 {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {vr : BitVec 5 → BitVec 128} {Q : State → Prop}
    {base a0 a1 a2 a3 : BitVec 64} {ws : List (BitVec 64)} {F : SepProp} {v0 v1 v2 v3 : BitVec 64}
    (i : Nat) (hs : m ⊨ (base ↦₆₄* ws) ∗ F) (h0 : a0 = base + BitVec.ofNat 64 (8 * i))
    (h1 : a1 = base + BitVec.ofNat 64 (8 * (i + 1))) (h2 : a2 = base + BitVec.ofNat 64 (8 * (i + 2)))
    (h3 : a3 = base + BitVec.ofNat 64 (8 * (i + 3))) (hi : i + 3 < ws.length)
    (h : ∀ m', (m' ⊨ (base ↦₆₄* (((ws.set i v0).set (i + 1) v1).set (i + 2) v2).set (i + 3) v3) ∗ F) →
      m.KeepsFrozen m' → Reach p (mkS s0 pc r sp ps m' vr) Q) :
    Reach p (mkS s0 pc r sp ps ((((m.write64 a0 v0).write64 a1 v1).write64 a2 v2).write64 a3 v3) vr) Q := by
  subst h0 h1
  obtain ⟨g1, k1⟩ := sat_words_write hs i (by omega) v0
  obtain ⟨g2, k2⟩ := sat_words_write g1 (i + 1) (by simp; omega) v1
  exact Reach.wr64x2 (i + 2) g2 h2 h3 (by simp; omega) (fun m' h' k' => h m' h' (k1.trans (k2.trans k')))

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem sat_mr_merge {m : Memory} {a b : BitVec 64} {F : SepProp} (n k : Nat) (h : n + k < 2 ^ 64)
    (hb : b = a + BitVec.ofNat 64 n) (hs : m ⊨ memRegion a n ∗ memRegion b k ∗ F) :
    m ⊨ memRegion a (n + k) ∗ F := by
  subst hb
  rw [← sepConj_assoc] at hs
  refine sat_sep_mono hs ?_
  intro hp hh
  obtain ⟨h1, h2, hd, rfl, hm1, hm2⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨bs, hb⟩ := memRegion_entails_bytes _ k (by omega) h2 hm2
  obtain ⟨hl, hb⟩ := pure_sepConj_holds.mp hb
  have := memRegion_append a n bs (by omega) _ (SepProp.holds_sepConj_iff.mpr ⟨h1, h2, hd, rfl, hm1, hb⟩)
  rwa [hl] at this

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem sat_mr_bytes {m : Memory} {a b : BitVec 64} {bs : List (BitVec 8)} {F : SepProp} (n : Nat)
    (hn : n < 2 ^ 64) (hb : b = a + BitVec.ofNat 64 n) (hs : m ⊨ memRegion a n ∗ (b ↦ₛ bs) ∗ F) :
    m ⊨ memRegion a (n + bs.length) ∗ F := by
  subst hb
  rw [← sepConj_assoc] at hs
  exact sat_sep_mono hs (memRegion_append a n bs hn)

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

end X25519Dalek.EMulB
end

section
/-! # Block 13: one `Reach` lemma per instruction shape (generated by tools/gen_shp.py)

Each lemma runs one instruction of a given shape from an abstract state `mkS s0 pc r sp ps m v`
(the pattern of the sibling ladder proof's `Shapes.lean`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64

section
variable {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem y_addi_sp {d : BitVec 5} {k : BitVec 12} {pc' : BitVec 64} (hd : d ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD (.gpr d) .sp k false))
    (h : Reach p (mkS s0 pc' (upd r d (sp + k.setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd]
  exact h

theorem y_addsp {k : BitVec 12} {pc' : BitVec 64}  (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD .sp .sp k false))
    (h : Reach p (mkS s0 pc' r (sp + k.setWidth 64) ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', BitVec.truncate_eq_setWidth]
  exact h

theorem y_movzr {d : BitVec 5} {pc' : BitVec 64} (hd : d ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .ORR (.gpr d) .xzr .xzr .LSL 0))
    (h : Reach p (mkS s0 pc' (upd r d 0#64) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd]
  exact h

theorem y_movz32 {d : BitVec 5} {k : BitVec 16} {pc' : BitVec 64} (hd : d ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.moveWide .W32 .MOVZ (.gpr d) k 0))
    (h : Reach p (mkS s0 pc' (upd r d (((k.setWidth 64).setWidth 32).setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd]
  exact h

theorem y_cmpi {n : BitVec 5} {k : BitVec 12} {pc' : BitVec 64} (hn : n ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUBS .xzr (.gpr n) k false))
    (h : Reach p (mkS s0 pc' r sp (AddWithCarry64 (r n) (~~~(k.setWidth 64)) true).2 m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hn]
  exact h

theorem y_bcond_t {c : CondCode} {off : BitVec 64} {pc' : BitVec 64} (hc : ConditionHolds c ps = true) (hpc : pc + off = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.bCond c off))
    (h : Reach p (mkS s0 pc' r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, mkS_pstate, mkS_pc, mkS_setPC, mkS_advancePC, hc, ite_true, Bool.false_eq_true, ite_false]
  exact h

theorem y_bl {off : BitVec 64} {pc' : BitVec 64} {lr : BitVec 64}  (hpc : pc + off = pc') (hlr : pc + 4#64 = lr) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.bl off))
    (h : Reach p (mkS s0 pc' (upd r 30#5 lr) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; subst hlr; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', Bool.true_eq]
  exact h

theorem y_ret   (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ret (.gpr 30#5)))
    (h : Reach p (mkS s0 (r 30#5) r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', Bool.true_eq]
  exact h

theorem y_ldr_sp {d : BitVec 5} {off A w : BitVec 64} {pc' : BitVec 64} (hd : d ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (c : m.canRead A 8 = true) (e : m.read64 A = w) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W64 .X64 false (.gpr d) (.Offset .sp off)))
    (h : Reach p (mkS s0 pc' (upd r d w) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, hal, hA, c, e]
  exact h

theorem y_ldp_sp {d1 d2 : BitVec 5} {off A A8 w1 w2 : BitVec 64} {pc' : BitVec 64} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (hA8 : A + 8#64 = A8) (c1 : m.canRead A 8 = true) (c2 : m.canRead A8 8 = true) (e1 : m.read64 A = w1) (e2 : m.read64 A8 = w2) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.Offset .sp off)))
    (h : Reach p (mkS s0 pc' (upd (upd r d1 w1) d2 w2) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd1, hd2, hal, hA, hA8, c1, c2, e1, e2]
  exact h

theorem y_ldp_post {d1 d2 : BitVec 5} {off w1 w2 : BitVec 64} {pc' : BitVec 64} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (c1 : m.canRead sp 8 = true) (c2 : m.canRead (sp + 8#64) 8 = true) (e1 : m.read64 sp = w1) (e2 : m.read64 (sp + 8#64) = w2) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.PostIndex .sp off)))
    (h : Reach p (mkS s0 pc' (upd (upd r d1 w1) d2 w2) (sp + off) ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd1, hd2, hal, c1, c2, e1, e2]
  exact h

theorem y_ldpq_o {t1 t2 b : BitVec 5} {off A A16 lo1 hi1 lo2 hi2 : BitVec 64} {pc' : BitVec 64} (hb : b ≠ 31#5) (hA : r b + off = A) (hA16 : A + 16#64 = A16) (c1 : m.canRead A 16 = true) (c2 : m.canRead A16 16 = true) (e1 : m.read64 A = lo1) (e2 : m.read64 (A + 8#64) = hi1) (e3 : m.read64 A16 = lo2) (e4 : m.read64 (A16 + 8#64) = hi2) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldpSimd .Q128 t1 t2 (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 pc' r sp ps m (upd (upd v t1 (hi1 ++ lo1)) t2 (hi2 ++ lo2))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, hA16, c1, c2, e1, e2, e3, e4]
  exact h

theorem y_ldpq_sp {t1 t2 : BitVec 5} {off A A16 lo1 hi1 lo2 hi2 : BitVec 64} {pc' : BitVec 64} (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (hA16 : A + 16#64 = A16) (c1 : m.canRead A 16 = true) (c2 : m.canRead A16 16 = true) (e1 : m.read64 A = lo1) (e2 : m.read64 (A + 8#64) = hi1) (e3 : m.read64 A16 = lo2) (e4 : m.read64 (A16 + 8#64) = hi2) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldpSimd .Q128 t1 t2 (.Offset .sp off)))
    (h : Reach p (mkS s0 pc' r sp ps m (upd (upd v t1 (hi1 ++ lo1)) t2 (hi2 ++ lo2))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hal, hA, hA16, c1, c2, e1, e2, e3, e4]
  exact h

theorem y_stpq_o {t1 t2 b : BitVec 5} {off A A8 A16 A24 lo1 hi1 lo2 hi2 : BitVec 64} {pc' : BitVec 64} (hb : b ≠ 31#5) (hA : r b + off = A) (hA8 : A + 8#64 = A8) (hA16 : A + 16#64 = A16) (hA24 : A16 + 8#64 = A24) (c1 : m.canWrite A 16 = true) (c2 : m.canWrite A16 16 = true) (ev1 : v t1 = hi1 ++ lo1) (ev2 : v t2 = hi2 ++ lo2) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stpSimd .Q128 t1 t2 (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 pc' r sp ps ((((m.write64 A lo1).write64 A8 hi1).write64 A16 lo2).write64 A24 hi2) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, hA8, hA16, hA24, c1, c2, ev1, ev2]
  exact h

theorem y_stpq_sp {t1 t2 : BitVec 5} {off A A8 A16 A24 lo1 hi1 lo2 hi2 : BitVec 64} {pc' : BitVec 64} (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (hA8 : A + 8#64 = A8) (hA16 : A + 16#64 = A16) (hA24 : A16 + 8#64 = A24) (c1 : m.canWrite A 16 = true) (c2 : m.canWrite A16 16 = true) (ev1 : v t1 = hi1 ++ lo1) (ev2 : v t2 = hi2 ++ lo2) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stpSimd .Q128 t1 t2 (.Offset .sp off)))
    (h : Reach p (mkS s0 pc' r sp ps ((((m.write64 A lo1).write64 A8 hi1).write64 A16 lo2).write64 A24 hi2) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hal, hA, hA8, hA16, hA24, c1, c2, ev1, ev2]
  exact h

end

end X25519Dalek.EMulB
end

section
/-! # Block 13: generic helpers (register and vector bookkeeping, callee frames, 128-bit copies) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem cs_upd {v : BitVec 5 → BitVec 128} {i : BitVec 5} {x : BitVec 128} (hi : i.toNat < 8)
    {X : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    (h : VRegFile.calleeSaved ⟨v⟩ = X) : VRegFile.calleeSaved ⟨upd v i x⟩ = X := by
  rw [← h]
  have hne : ∀ k : BitVec 5, 8 ≤ k.toNat → (k = i) = False := fun k hk => by
    apply propext; constructor
    · intro e; subst e; omega
    · intro e; exact e.elim
  simp only [VRegFile.calleeSaved, VRegFile.read, upd_apply, hne 8#5 (by decide), hne 9#5 (by decide),
    hne 10#5 (by decide), hne 11#5 (by decide), hne 12#5 (by decide), hne 13#5 (by decide),
    hne 14#5 (by decide), hne 15#5 (by decide), if_false]

/-- Unpack `(P ∗ ∃ res, out ↦ res ∗ ⌜φ res⌝) ∗ R`-shaped postconditions. -/
theorem post_unpack {m : Memory} {P R : SepProp} {out : BitVec 64} {φ : List (BitVec 8) → Prop}
    (h : m ⊨ (P ∗ ∃∗ res : List (BitVec 8), (out ↦ₛ res) ∗ ⌜φ res⌝) ∗ R) :
    ∃ res, φ res ∧ (m ⊨ (out ↦ₛ res) ∗ P ∗ R) := by
  have h1 := Satisfies.of_eq h (Q := (∃∗ res : List (BitVec 8), (out ↦ₛ res) ∗ ⌜φ res⌝) ∗ (P ∗ R))
  rw [sepExists_sepConj, sat_sepExists] at h1
  obtain ⟨res, h1⟩ := h1
  have h2 := Satisfies.of_eq h1 (Q := ⌜φ res⌝ ∗ ((out ↦ₛ res) ∗ P ∗ R))
  rw [sat_pure_sep] at h2
  exact ⟨res, h2.1, h2.2⟩

theorem aadd (S : BitVec 64) (a b c : Nat) (h : a + b = c) :
    S + BitVec.ofNat 64 a + BitVec.ofNat 64 b = S + BitVec.ofNat 64 c := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, h]

theorem addK (S : BitVec 64) (k : BitVec 12) (n : Nat) (h : k.setWidth 64 = BitVec.ofNat 64 n) :
    S + k.setWidth 64 = S + BitVec.ofNat 64 n := by rw [h]

theorem list20 {α : Type} (l : List α) (h : l.length = 20) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19, l = [a0, a1, a2, a3, a4,
      a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, rfl⟩

theorem fe51Point4Bounded_mono {bs : List (BitVec 8)} {b1 b2 : Nat} (h : b1 ≤ b2)
    (hb : fe51Point4Bounded bs b1) : fe51Point4Bounded bs b2 := by
  obtain ⟨hl, ⟨a0, a1, a2, a3, a4⟩, ⟨b0, b1', b2', b3, b4⟩, ⟨c0, c1, c2, c3, c4⟩, ⟨d0, d1, d2, d3, d4⟩⟩ := hb
  exact ⟨hl, ⟨by omega, by omega, by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega, by omega⟩⟩

theorem pcA (b x y z : BitVec 64) (h : x + y = z) : b + x + y = b + z := by
  rw [BitVec.add_assoc, h]

/-- The callee-saved registers `x19`–`x29` other than the loop counter `x23` agree. -/
def KeepHi (r r0 : BitVec 5 → BitVec 64) : Prop :=
  ∀ k : BitVec 5, k ≠ 23#5 → 19 ≤ k.toNat → k.toNat < 30 → r k = r0 k

theorem KeepHi.refl (r : BitVec 5 → BitVec 64) : KeepHi r r := fun _ _ _ _ => rfl

theorem KeepHi.get {r r0 : BitVec 5 → BitVec 64} (h : KeepHi r r0) (k : BitVec 5)
    (hk : k ≠ 23#5 ∧ 19 ≤ k.toNat ∧ k.toNat < 30 := by decide) : r k = r0 k :=
  h k hk.1 hk.2.1 hk.2.2

/-- Abstract the register file after a write. -/
theorem Reach.absR {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}
    {d : BitVec 5} {t : BitVec 64}
    (h : ∀ r' : BitVec 5 → BitVec 64, (∀ k, k ≠ d → r' k = r k) → r' d = t →
      Reach p (mkS s0 pc r' sp ps m v) Q) :
    Reach p (mkS s0 pc (upd r d t) sp ps m v) Q :=
  h _ (fun _ hk => upd_ne r t hk) (upd_same r d t)

/-! ## 128-bit copies between word lists -/

theorem allPerm_add (m : Memory) (p : Option Perm → Bool) : ∀ (a : BitVec 64) (n k : Nat),
    m.allPerm p a (n + k) = (m.allPerm p a n && m.allPerm p (a + BitVec.ofNat 64 n) k)
  | a, 0, k => by simp [Memory.allPerm]
  | a, n + 1, k => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [Memory.allPerm, allPerm_add m p (a + 1#64) n k, Bool.and_assoc]
    congr 3
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem allNoLazyFree_add (m : Memory) : ∀ (a : BitVec 64) (n k : Nat),
    m.allNoLazyFree a (n + k) = (m.allNoLazyFree a n && m.allNoLazyFree (a + BitVec.ofNat 64 n) k)
  | a, 0, k => by simp [Memory.allNoLazyFree]
  | a, n + 1, k => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [Memory.allNoLazyFree, allNoLazyFree_add m (a + 1#64) n k, Bool.and_assoc]
    congr 3
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem canRead16 {m : Memory} {a : BitVec 64} (h1 : m.canRead a 8 = true)
    (h2 : m.canRead (a + 8#64) 8 = true) : m.canRead a 16 = true := by
  simp only [Memory.canRead, Bool.and_eq_true] at h1 h2 ⊢
  rw [show 16 = 8 + 8 from rfl, allPerm_add, allNoLazyFree_add]
  simp only [Bool.and_eq_true]
  exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩

theorem canWrite16 {m : Memory} {a : BitVec 64} (h1 : m.canWrite a 8 = true)
    (h2 : m.canWrite (a + 8#64) 8 = true) : m.canWrite a 16 = true := by
  simp only [Memory.canWrite] at h1 h2 ⊢
  rw [show 16 = 8 + 8 from rfl, allPerm_add]
  simp only [Bool.and_eq_true]
  exact ⟨h1, h2⟩

section
variable {p : Program} {s0 : State} {pc pc' : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem w8' (a : BitVec 64) (i : Nat) :
    a + BitVec.ofNat 64 (8 * i) + 8#64 = a + BitVec.ofNat 64 (8 * (i + 1)) := by
  rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
  congr 2

theorem w16' (a : BitVec 64) (i : Nat) :
    a + BitVec.ofNat 64 (8 * i) + 16#64 = a + BitVec.ofNat 64 (8 * (i + 2)) := by
  rw [BitVec.add_assoc, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
  congr 2

/-- `ldp q_t1, q_t2, [x_b, #off]` from words `k … k+3` of the word list in front. -/
theorem x_ldpq_w {t1 t2 b : BitVec 5} {off x a lo1 hi1 lo2 hi2 : BitVec 64} {ws : List (BitVec 64)}
    {Fm : SepProp} {k : Nat} (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldpSimd .Q128 t1 t2 (.Offset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm) (hk : k + 3 < ws.length)
    (g1 : ws.getD k 0 = lo1) (g2 : ws.getD (k + 1) 0 = hi1) (g3 : ws.getD (k + 2) 0 = lo2)
    (g4 : ws.getD (k + 3) 0 = hi2)
    (h : Reach p (mkS s0 pc' r sp ps m (upd (upd v t1 (hi1 ++ lo1)) t2 (hi2 ++ lo2))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  obtain ⟨f1, c1, -⟩ := sat_words_read hs k (by omega)
  obtain ⟨f2, c2, -⟩ := sat_words_read hs (k + 1) (by omega)
  obtain ⟨f3, c3, -⟩ := sat_words_read hs (k + 2) (by omega)
  obtain ⟨f4, c4, -⟩ := sat_words_read hs (k + 3) hk
  rw [← List.getD_eq_getElem _ 0] at f1 f2 f3 f4
  rw [g1] at f1; rw [g2] at f2; rw [g3] at f3; rw [g4] at f4
  rw [← w8'] at f2 c2
  rw [← w8' a (k + 2)] at f4 c4
  exact y_ldpq_o hb (by rw [ex]; exact hA) (w16' a k) (canRead16 c1 c2) (canRead16 c3 c4) f1 f2 f3 f4 hpc hrun hf h

/-- `stp q_t1, q_t2, [sp, #off]` into words `k … k+3` of the word list in second position. -/
theorem x_stpq_w2 {t1 t2 : BitVec 5} {off a lo1 hi1 lo2 hi2 : BitVec 64} {ws : List (BitVec 64)}
    {X Fm : SepProp} {k : Nat} (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stpSimd .Q128 t1 t2 (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ X ∗ (a ↦₆₄* ws) ∗ Fm) (hk : k + 3 < ws.length) (ev1 : v t1 = hi1 ++ lo1)
    (ev2 : v t2 = hi2 ++ lo2)
    (h : ∀ m', (m' ⊨ X ∗ (a ↦₆₄* (((ws.set k lo1).set (k + 1) hi1).set (k + 2) lo2).set (k + 3) hi2) ∗ Fm) →
      m.KeepsFrozen m' → Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  rw [sepConj_left_comm] at hs
  obtain ⟨-, -, c1⟩ := sat_words_read hs k (by omega)
  obtain ⟨-, -, c2⟩ := sat_words_read hs (k + 1) (by omega)
  obtain ⟨-, -, c3⟩ := sat_words_read hs (k + 2) (by omega)
  obtain ⟨-, -, c4⟩ := sat_words_read hs (k + 3) hk
  rw [← w8'] at c2
  rw [← w8' a (k + 2)] at c4
  refine y_stpq_sp hal hA (w8' a k) (w16' a k) (w8' a (k + 2)) (canWrite16 c1 c2) (canWrite16 c3 c4) ev1 ev2
    hpc hrun hf ?_
  refine Reach.wr64x4 k hs rfl rfl rfl rfl hk ?_
  intro m' hm' hk'
  exact h m' (by rw [sepConj_left_comm]; exact hm') hk'

end

end X25519Dalek.EMulB
end

section
/-! # Block 13 calls of `Scalar::as_radix_16` and `EdwardsPoint::mul_by_pow_2` (k = 4) through their
published contracts -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

abbrev p2Name : String := "<curve25519_dalek::edwards::EdwardsPoint>::mul_by_pow_2"

theorem lk_p2 : lookupBlockSym p2Name x25519CliMultiLib.blocks = some (9, 0) := by decide +kernel

/-- A call of `mul_by_pow_2(·, 4)` (block 9): `out ← [16] self`, callee frame 912 bytes. -/
theorem call_p2 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {Q : State → Prop}
    {s0 : State} {pc : BitVec 64} {rf : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState}
    {m : Memory} {vf : BitVec 5 → BitVec 128} {out self : BitVec 64} {O A : List (BitVec 8)} {R : SepProp}
    (hpc : pc = mpl.base 9 + BitVec.ofNat 64 0) (hrun : s0.status = .Running)
    (hal : (sp &&& 15#64) = 0#64) (hCL : x25519CliMultiLib.CodeLoaded mpl m)
    (h8 : rf 8#5 = out) (h0 : rf 0#5 = self) (h1 : BitVec.truncate 32 (rf 1#5) = 4#32)
    (hO : O.length = 160) (hA : fe51Point4Bounded A (2 ^ 53))
    (hm : m ⊨ (self ↦ₛ A) ∗ (out ↦ₛ O) ∗ memRegion (sp - BitVec.ofNat 64 912) 912 ∗ R)
    (hcont : ∀ (sf : State) (res : List (BitVec 8)), sf.status = .Running → sf.sp = sp →
      CSRegs sf rf → calleeSavedVRegs sf = VRegFile.calleeSaved ⟨vf⟩ →
      (sf.mem ⊨ (out ↦ₛ res) ∗ (self ↦ₛ A) ∗ memRegion (sp - BitVec.ofNat 64 912) 912 ∗ R) →
      m.KeepsFrozen sf.mem → fe51Point4Bounded res (2 ^ 52) →
      edExtOfBytes res = edDouble4 (edExtOfBytes A) →
      Reach (bprog mpl 13) (mkS sf (rf 30#5) sf.regs.regs sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl 13) (mkS s0 pc rf sp ps m vf) Q := by
  have hpre := sat_pre3 (φ := (mkS s0 pc rf sp ps m vf).readReg64 Reg.x8 = out ∧
      (mkS s0 pc rf sp ps m vf).readReg64 Reg.x0 = self ∧
      (mkS s0 pc rf sp ps m vf).readReg32 Reg.x1 = 4#32 ∧ O.length = 160 ∧
      fe51Point4Bounded A (2 ^ 53) ∧ (4#32 : BitVec 32) = 4#32)
    ⟨by simp [h8], by simp [h0], by simpa [State.readReg32] using h1, hO, hA, rfl⟩ hm
  refine Reach.callS hP 13 fnOk_edwardsPoint_mul_by_pow_2_four_v2 lk_p2 (by decide) (out, self, 4#32, O, A) R
    hpc hrun hal hCL hpre ?_ ?_ ?_ ?_
  · intro sf; exact not_sat_false
  · intro c sf; exact not_sat_false
  · intro sf; exact not_sat_false
  intro sf hrunf hspf hcs hv hpost hkf
  simp only [stackFrame, hspf] at hpost
  obtain ⟨res, hφ, hpost⟩ := post_unpack (φ := fun res => fe51Point4Bounded res (2 ^ 52) ∧
      edExtOfBytes res = edDouble4 (edExtOfBytes A)) (P := (self ↦ₛ A) ∗
    memRegion (sp - BitVec.ofNat 64 912) 912) (Satisfies.of_eq hpost)
  exact hcont sf res hrunf hspf hcs hv (Satisfies.of_eq hpost) hkf hφ.1 hφ.2

end X25519Dalek.EMulB
end

section
/-! # Block 13: the two loops of `mul_base`, by induction over the one-iteration statements
(generated by tools/gen_loops.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem loopWith_step {α : Type} (step : Nat → α → α) (i rem : Nat) (acc : α) :
    edMulBaseLoopWith step i (rem + 1) acc = edMulBaseLoopWith step (i + 1) rem (step i acc) := rfl
theorem loopWith_zero {α : Type} (step : Nat → α → α) (i : Nat) (acc : α) :
    edMulBaseLoopWith step i 0 acc = acc := rfl
theorem loop_step (T D : List (BitVec 8)) (par i rem : Nat) (acc : EdExtPoint) :
    edMulBaseLoop T D par i (rem + 1) acc =
      edMulBaseLoop T D par (i + 1) rem (edMulBaseStep T i (D.getD (2 * i + par) 0#8) acc) := by
  unfold edMulBaseLoop
  rw [loopWith_step]
  unfold edMulBaseStepAt
  rfl
theorem loop_zero (T D : List (BitVec 8)) (par : Nat) (acc : EdExtPoint) :
    edMulBaseLoop T D par 32 0 acc = acc := by
  unfold edMulBaseLoop; exact loopWith_zero _ _ _

/-- The odd loop of `mul_base`, by induction on the remaining iterations, from the published
one-iteration statement. -/
theorem odd_loop {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {S table : BitVec 64}
    {T D : List (BitVec 8)} {F : SepProp} {r0 : BitVec 5 → BitVec 64}
    {V0 : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {Q : State → Prop} (htab : fe51BasepointTable32Bounded T (2 ^ 53)) (hD : D.length = 64)
    (hal : (S &&& 15#64) = 0#64) :
    ∀ (rem i : Nat) (s : State) (A E C N : List (BitVec 8)) (acc : EdExtPoint), i + rem = 32 →
      x25519CliMultiLib.CodeLoaded mpl s.mem → s.status = .Running →
      s.pc = (if rem = 0 then mpl.base 13 + 316#64 else mpl.base 13 + 152#64) → s.sp = S →
      s.regs.regs 20#5 = table →
      s.regs.regs 21#5 = S + 232#64 →
      s.regs.regs 22#5 = S →
      s.regs.regs 24#5 = S + 392#64 →
      s.regs.regs 25#5 = 960#64 →
      s.regs.regs 29#5 = S + 672#64 →
      s.regs.regs 23#5 = BitVec.ofNat 64 (2 * i) →
      KeepHi s.regs.regs r0 → VRegFile.calleeSaved s.vregs = V0 →
      fe51Point4Bounded A (2 ^ 52) → edExtOfBytes A = acc → E.length = 160 → C.length = 160 →
      N.length = 120 →
      (s.mem ⊨ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 232#64) ↦ₛ E) ∗
        ((S + 392#64) ↦ₛ C) ∗ ((S + 552#64) ↦ₛ N) ∗ memRegion (S - 912#64) 912 ∗ F) →
      (∀ (s' : State) (A' E' C' N' : List (BitVec 8)), x25519CliMultiLib.CodeLoaded mpl s'.mem →
        s'.status = .Running → s'.pc = mpl.base 13 + 316#64 → s'.sp = S →
        s'.regs.regs 20#5 = table →
        s'.regs.regs 21#5 = S + 232#64 →
        s'.regs.regs 22#5 = S →
        s'.regs.regs 24#5 = S + 392#64 →
        s'.regs.regs 25#5 = 960#64 →
        s'.regs.regs 29#5 = S + 672#64 →
        s'.regs.regs 23#5 = BitVec.ofNat 64 64 →
        KeepHi s'.regs.regs r0 → VRegFile.calleeSaved s'.vregs = V0 →
        fe51Point4Bounded A' (2 ^ 52) → edExtOfBytes A' = edMulBaseLoop T D 1 i rem acc →
        E'.length = 160 → C'.length = 160 → N'.length = 120 →
        (s'.mem ⊨ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A') ∗ ((S + 232#64) ↦ₛ E') ∗
          ((S + 392#64) ↦ₛ C') ∗ ((S + 552#64) ↦ₛ N') ∗ memRegion (S - 912#64) 912 ∗ F) →
        Reach (bprog mpl 13) s' Q) →
      Reach (bprog mpl 13) s Q := by
  intro rem
  induction rem with
  | zero =>
    intro i s A E C N acc hrem hCL hrun hpc hsp h20 h21 h22 h24 h25 h29 h23 hkh hv hA hAv hE hC hN hs hcont
    have hi : i = 32 := by omega
    subst hi
    exact hcont s A E C N hCL hrun (hpc.trans (if_pos rfl)) hsp h20 h21 h22 h24 h25 h29 h23 hkh hv hA (hAv.trans (loop_zero T D 1 acc).symm) hE hC hN hs
  | succ rem ih =>
    intro i s A E C N acc hrem hCL hrun hpc hsp h20 h21 h22 h24 h25 h29 h23 hkh hv hA hAv hE hC hN hs hcont
    have hi : i < 32 := by omega
    rw [if_neg (by omega)] at hpc
    obtain ⟨s', hst, hrun', hpc', hsp', h23', hkh', hv', A', E', C', N', hm', hA', hAv', hE', hC', hN'⟩ :=
      X25519Dalek.basepointTable_mul_base_odd_iter hP hCL hi hrun hpc hsp hal h20 h21 h22 h23 h24 h25 h29 htab hD hA hE hC hN hs
    refine Reach.steps hst ?_
    have kp : ∀ k : BitVec 5, k ≠ 23#5 ∧ 19 ≤ k.toNat ∧ k.toNat < 30 → s'.regs.regs k = s.regs.regs k :=
      fun k hk => hkh' k hk.1 hk.2.1 hk.2.2
    have hpcn : s'.pc = if rem = 0 then mpl.base 13 + 316#64 else mpl.base 13 + 152#64 := by
      rw [hpc']; by_cases h : i = 31
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    refine ih (i + 1) s' A' E' C' N' (edMulBaseStep T i (D.getD (2 * i + 1) 0#8) acc) (by omega)
      (libCodeLoaded_keepsFrozen hCL (X25519Dalek.steps_keepsFrozen_v2 hst)) hrun'
      hpcn hsp' ((kp 20#5 (by decide)).trans h20) ((kp 21#5 (by decide)).trans h21) ((kp 22#5 (by decide)).trans h22) ((kp 24#5 (by decide)).trans h24) ((kp 25#5 (by decide)).trans h25) ((kp 29#5 (by decide)).trans h29) h23'
      (fun k a b c => (hkh' k a b c).trans (hkh k a b c)) (hv'.trans hv) hA' (hAv'.trans (by rw [hAv]; try rw [Nat.add_zero])) hE' hC' hN' hm' ?_
    intro s'' A'' E'' C'' N'' hCL'' hrun'' hpc'' hsp'' h20'' h21'' h22'' h24'' h25'' h29'' h23'' hkh'' hv'' hA'' hAv'' hE'' hC'' hN'' hm''
    exact hcont s'' A'' E'' C'' N'' hCL'' hrun'' hpc'' hsp'' h20'' h21'' h22'' h24'' h25'' h29'' h23'' hkh'' hv'' hA'' (hAv''.trans (loop_step T D 1 i rem acc).symm) hE'' hC'' hN'' hm''

/-- The even loop of `mul_base`, by induction on the remaining iterations, from the published
one-iteration statement. -/
theorem even_loop {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {S table : BitVec 64}
    {T D : List (BitVec 8)} {F : SepProp} {r0 : BitVec 5 → BitVec 64}
    {V0 : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {Q : State → Prop} (htab : fe51BasepointTable32Bounded T (2 ^ 53)) (hD : D.length = 64)
    (hal : (S &&& 15#64) = 0#64) :
    ∀ (rem i : Nat) (s : State) (A E C N : List (BitVec 8)) (acc : EdExtPoint), i + rem = 32 →
      x25519CliMultiLib.CodeLoaded mpl s.mem → s.status = .Running →
      s.pc = (if rem = 0 then mpl.base 13 + 580#64 else mpl.base 13 + 416#64) → s.sp = S →
      s.regs.regs 20#5 = table →
      s.regs.regs 21#5 = S + 232#64 →
      s.regs.regs 22#5 = S + 392#64 →
      s.regs.regs 24#5 = S + 232#64 →
      s.regs.regs 25#5 = 960#64 →
      s.regs.regs 26#5 = S →
      s.regs.regs 29#5 = S + 672#64 →
      s.regs.regs 23#5 = BitVec.ofNat 64 (2 * i) →
      KeepHi s.regs.regs r0 → VRegFile.calleeSaved s.vregs = V0 →
      fe51Point4Bounded A (2 ^ 52) → edExtOfBytes A = acc → E.length = 160 → C.length = 160 →
      N.length = 120 →
      (s.mem ⊨ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 232#64) ↦ₛ E) ∗
        ((S + 392#64) ↦ₛ C) ∗ ((S + 552#64) ↦ₛ N) ∗ memRegion (S - 912#64) 912 ∗ F) →
      (∀ (s' : State) (A' E' C' N' : List (BitVec 8)), x25519CliMultiLib.CodeLoaded mpl s'.mem →
        s'.status = .Running → s'.pc = mpl.base 13 + 580#64 → s'.sp = S →
        s'.regs.regs 20#5 = table →
        s'.regs.regs 21#5 = S + 232#64 →
        s'.regs.regs 22#5 = S + 392#64 →
        s'.regs.regs 24#5 = S + 232#64 →
        s'.regs.regs 25#5 = 960#64 →
        s'.regs.regs 26#5 = S →
        s'.regs.regs 29#5 = S + 672#64 →
        s'.regs.regs 23#5 = BitVec.ofNat 64 64 →
        KeepHi s'.regs.regs r0 → VRegFile.calleeSaved s'.vregs = V0 →
        fe51Point4Bounded A' (2 ^ 52) → edExtOfBytes A' = edMulBaseLoop T D 0 i rem acc →
        E'.length = 160 → C'.length = 160 → N'.length = 120 →
        (s'.mem ⊨ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A') ∗ ((S + 232#64) ↦ₛ E') ∗
          ((S + 392#64) ↦ₛ C') ∗ ((S + 552#64) ↦ₛ N') ∗ memRegion (S - 912#64) 912 ∗ F) →
        Reach (bprog mpl 13) s' Q) →
      Reach (bprog mpl 13) s Q := by
  intro rem
  induction rem with
  | zero =>
    intro i s A E C N acc hrem hCL hrun hpc hsp h20 h21 h22 h24 h25 h26 h29 h23 hkh hv hA hAv hE hC hN hs hcont
    have hi : i = 32 := by omega
    subst hi
    exact hcont s A E C N hCL hrun (hpc.trans (if_pos rfl)) hsp h20 h21 h22 h24 h25 h26 h29 h23 hkh hv hA (hAv.trans (loop_zero T D 0 acc).symm) hE hC hN hs
  | succ rem ih =>
    intro i s A E C N acc hrem hCL hrun hpc hsp h20 h21 h22 h24 h25 h26 h29 h23 hkh hv hA hAv hE hC hN hs hcont
    have hi : i < 32 := by omega
    rw [if_neg (by omega)] at hpc
    obtain ⟨s', hst, hrun', hpc', hsp', h23', hkh', hv', A', E', C', N', hm', hA', hAv', hE', hC', hN'⟩ :=
      X25519Dalek.basepointTable_mul_base_even_iter hP hCL hi hrun hpc hsp hal h20 h21 h22 h23 h24 h25 h26 h29 htab hD hA hE hC hN hs
    refine Reach.steps hst ?_
    have kp : ∀ k : BitVec 5, k ≠ 23#5 ∧ 19 ≤ k.toNat ∧ k.toNat < 30 → s'.regs.regs k = s.regs.regs k :=
      fun k hk => hkh' k hk.1 hk.2.1 hk.2.2
    have hpcn : s'.pc = if rem = 0 then mpl.base 13 + 580#64 else mpl.base 13 + 416#64 := by
      rw [hpc']; by_cases h : i = 31
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    refine ih (i + 1) s' A' E' C' N' (edMulBaseStep T i (D.getD (2 * i + 0) 0#8) acc) (by omega)
      (libCodeLoaded_keepsFrozen hCL (X25519Dalek.steps_keepsFrozen_v2 hst)) hrun'
      hpcn hsp' ((kp 20#5 (by decide)).trans h20) ((kp 21#5 (by decide)).trans h21) ((kp 22#5 (by decide)).trans h22) ((kp 24#5 (by decide)).trans h24) ((kp 25#5 (by decide)).trans h25) ((kp 26#5 (by decide)).trans h26) ((kp 29#5 (by decide)).trans h29) h23'
      (fun k a b c => (hkh' k a b c).trans (hkh k a b c)) (hv'.trans hv) hA' (hAv'.trans (by rw [hAv]; try rw [Nat.add_zero])) hE' hC' hN' hm' ?_
    intro s'' A'' E'' C'' N'' hCL'' hrun'' hpc'' hsp'' h20'' h21'' h22'' h24'' h25'' h26'' h29'' h23'' hkh'' hv'' hA'' hAv'' hE'' hC'' hN'' hm''
    exact hcont s'' A'' E'' C'' N'' hCL'' hrun'' hpc'' hsp'' h20'' h21'' h22'' h24'' h25'' h26'' h29'' h23'' hkh'' hv'' hA'' (hAv''.trans (loop_step T D 0 i rem acc).symm) hE'' hC'' hN'' hm''

end X25519Dalek.EMulB
end

section
/-! # Block 13: per-offset instruction fetch (generated by tools/gen_code13.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem blk13 : blk 13 = x25519CliBlk13 := rfl

theorem len13 : x25519CliBlk13.code.length = 668 := by decide +kernel

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (j : Nat) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem c13_316 : (bprog mpl j).fetchMem m (mpl.base 13 + 316#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.sp) 0x188#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 316) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.sp) 0x188#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_320 : (bprog mpl j).fetchMem m (mpl.base 13 + 320#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x040#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 320) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x040#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_324 : (bprog mpl j).fetchMem m (mpl.base 13 + 324#64) =
    some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x01#5) 0x0004#16 0) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 324) (inst := (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x01#5) 0x0004#16 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_328 : (bprog mpl j).fetchMem m (mpl.base 13 + 328#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x16#5) (Reg.sp) 0x188#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 328) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x16#5) (Reg.sp) 0x188#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_332 {j' offj : Nat} (hlk : lookupBlockSym p2Name x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 13 + 332#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 13 + BitVec.ofNat 64 332))) :=
  fetch_bl hP hCL (i := 13) (by decide) j (off := 332) (name := p2Name) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c13_336 : (bprog mpl j).fetchMem m (mpl.base 13 + 336#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000100#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 336) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000100#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_340 : (bprog mpl j).fetchMem m (mpl.base 13 + 340#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x17#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 340) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x17#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_344 : (bprog mpl j).fetchMem m (mpl.base 13 + 344#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x18#5) (Reg.sp) 0x0e8#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 344) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x18#5) (Reg.sp) 0x0e8#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_348 : (bprog mpl j).fetchMem m (mpl.base 13 + 348#64) =
    some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x19#5) 0x03c0#16 0) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 348) (inst := (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x19#5) 0x03c0#16 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_352 : (bprog mpl j).fetchMem m (mpl.base 13 + 352#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1a#5) (Reg.sp) 0x000#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 352) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1a#5) (Reg.sp) 0x000#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_356 : (bprog mpl j).fetchMem m (mpl.base 13 + 356#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 356) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_360 : (bprog mpl j).fetchMem m (mpl.base 13 + 360#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x02#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000120#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 360) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x02#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000120#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_364 : (bprog mpl j).fetchMem m (mpl.base 13 + 364#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x02#5 (AddrMode.Offset (Reg.sp) 0x00000000000000c0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 364) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x02#5 (AddrMode.Offset (Reg.sp) 0x00000000000000c0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_368 : (bprog mpl j).fetchMem m (mpl.base 13 + 368#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x00000000000000c0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 368) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x00000000000000c0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_372 : (bprog mpl j).fetchMem m (mpl.base 13 + 372#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000060#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 372) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000060#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_376 : (bprog mpl j).fetchMem m (mpl.base 13 + 376#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x02#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x00000000000000e0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 376) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x02#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x00000000000000e0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_380 : (bprog mpl j).fetchMem m (mpl.base 13 + 380#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x02#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000080#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 380) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x02#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000080#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_384 : (bprog mpl j).fetchMem m (mpl.base 13 + 384#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x00000000000000a0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 384) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x00000000000000a0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_388 : (bprog mpl j).fetchMem m (mpl.base 13 + 388#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 388) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_392 : (bprog mpl j).fetchMem m (mpl.base 13 + 392#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x17#5) 0x040#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 392) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x17#5) 0x040#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_396 : (bprog mpl j).fetchMem m (mpl.base 13 + 396#64) =
    some (Instr.bCond (CondCode.NE) 0x0000000000000014#64) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 396) (inst := (Instr.bCond (CondCode.NE) 0x0000000000000014#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_580 : (bprog mpl j).fetchMem m (mpl.base 13 + 580#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 580) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_584 : (bprog mpl j).fetchMem m (mpl.base 13 + 584#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000060#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 584) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000060#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_588 : (bprog mpl j).fetchMem m (mpl.base 13 + 588#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x02#5 (AddrMode.Offset (Reg.sp) 0x00000000000000c0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 588) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x02#5 (AddrMode.Offset (Reg.sp) 0x00000000000000c0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_592 : (bprog mpl j).fetchMem m (mpl.base 13 + 592#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x02#5 (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000080#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 592) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x02#5 (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000080#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_596 : (bprog mpl j).fetchMem m (mpl.base 13 + 596#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000060#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 596) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000060#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_600 : (bprog mpl j).fetchMem m (mpl.base 13 + 600#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000020#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 600) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000020#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_604 : (bprog mpl j).fetchMem m (mpl.base 13 + 604#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x02#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000080#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 604) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x02#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000080#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_608 : (bprog mpl j).fetchMem m (mpl.base 13 + 608#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x02#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 608) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x02#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_612 : (bprog mpl j).fetchMem m (mpl.base 13 + 612#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 612) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_616 : (bprog mpl j).fetchMem m (mpl.base 13 + 616#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000000#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 616) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000000#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_620 : (bprog mpl j).fetchMem m (mpl.base 13 + 620#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.sp) (Reg.sp) 0x2a0#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 620) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.sp) (Reg.sp) 0x2a0#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_624 : (bprog mpl j).fetchMem m (mpl.base 13 + 624#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 624) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_628 : (bprog mpl j).fetchMem m (mpl.base 13 + 628#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x1c#5) (AddrMode.Offset (Reg.sp) 0x0000000000000010#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 628) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x1c#5) (AddrMode.Offset (Reg.sp) 0x0000000000000010#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_632 : (bprog mpl j).fetchMem m (mpl.base 13 + 632#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 632) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_636 : (bprog mpl j).fetchMem m (mpl.base 13 + 636#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 636) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_640 : (bprog mpl j).fetchMem m (mpl.base 13 + 640#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 640) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_644 : (bprog mpl j).fetchMem m (mpl.base 13 + 644#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.PostIndex (Reg.sp) 0x0000000000000060#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 644) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.PostIndex (Reg.sp) 0x0000000000000060#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_648 : (bprog mpl j).fetchMem m (mpl.base 13 + 648#64) =
    some (Instr.ret (Reg.gpr 0x1e#5)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 648) (inst := (Instr.ret (Reg.gpr 0x1e#5))) (by decide) rfl (by decide +kernel) hk
  exact this

end

end X25519Dalek.EMulB
end

section
/-! # Relocated `ADRP`/`ADD` (and their relaxed `NOP`/`ADR` form): loading a `.rodata` address

Decoding lemmas copied from the sibling batch's `Solutions/X25519DalekEdwards/Reloc.lean`, itself from
the zlib CRC-32 mission's `ZlibCrc32.Small.RelocBase`/`RelocTab`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj


section words
variable (D : BitVec 64)

end words

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (j : Nat) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

end

end X25519Dalek.EMulB
end

section
/-! # Block 13 outside the loops: stores into and loads from word lists, the constant `ONE` -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

section
variable {p : Program} {s0 : State} {pc pc' : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem wcan {a : BitVec 64} {ws : List (BitVec 64)} {Fm : SepProp} (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm)
    (k : Nat) (hk : k < ws.length) : m.canWrite (a + BitVec.ofNat 64 (8 * k)) 8 = true :=
  (sat_words_read hs k hk).2.2

theorem wread {a : BitVec 64} {ws : List (BitVec 64)} {Fm : SepProp} (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm)
    (k : Nat) (hk : k < ws.length) :
    m.read64 (a + BitVec.ofNat 64 (8 * k)) = ws.getD k 0 ∧ m.canRead (a + BitVec.ofNat 64 (8 * k)) 8 = true := by
  obtain ⟨f, c, -⟩ := sat_words_read hs k hk
  exact ⟨by rw [f, List.getD_eq_getElem], c⟩

/-- `stp q_t1, q_t2, [x_b, #off]` into words `k … k+3` of the list in second position. -/
theorem x_stpq_ow2 {t1 t2 b : BitVec 5} {off x a lo1 hi1 lo2 hi2 : BitVec 64} {ws : List (BitVec 64)}
    {X Fm : SepProp} {k : Nat} (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stpSimd .Q128 t1 t2 (.Offset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ X ∗ (a ↦₆₄* ws) ∗ Fm) (hk : k + 3 < ws.length) (ev1 : v t1 = hi1 ++ lo1)
    (ev2 : v t2 = hi2 ++ lo2)
    (h : ∀ m', (m' ⊨ X ∗ (a ↦₆₄* (((ws.set k lo1).set (k + 1) hi1).set (k + 2) lo2).set (k + 3) hi2) ∗ Fm) →
      m.KeepsFrozen m' → Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  rw [sepConj_left_comm] at hs
  have c2 := wcan hs (k + 1) (by omega)
  have c4 := wcan hs (k + 3) hk
  rw [← w8'] at c2
  rw [← w8' a (k + 2)] at c4
  refine y_stpq_o hb (by rw [ex]; exact hA) (w8' a k) (w16' a k) (w8' a (k + 2))
    (canWrite16 (wcan hs k (by omega)) c2) (canWrite16 (wcan hs (k + 2) (by omega)) c4) ev1 ev2 hpc hrun hf ?_
  refine Reach.wr64x4 k hs rfl rfl rfl rfl hk ?_
  intro m' hm' hk'
  exact h m' (by rw [sepConj_left_comm]; exact hm') hk'

/-- `ldp q_t1, q_t2, [sp, #off]` from words `k … k+3` of the list in front. -/
theorem x_ldpq_spw {t1 t2 : BitVec 5} {off a lo1 hi1 lo2 hi2 : BitVec 64} {ws : List (BitVec 64)}
    {Fm : SepProp} {k : Nat} (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldpSimd .Q128 t1 t2 (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm) (hk : k + 3 < ws.length)
    (g1 : ws.getD k 0 = lo1) (g2 : ws.getD (k + 1) 0 = hi1) (g3 : ws.getD (k + 2) 0 = lo2)
    (g4 : ws.getD (k + 3) 0 = hi2)
    (h : Reach p (mkS s0 pc' r sp ps m (upd (upd v t1 (hi1 ++ lo1)) t2 (hi2 ++ lo2))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  obtain ⟨f1, c1⟩ := wread hs k (by omega)
  obtain ⟨f2, c2⟩ := wread hs (k + 1) (by omega)
  obtain ⟨f3, c3⟩ := wread hs (k + 2) (by omega)
  obtain ⟨f4, c4⟩ := wread hs (k + 3) hk
  rw [g1] at f1; rw [g2] at f2; rw [g3] at f3; rw [g4] at f4
  rw [← w8'] at f2 c2
  rw [← w8' a (k + 2)] at f4 c4
  exact y_ldpq_sp hal hA (w16' a k) (canRead16 c1 c2) (canRead16 c3 c4) f1 f2 f3 f4 hpc hrun hf h

/-- `ldp x_d1, x_d2, [sp, #off]` from words `k`, `k+1`. -/
theorem x_ldp_w {d1 d2 : BitVec 5} {off a w1 w2 : BitVec 64} {ws : List (BitVec 64)} {Fm : SepProp}
    {k : Nat} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm) (hk : k + 1 < ws.length)
    (g1 : ws.getD k 0 = w1) (g2 : ws.getD (k + 1) 0 = w2)
    (h : Reach p (mkS s0 pc' (upd (upd r d1 w1) d2 w2) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  obtain ⟨f1, c1⟩ := wread hs k (by omega)
  obtain ⟨f2, c2⟩ := wread hs (k + 1) hk
  rw [g1] at f1; rw [g2] at f2
  exact y_ldp_sp hd1 hd2 hal hA (w8' a k) c1 c2 f1 f2 hpc hrun hf h

theorem x_ldr_w {d : BitVec 5} {off a w : BitVec 64} {ws : List (BitVec 64)} {Fm : SepProp}
    {k : Nat} (hd : d ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W64 .X64 false (.gpr d) (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm) (hk : k < ws.length) (g : ws.getD k 0 = w)
    (h : Reach p (mkS s0 pc' (upd r d w) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  obtain ⟨f, c⟩ := wread hs k hk
  rw [g] at f
  exact y_ldr_sp hd hal hA c f hpc hrun hf h

/-- `ldp x_d1, x_d2, [sp], #off` from words `k`, `k+1` (`sp` is word `k`'s address). -/
theorem x_ldp_post_w {d1 d2 : BitVec 5} {off a w1 w2 : BitVec 64} {ws : List (BitVec 64)} {Fm : SepProp}
    {k : Nat} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.PostIndex .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm) (hk : k + 1 < ws.length)
    (g1 : ws.getD k 0 = w1) (g2 : ws.getD (k + 1) 0 = w2)
    (h : Reach p (mkS s0 pc' (upd (upd r d1 w1) d2 w2) (sp + off) ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  obtain ⟨f1, c1⟩ := wread hs k (by omega)
  obtain ⟨f2, c2⟩ := wread hs (k + 1) hk
  rw [g1] at f1; rw [g2] at f2
  rw [← w8'] at f2 c2
  subst hA
  exact y_ldp_post hd1 hd2 hal c1 c2 f1 f2 hpc hrun hf h

end

/-! ## The constant `FieldElement51::ONE` -/

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem addK0 (x : BitVec 64) : x + (0x000#12 : BitVec 12).setWidth 64 = x := by simp

theorem aoff0 (a : BitVec 64) : a = a + BitVec.ofNat 64 (8 * 0) := by simp

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

/-- Abstract the register file after a write of two different registers. -/
theorem Reach.absR2 {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}
    {d1 d2 : BitVec 5} {t1 t2 : BitVec 64} (hd : d1 ≠ d2)
    (h : ∀ r' : BitVec 5 → BitVec 64, (∀ k, k ≠ d1 → k ≠ d2 → r' k = r k) → r' d1 = t1 → r' d2 = t2 →
      Reach p (mkS s0 pc r' sp ps m v) Q) :
    Reach p (mkS s0 pc (upd (upd r d1 t1) d2 t2) sp ps m v) Q :=
  h _ (fun _ h1 h2 => (upd_ne _ t2 h2).trans (upd_ne r t1 h1))
    ((upd_ne _ t2 hd).trans (upd_same r d1 t1)) (upd_same _ d2 t2)

end X25519Dalek.EMulB
end

section
/-! # Block 13: the 1680-byte stack frame split into the function's buffers and merged back;
the identity accumulator -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem asub0 (S : BitVec 64) (a : Nat) : S - BitVec.ofNat 64 a + BitVec.ofNat 64 a = S := by
  rw [BitVec.sub_add_cancel]

theorem asubp (S : BitVec 64) (a b c : Nat) (h : b = a + c) :
    S - BitVec.ofNat 64 a + BitVec.ofNat 64 b = S + BitVec.ofNat 64 c := by
  subst h; rw [BitVec.ofNat_add]; abel

theorem mr_split {m : Memory} {a b : BitVec 64} {F : SepProp} (n k : Nat) (hnk : n + k < 2 ^ 64)
    (hb : a + BitVec.ofNat 64 n = b) (hs : m ⊨ memRegion a (n + k) ∗ F) :
    m ⊨ memRegion b k ∗ memRegion a n ∗ F := by
  have := sat_mr_split n k hnk b hb hs
  exact Satisfies.of_eq this

theorem frame_in {m : Memory} {S : BitVec 64} {X : SepProp}
    (hs : m ⊨ memRegion (S - 912#64) 1680 ∗ X) :
    ∃ (E0 C0 N0 : List (BitVec 8)), E0.length = 160 ∧ C0.length = 160 ∧ N0.length = 120 ∧
      (m ⊨ memRegion (S + 672#64) 96 ∗ memRegion (S + 64#64) 160 ∗ memRegion S 64 ∗ ((S + 232#64) ↦ₛ E0) ∗
        ((S + 392#64) ↦ₛ C0) ∗ ((S + 552#64) ↦ₛ N0) ∗ memRegion (S + 224#64) 8 ∗
        memRegion (S - 912#64) 912 ∗ X) := by
  have h1 := mr_split (a := S - 912#64) (b := S) 912 768 (by norm_num) (asub0 S 912) hs
  have h2 := mr_split (a := S) 64 704 (by norm_num) rfl h1
  have h3 := mr_split (a := S + 64#64) 160 544 (by norm_num) (aadd S 64 160 224 rfl) h2
  have h4 := mr_split (a := S + 224#64) 8 536 (by norm_num) (aadd S 224 8 232 rfl) h3
  have h5 := mr_split (a := S + 232#64) 160 376 (by norm_num) (aadd S 232 160 392 rfl) h4
  have h6 := mr_split (a := S + 392#64) 160 216 (by norm_num) (aadd S 392 160 552 rfl) h5
  have h7 := mr_split (a := S + 552#64) 120 96 (by norm_num) (aadd S 552 120 672 rfl) h6
  have h9 : m ⊨ memRegion (S + 552#64) 120 ∗ (memRegion (S + 672#64) 96 ∗ memRegion (S + 392#64) 160 ∗
      memRegion (S + 232#64) 160 ∗ memRegion (S + 224#64) 8 ∗ memRegion (S + 64#64) 160 ∗ memRegion S 64 ∗
      memRegion (S - 912#64) 912 ∗ X) := Satisfies.of_eq h7
  obtain ⟨N0, hN, h10⟩ := memRegion_bytes _ 120 (by norm_num) h9
  have h11 : m ⊨ memRegion (S + 392#64) 160 ∗ (((S + 552#64) ↦ₛ N0) ∗ memRegion (S + 672#64) 96 ∗
      memRegion (S + 232#64) 160 ∗ memRegion (S + 224#64) 8 ∗ memRegion (S + 64#64) 160 ∗ memRegion S 64 ∗
      memRegion (S - 912#64) 912 ∗ X) := Satisfies.of_eq h10
  obtain ⟨C0, hC, h12⟩ := memRegion_bytes _ 160 (by norm_num) h11
  have h13 : m ⊨ memRegion (S + 232#64) 160 ∗ (((S + 392#64) ↦ₛ C0) ∗ ((S + 552#64) ↦ₛ N0) ∗
      memRegion (S + 672#64) 96 ∗ memRegion (S + 224#64) 8 ∗ memRegion (S + 64#64) 160 ∗ memRegion S 64 ∗
      memRegion (S - 912#64) 912 ∗ X) := Satisfies.of_eq h12
  obtain ⟨E0, hE, h14⟩ := memRegion_bytes _ 160 (by norm_num) h13
  exact ⟨E0, C0, N0, hE, hC, hN, Satisfies.of_eq h14⟩

theorem frame_out {m : Memory} {S : BitVec 64} {X : SepProp} {D A E C N : List (BitVec 8)}
    {W : List (BitVec 64)} (hD : D.length = 64) (hA : A.length = 160) (hE : E.length = 160)
    (hC : C.length = 160) (hN : N.length = 120) (hW : W.length = 12)
    (hs : m ⊨ ((S + 672#64) ↦₆₄* W) ∗ ((S + 64#64) ↦ₛ A) ∗ (S ↦ₛ D) ∗ ((S + 232#64) ↦ₛ E) ∗
      ((S + 392#64) ↦ₛ C) ∗ ((S + 552#64) ↦ₛ N) ∗ memRegion (S + 224#64) 8 ∗
      memRegion (S - 912#64) 912 ∗ X) :
    m ⊨ memRegion (S - 912#64) 1680 ∗ X := by
  rw [words_eq_bytes] at hs
  have hWl : (W.flatMap unpack64).length = 96 := by rw [flatMap_unpack64_length, hW]
  have h1 := sat_mr_bytes (a := S - 912#64) (b := S) 912 (by norm_num)
    (asub0 S 912).symm (Satisfies.of_eq hs (Q := memRegion (S - 912#64) 912 ∗
      (S ↦ₛ D) ∗ (((S + 672#64) ↦ₛ W.flatMap unpack64) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 232#64) ↦ₛ E) ∗
      ((S + 392#64) ↦ₛ C) ∗ ((S + 552#64) ↦ₛ N) ∗ memRegion (S + 224#64) 8 ∗ X)))
  rw [hD] at h1
  have h2 := sat_mr_bytes (a := S - 912#64) (b := S + 64#64) (912 + 64) (by norm_num)
    (asubp S 912 (912 + 64) 64 rfl).symm (Satisfies.of_eq h1 (Q := memRegion (S - 912#64) (912 + 64) ∗
      ((S + 64#64) ↦ₛ A) ∗ (((S + 672#64) ↦ₛ W.flatMap unpack64) ∗ ((S + 232#64) ↦ₛ E) ∗
      ((S + 392#64) ↦ₛ C) ∗ ((S + 552#64) ↦ₛ N) ∗ memRegion (S + 224#64) 8 ∗ X)))
  rw [hA] at h2
  have h3 := sat_mr_merge (a := S - 912#64) (b := S + 224#64) (912 + 64 + 160) 8 (by norm_num)
    (asubp S 912 (912 + 64 + 160) 224 rfl).symm (Satisfies.of_eq h2 (Q := memRegion (S - 912#64) (912 + 64 + 160) ∗
      memRegion (S + 224#64) 8 ∗ (((S + 672#64) ↦ₛ W.flatMap unpack64) ∗ ((S + 232#64) ↦ₛ E) ∗
      ((S + 392#64) ↦ₛ C) ∗ ((S + 552#64) ↦ₛ N) ∗ X)))
  have h4 := sat_mr_bytes (a := S - 912#64) (b := S + 232#64) (912 + 64 + 160 + 8) (by norm_num)
    (asubp S 912 (912 + 64 + 160 + 8) 232 rfl).symm (Satisfies.of_eq h3 (Q := memRegion (S - 912#64) (912 + 64 + 160 + 8) ∗
      ((S + 232#64) ↦ₛ E) ∗ (((S + 672#64) ↦ₛ W.flatMap unpack64) ∗
      ((S + 392#64) ↦ₛ C) ∗ ((S + 552#64) ↦ₛ N) ∗ X)))
  rw [hE] at h4
  have h5 := sat_mr_bytes (a := S - 912#64) (b := S + 392#64) (912 + 64 + 160 + 8 + 160) (by norm_num)
    (asubp S 912 (912 + 64 + 160 + 8 + 160) 392 rfl).symm (Satisfies.of_eq h4 (Q := memRegion (S - 912#64) (912 + 64 + 160 + 8 + 160) ∗
      ((S + 392#64) ↦ₛ C) ∗ (((S + 672#64) ↦ₛ W.flatMap unpack64) ∗ ((S + 552#64) ↦ₛ N) ∗ X)))
  rw [hC] at h5
  have h6 := sat_mr_bytes (a := S - 912#64) (b := S + 552#64) (912 + 64 + 160 + 8 + 160 + 160) (by norm_num)
    (asubp S 912 (912 + 64 + 160 + 8 + 160 + 160) 552 rfl).symm (Satisfies.of_eq h5 (Q := memRegion (S - 912#64) (912 + 64 + 160 + 8 + 160 + 160) ∗
      ((S + 552#64) ↦ₛ N) ∗ (((S + 672#64) ↦ₛ W.flatMap unpack64) ∗ X)))
  rw [hN] at h6
  have h7 := sat_mr_bytes (a := S - 912#64) (b := S + 672#64) (912 + 64 + 160 + 8 + 160 + 160 + 120) (by norm_num)
    (asubp S 912 (912 + 64 + 160 + 8 + 160 + 160 + 120) 672 rfl).symm h6
  rw [hWl] at h7
  exact h7

theorem srd_go_len (a : List (BitVec 8)) : ∀ (idx : Nat) (c : Int) (acc : List (BitVec 8)),
    (scalarRadix16Digits.go a idx c acc).length = idx + acc.length
  | 0, c, acc => by simp [scalarRadix16Digits.go]
  | k + 1, c, acc => by
    unfold scalarRadix16Digits.go
    simp only []
    split <;> (rw [srd_go_len]; simp; omega)
theorem srd_length (a : List (BitVec 8)) : (scalarRadix16Digits a).length = 64 := by
  unfold scalarRadix16Digits; rw [srd_go_len]; rfl
theorem post_intro5 {m : Memory} {A B C D R : SepProp} {out : BitVec 64} {res : List (BitVec 8)}
    {P : List (BitVec 8) → Prop} (h : m ⊨ A ∗ B ∗ C ∗ D ∗ (out ↦ₛ res) ∗ R) (hp : P res) :
    m ⊨ (A ∗ B ∗ C ∗ D ∗ ∃∗ r, (out ↦ₛ r) ∗ ⌜P r⌝) ∗ R := by
  have e : ((A ∗ B ∗ C ∗ D ∗ ∃∗ r, (out ↦ₛ r) ∗ ⌜P r⌝) ∗ R) =
      ((∃∗ r, (out ↦ₛ r) ∗ ⌜P r⌝) ∗ (A ∗ B ∗ C ∗ D ∗ R)) := by ac_rfl
  rw [e, sepExists_sepConj, sat_sepExists]
  refine ⟨res, ?_⟩
  have e2 : (((out ↦ₛ res) ∗ ⌜P res⌝) ∗ (A ∗ B ∗ C ∗ D ∗ R)) = (⌜P res⌝ ∗ (A ∗ B ∗ C ∗ D ∗ (out ↦ₛ res) ∗ R)) := by
    ac_rfl
  rw [e2, sat_pure_sep]
  exact ⟨hp, h⟩

end X25519Dalek.EMulB
end

section
/-! # Block 13 outside the loops (generated by tools/gen_main.py B) -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

set_option maxHeartbeats 4000000 in
theorem mainB {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s0 : State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s0.mem) {S table out v26 v27 v28 : BitVec 64}
    {T D A E C N : List (BitVec 8)} {F : SepProp} {Q : State → Prop}
    {V0 : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    (hrun : s0.status = .Running) (hal : (S &&& 15#64) = 0#64)
    (h19 : s0.regs.regs 19#5 = out) (h20 : s0.regs.regs 20#5 = table) (h21 : s0.regs.regs 21#5 = S + 232#64)
    (h22 : s0.regs.regs 22#5 = S) (h23 : s0.regs.regs 23#5 = BitVec.ofNat 64 64)
    (h24 : s0.regs.regs 24#5 = S + 392#64) (h25 : s0.regs.regs 25#5 = 960#64) (h26 : s0.regs.regs 26#5 = v26)
    (h27 : s0.regs.regs 27#5 = v27) (h28 : s0.regs.regs 28#5 = v28) (h29 : s0.regs.regs 29#5 = S + 672#64)
    (hv0 : VRegFile.calleeSaved ⟨s0.vregs.regs⟩ = V0)
    (hA : fe51Point4Bounded A (2 ^ 52)) (hC : C.length = 160)
    (hm : s0.mem ⊨ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 232#64) ↦ₛ E) ∗ ((S + 392#64) ↦ₛ C) ∗ ((S + 552#64) ↦ₛ N) ∗ memRegion (S - 912#64) 912 ∗ F)
    (hcont : ∀ (sb : State) (r : BitVec 5 → BitVec 64) (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128)
      (A' : List (BitVec 8)), sb.status = .Running → s0.mem.KeepsFrozen m →
      r 19#5 = out → r 20#5 = table → r 21#5 = S + 232#64 → r 22#5 = S + 392#64 →
      r 23#5 = BitVec.ofNat 64 (2 * 0) → r 24#5 = S + 232#64 → r 25#5 = 960#64 → r 26#5 = S →
      r 27#5 = v27 → r 28#5 = v28 → r 29#5 = S + 672#64 → VRegFile.calleeSaved ⟨v⟩ = V0 →
      fe51Point4Bounded A' (2 ^ 52) → edExtOfBytes A' = edDouble4 (edExtOfBytes A) →
      (m ⊨ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A') ∗ ((S + 232#64) ↦ₛ E) ∗ ((S + 392#64) ↦ₛ A') ∗ ((S + 552#64) ↦ₛ N) ∗ memRegion (S - 912#64) 912 ∗ F) →
      Reach (bprog mpl 13) (mkS sb (mpl.base 13 + 416#64) r S ps m v) Q) :
    Reach (bprog mpl 13) (mkS s0 (mpl.base 13 + 316#64) s0.regs.regs S s0.pstate s0.mem s0.vregs.regs) Q := by
  have kf0 : s0.mem.KeepsFrozen s0.mem := Memory.KeepsFrozen.refl _
  -- 316: add x8, sp, #392
  refine y_addi_sp (d := 8#5) (by decide) (pcA _ _ _ (320#64) (by decide)) hrun (c13_316 hP hCL 13 kf0) ?_
  refine Reach.absR (fun r1 hn1 hw1 => ?_)
  have e19_1 : r1 19#5 = out := (hn1 _ (by decide)).trans h19
  have e20_1 : r1 20#5 = table := (hn1 _ (by decide)).trans h20
  have e21_1 : r1 21#5 = S + 232#64 := (hn1 _ (by decide)).trans h21
  have e22_1 : r1 22#5 = S := (hn1 _ (by decide)).trans h22
  have e23_1 : r1 23#5 = BitVec.ofNat 64 64 := (hn1 _ (by decide)).trans h23
  have e24_1 : r1 24#5 = S + 392#64 := (hn1 _ (by decide)).trans h24
  have e25_1 : r1 25#5 = 960#64 := (hn1 _ (by decide)).trans h25
  have e26_1 : r1 26#5 = v26 := (hn1 _ (by decide)).trans h26
  have e27_1 : r1 27#5 = v27 := (hn1 _ (by decide)).trans h27
  have e28_1 : r1 28#5 = v28 := (hn1 _ (by decide)).trans h28
  have e29_1 : r1 29#5 = S + 672#64 := (hn1 _ (by decide)).trans h29
  have e8_1 : r1 8#5 = S + 392#64 := (hw1.trans (addK S _ 392 (by decide)))
  clear hn1 hw1
  -- 320: add x0, sp, #64
  refine y_addi_sp (d := 0#5) (by decide) (pcA _ _ _ (324#64) (by decide)) hrun (c13_320 hP hCL 13 kf0) ?_
  refine Reach.absR (fun r2 hn2 hw2 => ?_)
  have e8_2 : r2 8#5 = S + 392#64 := (hn2 _ (by decide)).trans e8_1
  have e19_2 : r2 19#5 = out := (hn2 _ (by decide)).trans e19_1
  have e20_2 : r2 20#5 = table := (hn2 _ (by decide)).trans e20_1
  have e21_2 : r2 21#5 = S + 232#64 := (hn2 _ (by decide)).trans e21_1
  have e22_2 : r2 22#5 = S := (hn2 _ (by decide)).trans e22_1
  have e23_2 : r2 23#5 = BitVec.ofNat 64 64 := (hn2 _ (by decide)).trans e23_1
  have e24_2 : r2 24#5 = S + 392#64 := (hn2 _ (by decide)).trans e24_1
  have e25_2 : r2 25#5 = 960#64 := (hn2 _ (by decide)).trans e25_1
  have e26_2 : r2 26#5 = v26 := (hn2 _ (by decide)).trans e26_1
  have e27_2 : r2 27#5 = v27 := (hn2 _ (by decide)).trans e27_1
  have e28_2 : r2 28#5 = v28 := (hn2 _ (by decide)).trans e28_1
  have e29_2 : r2 29#5 = S + 672#64 := (hn2 _ (by decide)).trans e29_1
  have e0_2 : r2 0#5 = S + 64#64 := (hw2.trans (addK S _ 64 (by decide)))
  clear hn2 hw2
  -- 324: movz w1
  refine y_movz32 (d := 1#5) (by decide) (pcA _ _ _ (328#64) (by decide)) hrun (c13_324 hP hCL 13 kf0) ?_
  refine Reach.absR (fun r3 hn3 hw3 => ?_)
  have e0_3 : r3 0#5 = S + 64#64 := (hn3 _ (by decide)).trans e0_2
  have e8_3 : r3 8#5 = S + 392#64 := (hn3 _ (by decide)).trans e8_2
  have e19_3 : r3 19#5 = out := (hn3 _ (by decide)).trans e19_2
  have e20_3 : r3 20#5 = table := (hn3 _ (by decide)).trans e20_2
  have e21_3 : r3 21#5 = S + 232#64 := (hn3 _ (by decide)).trans e21_2
  have e22_3 : r3 22#5 = S := (hn3 _ (by decide)).trans e22_2
  have e23_3 : r3 23#5 = BitVec.ofNat 64 64 := (hn3 _ (by decide)).trans e23_2
  have e24_3 : r3 24#5 = S + 392#64 := (hn3 _ (by decide)).trans e24_2
  have e25_3 : r3 25#5 = 960#64 := (hn3 _ (by decide)).trans e25_2
  have e26_3 : r3 26#5 = v26 := (hn3 _ (by decide)).trans e26_2
  have e27_3 : r3 27#5 = v27 := (hn3 _ (by decide)).trans e27_2
  have e28_3 : r3 28#5 = v28 := (hn3 _ (by decide)).trans e28_2
  have e29_3 : r3 29#5 = S + 672#64 := (hn3 _ (by decide)).trans e29_2
  have e1_3 : r3 1#5 = ((((0x0004#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) := hw3
  clear hn3 hw3
  -- 328: add x22, sp, #392
  refine y_addi_sp (d := 22#5) (by decide) (pcA _ _ _ (332#64) (by decide)) hrun (c13_328 hP hCL 13 kf0) ?_
  refine Reach.absR (fun r4 hn4 hw4 => ?_)
  have e0_4 : r4 0#5 = S + 64#64 := (hn4 _ (by decide)).trans e0_3
  have e1_4 : r4 1#5 = ((((0x0004#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) := (hn4 _ (by decide)).trans e1_3
  have e8_4 : r4 8#5 = S + 392#64 := (hn4 _ (by decide)).trans e8_3
  have e19_4 : r4 19#5 = out := (hn4 _ (by decide)).trans e19_3
  have e20_4 : r4 20#5 = table := (hn4 _ (by decide)).trans e20_3
  have e21_4 : r4 21#5 = S + 232#64 := (hn4 _ (by decide)).trans e21_3
  have e23_4 : r4 23#5 = BitVec.ofNat 64 64 := (hn4 _ (by decide)).trans e23_3
  have e24_4 : r4 24#5 = S + 392#64 := (hn4 _ (by decide)).trans e24_3
  have e25_4 : r4 25#5 = 960#64 := (hn4 _ (by decide)).trans e25_3
  have e26_4 : r4 26#5 = v26 := (hn4 _ (by decide)).trans e26_3
  have e27_4 : r4 27#5 = v27 := (hn4 _ (by decide)).trans e27_3
  have e28_4 : r4 28#5 = v28 := (hn4 _ (by decide)).trans e28_3
  have e29_4 : r4 29#5 = S + 672#64 := (hn4 _ (by decide)).trans e29_3
  have e22_4 : r4 22#5 = S + 392#64 := (hw4.trans (addK S _ 392 (by decide)))
  clear hn4 hw4
  -- 332: bl
  refine y_bl (add_sub_cancel' _ _) (pcA _ _ _ (336#64) (by decide)) hrun (c13_332 hP hCL 13 kf0 lk_p2) ?_
  refine Reach.absR (fun r5 hn5 hw5 => ?_)
  have e0_5 : r5 0#5 = S + 64#64 := (hn5 _ (by decide)).trans e0_4
  have e1_5 : r5 1#5 = ((((0x0004#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) := (hn5 _ (by decide)).trans e1_4
  have e8_5 : r5 8#5 = S + 392#64 := (hn5 _ (by decide)).trans e8_4
  have e19_5 : r5 19#5 = out := (hn5 _ (by decide)).trans e19_4
  have e20_5 : r5 20#5 = table := (hn5 _ (by decide)).trans e20_4
  have e21_5 : r5 21#5 = S + 232#64 := (hn5 _ (by decide)).trans e21_4
  have e22_5 : r5 22#5 = S + 392#64 := (hn5 _ (by decide)).trans e22_4
  have e23_5 : r5 23#5 = BitVec.ofNat 64 64 := (hn5 _ (by decide)).trans e23_4
  have e24_5 : r5 24#5 = S + 392#64 := (hn5 _ (by decide)).trans e24_4
  have e25_5 : r5 25#5 = 960#64 := (hn5 _ (by decide)).trans e25_4
  have e26_5 : r5 26#5 = v26 := (hn5 _ (by decide)).trans e26_4
  have e27_5 : r5 27#5 = v27 := (hn5 _ (by decide)).trans e27_4
  have e28_5 : r5 28#5 = v28 := (hn5 _ (by decide)).trans e28_4
  have e29_5 : r5 29#5 = S + 672#64 := (hn5 _ (by decide)).trans e29_4
  have e30_5 : r5 30#5 = mpl.base 13 + 336#64 := hw5
  clear hn5 hw5
  refine call_p2 hP rfl hrun hal (libCodeLoaded_keepsFrozen hCL kf0) e8_5 e0_5 (by rw [e1_5]; decide) hC (fe51Point4Bounded_mono (by norm_num) hA) (Satisfies.of_eq hm (Q := ((S + 64#64) ↦ₛ A) ∗ ((S + 392#64) ↦ₛ C) ∗ memRegion (S - 912#64) 912 ∗ ((table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 232#64) ↦ₛ E) ∗ ((S + 552#64) ↦ₛ N) ∗ F))) ?_
  intro sf1 Rs hrun1 hsp1 hcs1 hv1 hm1 hkf1 hRb hRv
  rw [e30_5]
  have e19_c1 : sf1.regs.regs 19#5 = out := (hcs1.1).trans e19_5
  have e20_c1 : sf1.regs.regs 20#5 = table := (hcs1.2.1).trans e20_5
  have e21_c1 : sf1.regs.regs 21#5 = S + 232#64 := (hcs1.2.2.1).trans e21_5
  have e22_c1 : sf1.regs.regs 22#5 = S + 392#64 := (hcs1.2.2.2.1).trans e22_5
  have e23_c1 : sf1.regs.regs 23#5 = BitVec.ofNat 64 64 := (hcs1.2.2.2.2.1).trans e23_5
  have e24_c1 : sf1.regs.regs 24#5 = S + 392#64 := (hcs1.2.2.2.2.2.1).trans e24_5
  have e25_c1 : sf1.regs.regs 25#5 = 960#64 := (hcs1.2.2.2.2.2.2.1).trans e25_5
  have e26_c1 : sf1.regs.regs 26#5 = v26 := (hcs1.2.2.2.2.2.2.2.1).trans e26_5
  have e27_c1 : sf1.regs.regs 27#5 = v27 := (hcs1.2.2.2.2.2.2.2.2.1).trans e27_5
  have e28_c1 : sf1.regs.regs 28#5 = v28 := (hcs1.2.2.2.2.2.2.2.2.2.1).trans e28_5
  have e29_c1 : sf1.regs.regs 29#5 = S + 672#64 := (hcs1.2.2.2.2.2.2.2.2.2.2).trans e29_5
  have kfc1 : s0.mem.KeepsFrozen sf1.mem := kf0.trans hkf1
  have hvc1 : VRegFile.calleeSaved ⟨sf1.vregs.regs⟩ = V0 := hv1.trans hv0
  clear hcs1 hkf1 hv1
  have hRl : Rs.length = 160 := hRb.1
  rw [show ((S + 392#64) ↦ₛ Rs) = ((S + 392#64) ↦₆₄* chunks64 Rs 20) by rw [words_eq_bytes, chunks64_flat 20 Rs (by rw [hRl])], show ((S + 64#64) ↦ₛ A) = ((S + 64#64) ↦₆₄* chunks64 A 20) by rw [words_eq_bytes, chunks64_flat 20 A (by rw [hA.1])]] at hm1
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, hx⟩ := list20 (chunks64 Rs 20) (chunks64_length _ _)
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, ha⟩ := list20 (chunks64 A 20) (chunks64_length _ _)
  rw [hx, ha] at hm1
  have hmC : sf1.mem ⊨ ((S + 392#64) ↦₆₄* [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19]) ∗ ((S + 64#64) ↦₆₄* [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19]) ∗ (memRegion (S - 912#64) 912 ∗ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 232#64) ↦ₛ E) ∗ ((S + 552#64) ↦ₛ N) ∗ F) := Satisfies.of_eq hm1
  clear hm1
  refine x_ldpq_w (t1 := 0#5) (t2 := 1#5) (k := 12) (lo1 := x12) (hi1 := x13) (lo2 := x14) (hi2 := x15) (by decide) hrun1 (c13_336 hP hCL 13 kfc1) (pcA _ _ _ (340#64) (by decide)) e21_c1 ((aadd S 232 256 488 rfl).trans (aadd S 392 (8 * 12) 488 rfl).symm) hmC (by simp) rfl rfl rfl rfl ?_
  have hvq6 := cs_upd (i := 1#5) (x := x15 ++ x14) (by decide) (cs_upd (i := 0#5) (x := x13 ++ x12) (by decide) hvc1)
  -- 340: mov x23, xzr
  refine y_movzr (d := 23#5) (by decide) (pcA _ _ _ (344#64) (by decide)) hrun1 (c13_340 hP hCL 13 kfc1) ?_
  refine Reach.absR (fun r7 hn7 hw7 => ?_)
  have e19_7 : r7 19#5 = out := (hn7 _ (by decide)).trans e19_c1
  have e20_7 : r7 20#5 = table := (hn7 _ (by decide)).trans e20_c1
  have e21_7 : r7 21#5 = S + 232#64 := (hn7 _ (by decide)).trans e21_c1
  have e22_7 : r7 22#5 = S + 392#64 := (hn7 _ (by decide)).trans e22_c1
  have e24_7 : r7 24#5 = S + 392#64 := (hn7 _ (by decide)).trans e24_c1
  have e25_7 : r7 25#5 = 960#64 := (hn7 _ (by decide)).trans e25_c1
  have e26_7 : r7 26#5 = v26 := (hn7 _ (by decide)).trans e26_c1
  have e27_7 : r7 27#5 = v27 := (hn7 _ (by decide)).trans e27_c1
  have e28_7 : r7 28#5 = v28 := (hn7 _ (by decide)).trans e28_c1
  have e29_7 : r7 29#5 = S + 672#64 := (hn7 _ (by decide)).trans e29_c1
  have e23_7 : r7 23#5 = BitVec.ofNat 64 (2 * 0) := hw7
  clear hn7 hw7
  -- 344: add x24, sp, #232
  refine y_addi_sp (d := 24#5) (by decide) (pcA _ _ _ (348#64) (by decide)) hrun1 (c13_344 hP hCL 13 kfc1) ?_
  refine Reach.absR (fun r8 hn8 hw8 => ?_)
  have e19_8 : r8 19#5 = out := (hn8 _ (by decide)).trans e19_7
  have e20_8 : r8 20#5 = table := (hn8 _ (by decide)).trans e20_7
  have e21_8 : r8 21#5 = S + 232#64 := (hn8 _ (by decide)).trans e21_7
  have e22_8 : r8 22#5 = S + 392#64 := (hn8 _ (by decide)).trans e22_7
  have e23_8 : r8 23#5 = BitVec.ofNat 64 (2 * 0) := (hn8 _ (by decide)).trans e23_7
  have e25_8 : r8 25#5 = 960#64 := (hn8 _ (by decide)).trans e25_7
  have e26_8 : r8 26#5 = v26 := (hn8 _ (by decide)).trans e26_7
  have e27_8 : r8 27#5 = v27 := (hn8 _ (by decide)).trans e27_7
  have e28_8 : r8 28#5 = v28 := (hn8 _ (by decide)).trans e28_7
  have e29_8 : r8 29#5 = S + 672#64 := (hn8 _ (by decide)).trans e29_7
  have e24_8 : r8 24#5 = S + 232#64 := (hw8.trans (addK S _ 232 (by decide)))
  clear hn8 hw8
  -- 348: movz w25
  refine y_movz32 (d := 25#5) (by decide) (pcA _ _ _ (352#64) (by decide)) hrun1 (c13_348 hP hCL 13 kfc1) ?_
  refine Reach.absR (fun r9 hn9 hw9 => ?_)
  have e19_9 : r9 19#5 = out := (hn9 _ (by decide)).trans e19_8
  have e20_9 : r9 20#5 = table := (hn9 _ (by decide)).trans e20_8
  have e21_9 : r9 21#5 = S + 232#64 := (hn9 _ (by decide)).trans e21_8
  have e22_9 : r9 22#5 = S + 392#64 := (hn9 _ (by decide)).trans e22_8
  have e23_9 : r9 23#5 = BitVec.ofNat 64 (2 * 0) := (hn9 _ (by decide)).trans e23_8
  have e24_9 : r9 24#5 = S + 232#64 := (hn9 _ (by decide)).trans e24_8
  have e26_9 : r9 26#5 = v26 := (hn9 _ (by decide)).trans e26_8
  have e27_9 : r9 27#5 = v27 := (hn9 _ (by decide)).trans e27_8
  have e28_9 : r9 28#5 = v28 := (hn9 _ (by decide)).trans e28_8
  have e29_9 : r9 29#5 = S + 672#64 := (hn9 _ (by decide)).trans e29_8
  have e25_9 : r9 25#5 = 960#64 := (by rw [hw9]; rfl)
  clear hn9 hw9
  -- 352: add x26, sp, #0
  refine y_addi_sp (d := 26#5) (by decide) (pcA _ _ _ (356#64) (by decide)) hrun1 (c13_352 hP hCL 13 kfc1) ?_
  refine Reach.absR (fun r10 hn10 hw10 => ?_)
  have e19_10 : r10 19#5 = out := (hn10 _ (by decide)).trans e19_9
  have e20_10 : r10 20#5 = table := (hn10 _ (by decide)).trans e20_9
  have e21_10 : r10 21#5 = S + 232#64 := (hn10 _ (by decide)).trans e21_9
  have e22_10 : r10 22#5 = S + 392#64 := (hn10 _ (by decide)).trans e22_9
  have e23_10 : r10 23#5 = BitVec.ofNat 64 (2 * 0) := (hn10 _ (by decide)).trans e23_9
  have e24_10 : r10 24#5 = S + 232#64 := (hn10 _ (by decide)).trans e24_9
  have e25_10 : r10 25#5 = 960#64 := (hn10 _ (by decide)).trans e25_9
  have e27_10 : r10 27#5 = v27 := (hn10 _ (by decide)).trans e27_9
  have e28_10 : r10 28#5 = v28 := (hn10 _ (by decide)).trans e28_9
  have e29_10 : r10 29#5 = S + 672#64 := (hn10 _ (by decide)).trans e29_9
  have e26_10 : r10 26#5 = S := (hw10.trans (addK0 _))
  clear hn10 hw10
  refine x_stpq_w2 (k := 12) (lo1 := x12) (hi1 := x13) (lo2 := x14) (hi2 := x15) hal hrun1 (c13_356 hP hCL 13 kfc1) (pcA _ _ _ (360#64) (by decide)) (aadd S 64 (8 * 12) 160 rfl).symm hmC (by simp) (by simp) (by simp) ?_
  intro mw356 hmw356 kw356
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw356
  have kfw356 := kfc1.trans kw356
  clear hmC kw356
  refine x_ldpq_w (t1 := 0#5) (t2 := 2#5) (k := 16) (lo1 := x16) (hi1 := x17) (lo2 := x18) (hi2 := x19) (by decide) hrun1 (c13_360 hP hCL 13 kfw356) (pcA _ _ _ (364#64) (by decide)) e21_10 ((aadd S 232 288 520 rfl).trans (aadd S 392 (8 * 16) 520 rfl).symm) hmw356 (by simp) rfl rfl rfl rfl ?_
  have hvq11 := cs_upd (i := 2#5) (x := x19 ++ x18) (by decide) (cs_upd (i := 0#5) (x := x17 ++ x16) (by decide) hvq6)
  refine x_stpq_w2 (k := 16) (lo1 := x16) (hi1 := x17) (lo2 := x18) (hi2 := x19) hal hrun1 (c13_364 hP hCL 13 kfw356) (pcA _ _ _ (368#64) (by decide)) (aadd S 64 (8 * 16) 192 rfl).symm hmw356 (by simp) (by simp) (by simp) ?_
  intro mw364 hmw364 kw364
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw364
  have kfw364 := kfw356.trans kw364
  clear hmw356 kw364
  refine x_ldpq_w (t1 := 1#5) (t2 := 0#5) (k := 4) (lo1 := x4) (hi1 := x5) (lo2 := x6) (hi2 := x7) (by decide) hrun1 (c13_368 hP hCL 13 kfw364) (pcA _ _ _ (372#64) (by decide)) e21_10 ((aadd S 232 192 424 rfl).trans (aadd S 392 (8 * 4) 424 rfl).symm) hmw364 (by simp) rfl rfl rfl rfl ?_
  have hvq12 := cs_upd (i := 0#5) (x := x7 ++ x6) (by decide) (cs_upd (i := 1#5) (x := x5 ++ x4) (by decide) hvq11)
  refine x_stpq_w2 (k := 4) (lo1 := x4) (hi1 := x5) (lo2 := x6) (hi2 := x7) hal hrun1 (c13_372 hP hCL 13 kfw364) (pcA _ _ _ (376#64) (by decide)) (aadd S 64 (8 * 4) 96 rfl).symm hmw364 (by simp) (by simp) (by simp) ?_
  intro mw372 hmw372 kw372
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw372
  have kfw372 := kfw364.trans kw372
  clear hmw364 kw372
  refine x_ldpq_w (t1 := 2#5) (t2 := 0#5) (k := 8) (lo1 := x8) (hi1 := x9) (lo2 := x10) (hi2 := x11) (by decide) hrun1 (c13_376 hP hCL 13 kfw372) (pcA _ _ _ (380#64) (by decide)) e21_10 ((aadd S 232 224 456 rfl).trans (aadd S 392 (8 * 8) 456 rfl).symm) hmw372 (by simp) rfl rfl rfl rfl ?_
  have hvq13 := cs_upd (i := 0#5) (x := x11 ++ x10) (by decide) (cs_upd (i := 2#5) (x := x9 ++ x8) (by decide) hvq12)
  refine x_stpq_w2 (k := 8) (lo1 := x8) (hi1 := x9) (lo2 := x10) (hi2 := x11) hal hrun1 (c13_380 hP hCL 13 kfw372) (pcA _ _ _ (384#64) (by decide)) (aadd S 64 (8 * 8) 128 rfl).symm hmw372 (by simp) (by simp) (by simp) ?_
  intro mw380 hmw380 kw380
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw380
  have kfw380 := kfw372.trans kw380
  clear hmw372 kw380
  refine x_ldpq_w (t1 := 1#5) (t2 := 0#5) (k := 0) (lo1 := x0) (hi1 := x1) (lo2 := x2) (hi2 := x3) (by decide) hrun1 (c13_384 hP hCL 13 kfw380) (pcA _ _ _ (388#64) (by decide)) e21_10 ((aadd S 232 160 392 rfl).trans (aadd S 392 (8 * 0) 392 rfl).symm) hmw380 (by simp) rfl rfl rfl rfl ?_
  have hvq14 := cs_upd (i := 0#5) (x := x3 ++ x2) (by decide) (cs_upd (i := 1#5) (x := x1 ++ x0) (by decide) hvq13)
  refine x_stpq_w2 (k := 0) (lo1 := x0) (hi1 := x1) (lo2 := x2) (hi2 := x3) hal hrun1 (c13_388 hP hCL 13 kfw380) (pcA _ _ _ (392#64) (by decide)) (aadd S 64 (8 * 0) 64 rfl).symm hmw380 (by simp) (by simp) (by simp) ?_
  intro mw388 hmw388 kw388
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw388
  have kfw388 := kfw380.trans kw388
  clear hmw380 kw388
  -- 392: cmp x23, #64; 396: b.ne 416
  refine y_cmpi (n := 23#5) (by decide) (pcA _ _ _ (396#64) (by decide)) hrun1 (c13_392 hP hCL 13 kfw388) ?_
  refine y_bcond_t (by rw [e23_10]; decide) (pcA _ _ _ (416#64) (by decide)) hrun1 (c13_396 hP hCL 13 kfw388) ?_
  rw [← hx] at hmw388
  rw [words_eq_bytes, words_eq_bytes, chunks64_flat 20 Rs (by rw [hRl])] at hmw388
  exact hcont _ _ _ _ _ Rs hrun1 kfw388 e19_10 e20_10 e21_10 e22_10 e23_10 e24_10 e25_10 e26_10 e27_10 e28_10 e29_10 hvq14 hRb hRv (Satisfies.of_eq hmw388)

end X25519Dalek.EMulB
end

section
/-! # Block 13 outside the loops (generated by tools/gen_main.py C) -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

set_option maxHeartbeats 4000000 in
theorem mainC {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s0 : State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s0.mem) {S table out v27 : BitVec 64}
    {A O : List (BitVec 8)} {u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 : BitVec 64} {G : SepProp} {Q : State → Prop}
    {V0 : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    (hrun : s0.status = .Running) (hal : (S &&& 15#64) = 0#64)
    (h19 : s0.regs.regs 19#5 = out) (h21 : s0.regs.regs 21#5 = S + 232#64) (h27 : s0.regs.regs 27#5 = v27)
    (hv0 : VRegFile.calleeSaved ⟨s0.vregs.regs⟩ = V0)
    (hA : A.length = 160) (hO : O.length = 160)
    (hm : s0.mem ⊨ ((S + 64#64) ↦ₛ A) ∗ (out ↦ₛ O) ∗ ((S + 672#64) ↦₆₄* [u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11]) ∗ G)
    (hcont : ∀ (sb : State) (r : BitVec 5 → BitVec 64) (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128),
      sb.status = .Running → s0.mem.KeepsFrozen m →
      r 19#5 = u11 → r 20#5 = u10 → r 21#5 = u9 → r 22#5 = u8 → r 23#5 = u7 → r 24#5 = u6 → r 25#5 = u5 →
      r 26#5 = u4 → r 27#5 = v27 → r 28#5 = u2 → r 29#5 = u0 → r 30#5 = u1 →
      VRegFile.calleeSaved ⟨v⟩ = V0 →
      (m ⊨ ((S + 64#64) ↦ₛ A) ∗ (out ↦ₛ A) ∗ ((S + 672#64) ↦₆₄* [u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11]) ∗ G) →
      Q (mkS sb u1 r (S + 768#64) ps m v)) :
    Reach (bprog mpl 13) (mkS s0 (mpl.base 13 + 580#64) s0.regs.regs S s0.pstate s0.mem s0.vregs.regs) Q := by
  have kf0 : s0.mem.KeepsFrozen s0.mem := Memory.KeepsFrozen.refl _
  rw [show ((S + 64#64) ↦ₛ A) = ((S + 64#64) ↦₆₄* chunks64 A 20) by rw [words_eq_bytes, chunks64_flat 20 A (by rw [hA])],
    show (out ↦ₛ O) = (out ↦₆₄* chunks64 O 20) by rw [words_eq_bytes, chunks64_flat 20 O (by rw [hO])]] at hm
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, hx⟩ := list20 (chunks64 A 20) (chunks64_length _ _)
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, ho⟩ := list20 (chunks64 O 20) (chunks64_length _ _)
  rw [hx, ho] at hm
  refine x_ldpq_spw (t1 := 0#5) (t2 := 1#5) (k := 12) (lo1 := x12) (hi1 := x13) (lo2 := x14) (hi2 := x15) hal hrun (c13_580 hP hCL 13 kf0) (pcA _ _ _ (584#64) (by decide)) (aadd S 64 (8 * 12) 160 rfl).symm hm (by simp) rfl rfl rfl rfl ?_
  have hvq1 := cs_upd (i := 1#5) (x := x15 ++ x14) (by decide) (cs_upd (i := 0#5) (x := x13 ++ x12) (by decide) hv0)
  refine x_stpq_ow2 (k := 12) (lo1 := x12) (hi1 := x13) (lo2 := x14) (hi2 := x15) (by decide) hrun (c13_584 hP hCL 13 kf0) (pcA _ _ _ (588#64) (by decide)) h19 rfl hm (by simp) (by simp) (by simp) ?_
  intro mw584 hmw584 kw584
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw584
  have kfw584 := kf0.trans kw584
  clear hm kw584
  refine x_ldpq_spw (t1 := 0#5) (t2 := 2#5) (k := 16) (lo1 := x16) (hi1 := x17) (lo2 := x18) (hi2 := x19) hal hrun (c13_588 hP hCL 13 kfw584) (pcA _ _ _ (592#64) (by decide)) (aadd S 64 (8 * 16) 192 rfl).symm hmw584 (by simp) rfl rfl rfl rfl ?_
  have hvq2 := cs_upd (i := 2#5) (x := x19 ++ x18) (by decide) (cs_upd (i := 0#5) (x := x17 ++ x16) (by decide) hvq1)
  refine x_stpq_ow2 (k := 16) (lo1 := x16) (hi1 := x17) (lo2 := x18) (hi2 := x19) (by decide) hrun (c13_592 hP hCL 13 kfw584) (pcA _ _ _ (596#64) (by decide)) h19 rfl hmw584 (by simp) (by simp) (by simp) ?_
  intro mw592 hmw592 kw592
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw592
  have kfw592 := kfw584.trans kw592
  clear hmw584 kw592
  refine x_ldpq_spw (t1 := 1#5) (t2 := 0#5) (k := 4) (lo1 := x4) (hi1 := x5) (lo2 := x6) (hi2 := x7) hal hrun (c13_596 hP hCL 13 kfw592) (pcA _ _ _ (600#64) (by decide)) (aadd S 64 (8 * 4) 96 rfl).symm hmw592 (by simp) rfl rfl rfl rfl ?_
  have hvq3 := cs_upd (i := 0#5) (x := x7 ++ x6) (by decide) (cs_upd (i := 1#5) (x := x5 ++ x4) (by decide) hvq2)
  refine x_stpq_ow2 (k := 4) (lo1 := x4) (hi1 := x5) (lo2 := x6) (hi2 := x7) (by decide) hrun (c13_600 hP hCL 13 kfw592) (pcA _ _ _ (604#64) (by decide)) h19 rfl hmw592 (by simp) (by simp) (by simp) ?_
  intro mw600 hmw600 kw600
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw600
  have kfw600 := kfw592.trans kw600
  clear hmw592 kw600
  refine x_ldpq_spw (t1 := 2#5) (t2 := 0#5) (k := 8) (lo1 := x8) (hi1 := x9) (lo2 := x10) (hi2 := x11) hal hrun (c13_604 hP hCL 13 kfw600) (pcA _ _ _ (608#64) (by decide)) (aadd S 64 (8 * 8) 128 rfl).symm hmw600 (by simp) rfl rfl rfl rfl ?_
  have hvq4 := cs_upd (i := 0#5) (x := x11 ++ x10) (by decide) (cs_upd (i := 2#5) (x := x9 ++ x8) (by decide) hvq3)
  refine x_stpq_ow2 (k := 8) (lo1 := x8) (hi1 := x9) (lo2 := x10) (hi2 := x11) (by decide) hrun (c13_608 hP hCL 13 kfw600) (pcA _ _ _ (612#64) (by decide)) h19 rfl hmw600 (by simp) (by simp) (by simp) ?_
  intro mw608 hmw608 kw608
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw608
  have kfw608 := kfw600.trans kw608
  clear hmw600 kw608
  refine x_ldpq_spw (t1 := 1#5) (t2 := 0#5) (k := 0) (lo1 := x0) (hi1 := x1) (lo2 := x2) (hi2 := x3) hal hrun (c13_612 hP hCL 13 kfw608) (pcA _ _ _ (616#64) (by decide)) (aadd S 64 (8 * 0) 64 rfl).symm hmw608 (by simp) rfl rfl rfl rfl ?_
  have hvq5 := cs_upd (i := 0#5) (x := x3 ++ x2) (by decide) (cs_upd (i := 1#5) (x := x1 ++ x0) (by decide) hvq4)
  refine x_stpq_ow2 (k := 0) (lo1 := x0) (hi1 := x1) (lo2 := x2) (hi2 := x3) (by decide) hrun (c13_616 hP hCL 13 kfw608) (pcA _ _ _ (620#64) (by decide)) h19 rfl hmw608 (by simp) (by simp) (by simp) ?_
  intro mw616 hmw616 kw616
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw616
  have kfw616 := kfw608.trans kw616
  clear hmw608 kw616
  rw [← hx] at hmw616
  rw [words_eq_bytes, words_eq_bytes, chunks64_flat 20 A (by rw [hA])] at hmw616
  have hmS : mw616 ⊨ ((S + 672#64) ↦₆₄* [u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11]) ∗ (((S + 64#64) ↦ₛ A) ∗ (out ↦ₛ A) ∗ G) := Satisfies.of_eq hmw616
  -- 620: add sp, sp, #672
  refine y_addsp (pcA _ _ _ (624#64) (by decide)) hrun (c13_620 hP hCL 13 kfw616) ?_
  rw [addK S _ 672 (by decide)]
  have hal672 : ((S + 672#64) &&& 15#64) = 0#64 := aligned_add (by simp [hal]) 672 (by decide)
  -- 624: ldp x20, x19, [sp, #80]
  refine x_ldp_w (d1 := 20#5) (d2 := 19#5) (k := 10) (by decide) (by decide) hal672 hrun (c13_624 hP hCL 13 kfw616) (pcA _ _ _ (628#64) (by decide)) rfl hmS (by simp) rfl rfl ?_
  refine Reach.absR2 (by decide) (fun r6 hn6 hw6 hx6 => ?_)
  have e21_6 : r6 21#5 = S + 232#64 := (hn6 _ (by decide) (by decide)).trans h21
  have e27_6 : r6 27#5 = v27 := (hn6 _ (by decide) (by decide)).trans h27
  have e20_6 : r6 20#5 = u10 := hw6
  have e19_6 : r6 19#5 = u11 := hx6
  clear hn6 hw6 hx6
  -- 628: ldr x28, [sp, #16]
  refine x_ldr_w (d := 28#5) (k := 2) (by decide) hal672 hrun (c13_628 hP hCL 13 kfw616) (pcA _ _ _ (632#64) (by decide)) rfl hmS (by simp) rfl ?_
  refine Reach.absR (fun r7 hn7 hw7 => ?_)
  have e19_7 : r7 19#5 = u11 := (hn7 _ (by decide)).trans e19_6
  have e20_7 : r7 20#5 = u10 := (hn7 _ (by decide)).trans e20_6
  have e21_7 : r7 21#5 = S + 232#64 := (hn7 _ (by decide)).trans e21_6
  have e27_7 : r7 27#5 = v27 := (hn7 _ (by decide)).trans e27_6
  have e28_7 : r7 28#5 = u2 := hw7
  clear hn7 hw7
  -- 632: ldp x22, x21, [sp, #64]
  refine x_ldp_w (d1 := 22#5) (d2 := 21#5) (k := 8) (by decide) (by decide) hal672 hrun (c13_632 hP hCL 13 kfw616) (pcA _ _ _ (636#64) (by decide)) rfl hmS (by simp) rfl rfl ?_
  refine Reach.absR2 (by decide) (fun r8 hn8 hw8 hx8 => ?_)
  have e19_8 : r8 19#5 = u11 := (hn8 _ (by decide) (by decide)).trans e19_7
  have e20_8 : r8 20#5 = u10 := (hn8 _ (by decide) (by decide)).trans e20_7
  have e27_8 : r8 27#5 = v27 := (hn8 _ (by decide) (by decide)).trans e27_7
  have e28_8 : r8 28#5 = u2 := (hn8 _ (by decide) (by decide)).trans e28_7
  have e22_8 : r8 22#5 = u8 := hw8
  have e21_8 : r8 21#5 = u9 := hx8
  clear hn8 hw8 hx8
  -- 636: ldp x24, x23, [sp, #48]
  refine x_ldp_w (d1 := 24#5) (d2 := 23#5) (k := 6) (by decide) (by decide) hal672 hrun (c13_636 hP hCL 13 kfw616) (pcA _ _ _ (640#64) (by decide)) rfl hmS (by simp) rfl rfl ?_
  refine Reach.absR2 (by decide) (fun r9 hn9 hw9 hx9 => ?_)
  have e19_9 : r9 19#5 = u11 := (hn9 _ (by decide) (by decide)).trans e19_8
  have e20_9 : r9 20#5 = u10 := (hn9 _ (by decide) (by decide)).trans e20_8
  have e21_9 : r9 21#5 = u9 := (hn9 _ (by decide) (by decide)).trans e21_8
  have e22_9 : r9 22#5 = u8 := (hn9 _ (by decide) (by decide)).trans e22_8
  have e27_9 : r9 27#5 = v27 := (hn9 _ (by decide) (by decide)).trans e27_8
  have e28_9 : r9 28#5 = u2 := (hn9 _ (by decide) (by decide)).trans e28_8
  have e24_9 : r9 24#5 = u6 := hw9
  have e23_9 : r9 23#5 = u7 := hx9
  clear hn9 hw9 hx9
  -- 640: ldp x26, x25, [sp, #32]
  refine x_ldp_w (d1 := 26#5) (d2 := 25#5) (k := 4) (by decide) (by decide) hal672 hrun (c13_640 hP hCL 13 kfw616) (pcA _ _ _ (644#64) (by decide)) rfl hmS (by simp) rfl rfl ?_
  refine Reach.absR2 (by decide) (fun r10 hn10 hw10 hx10 => ?_)
  have e19_10 : r10 19#5 = u11 := (hn10 _ (by decide) (by decide)).trans e19_9
  have e20_10 : r10 20#5 = u10 := (hn10 _ (by decide) (by decide)).trans e20_9
  have e21_10 : r10 21#5 = u9 := (hn10 _ (by decide) (by decide)).trans e21_9
  have e22_10 : r10 22#5 = u8 := (hn10 _ (by decide) (by decide)).trans e22_9
  have e23_10 : r10 23#5 = u7 := (hn10 _ (by decide) (by decide)).trans e23_9
  have e24_10 : r10 24#5 = u6 := (hn10 _ (by decide) (by decide)).trans e24_9
  have e27_10 : r10 27#5 = v27 := (hn10 _ (by decide) (by decide)).trans e27_9
  have e28_10 : r10 28#5 = u2 := (hn10 _ (by decide) (by decide)).trans e28_9
  have e26_10 : r10 26#5 = u4 := hw10
  have e25_10 : r10 25#5 = u5 := hx10
  clear hn10 hw10 hx10
  -- 644: ldp x29, x30, [sp], #96
  refine x_ldp_post_w (d1 := 29#5) (d2 := 30#5) (k := 0) (by decide) (by decide) hal672 hrun (c13_644 hP hCL 13 kfw616) (pcA _ _ _ (648#64) (by decide)) (aoff0 _) hmS (by simp) rfl rfl ?_
  refine Reach.absR2 (by decide) (fun r11 hn11 hw11 hx11 => ?_)
  have e19_11 : r11 19#5 = u11 := (hn11 _ (by decide) (by decide)).trans e19_10
  have e20_11 : r11 20#5 = u10 := (hn11 _ (by decide) (by decide)).trans e20_10
  have e21_11 : r11 21#5 = u9 := (hn11 _ (by decide) (by decide)).trans e21_10
  have e22_11 : r11 22#5 = u8 := (hn11 _ (by decide) (by decide)).trans e22_10
  have e23_11 : r11 23#5 = u7 := (hn11 _ (by decide) (by decide)).trans e23_10
  have e24_11 : r11 24#5 = u6 := (hn11 _ (by decide) (by decide)).trans e24_10
  have e25_11 : r11 25#5 = u5 := (hn11 _ (by decide) (by decide)).trans e25_10
  have e26_11 : r11 26#5 = u4 := (hn11 _ (by decide) (by decide)).trans e26_10
  have e27_11 : r11 27#5 = v27 := (hn11 _ (by decide) (by decide)).trans e27_10
  have e28_11 : r11 28#5 = u2 := (hn11 _ (by decide) (by decide)).trans e28_10
  have e29_11 : r11 29#5 = u0 := hw11
  have e30_11 : r11 30#5 = u1 := hx11
  clear hn11 hw11 hx11
  rw [pcA S _ _ 768#64 (by decide)]
  -- 648: ret
  refine y_ret hrun (c13_648 hP hCL 13 kfw616) ?_
  rw [e30_11]
  exact Reach.done (hcont _ _ _ _ _ hrun kfw616 e19_11 e20_11 e21_11 e22_11 e23_11 e24_11 e25_11 e26_11 e27_11 e28_11 e29_11 e30_11 hvq5 (Satisfies.of_eq hmS))

end X25519Dalek.EMulB
end

section
/-! # `<EdwardsBasepointTable as BasepointTable>::mul_base` (block 13): the contract

The prologue and the identity accumulator (`mainA`), the odd loop (`odd_loop`, from the published
odd-iteration statement), `mul_by_pow_2` and the copy back (`mainB`), the even loop (`even_loop`),
the copy to `out` and the epilogue (`mainC`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

abbrev mbName : String :=
  "<curve25519_dalek::edwards::EdwardsBasepointTable as curve25519_dalek::traits::BasepointTable>::mul_base"

theorem lk_mb : lookupBlockSym mbName x25519CliMultiLib.blocks = some (13, 0) := by decide +kernel

theorem reach_eq {p : Program} {s s' : State} {Q : State → Prop} (h : s' = s) (H : Reach p s' Q) :
    Reach p s Q := by subst h; exact H

set_option maxHeartbeats 4000000 in
theorem mb_ok : fnOk mbName edwardsBasepointTableMulBaseSpec := by
  refine ⟨13, 0, lk_mb, fun mpl hP => ?_⟩
  rintro ⟨out, table, scalar, out_bs, table_bs, scalar_bs⟩ R s0 hpc hrun hpre hal hCLp
  have hfa : x25519CliMultiLib.fnAddr mpl mbName = mpl.base 13 + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.fnAddr, lk_mb]
  rw [hfa, BitVec.add_zero] at hpc
  change s0.mem ⊨ ((⌜s0.readReg64 Reg.x8 = out ∧ s0.readReg64 Reg.x0 = table ∧
      s0.readReg64 Reg.x1 = scalar ∧ out_bs.length = 160 ∧ fe51BasepointTable32Bounded table_bs (2 ^ 53) ∧
      scalar_bs.length = 32 ∧ (scalar_bs.getD 31 0#8).toNat ≤ 127⌝ ∗
      (table ↦ᵣ table_bs) ∗ (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (out ↦ₛ out_bs) ∗
      stackFrame s0 1680) ∗ ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝) ∗ R at hpre
  have h1 := Satisfies.of_eq hpre
    (Q := ⌜s0.readReg64 Reg.x8 = out ∧ s0.readReg64 Reg.x0 = table ∧
      s0.readReg64 Reg.x1 = scalar ∧ out_bs.length = 160 ∧ fe51BasepointTable32Bounded table_bs (2 ^ 53) ∧
      scalar_bs.length = 32 ∧ (scalar_bs.getD 31 0#8).toNat ≤ 127⌝ ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝ ∗ stackFrame s0 1680 ∗
      ((table ↦ᵣ table_bs) ∗ (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (out ↦ₛ out_bs) ∗ R))
  rw [sat_pure_sep, sat_pure_sep] at h1
  obtain ⟨⟨hx8, hx0, hx1, hlo, htab, hls, hl31⟩, hCL, h1⟩ := h1
  clear hpre
  have h8 : s0.regs.regs 8#5 = out := by rw [← hx8]; exact (readGpr_eq s0 8#5 (by decide)).symm
  have h0 : s0.regs.regs 0#5 = table := by rw [← hx0]; exact (readGpr_eq s0 0#5 (by decide)).symm
  have h1r : s0.regs.regs 1#5 = scalar := by rw [← hx1]; exact (readGpr_eq s0 1#5 (by decide)).symm
  have hal0 : (s0.sp &&& 15#64) = 0#64 := by simpa [State.spAligned] using hal
  generalize hSdef : s0.sp - 768#64 = S
  have hspS : s0.sp = S + 768#64 := by rw [← hSdef, BitVec.sub_add_cancel]
  have halS : (S &&& 15#64) = 0#64 := by
    rw [← hSdef]; exact aligned_sub (x := s0.sp) (by simp [hal0]) 768 (by decide) (by norm_num)
  have hfr : stackFrame s0 1680 = memRegion (S - 912#64) 1680 := by
    show memRegion _ _ = _
    rw [hspS, show (BitVec.ofNat 64 1680 : BitVec 64) = 768#64 + 912#64 from rfl, ← BitVec.sub_sub,
      BitVec.add_sub_cancel]
  rw [hfr] at h1
  obtain ⟨E0, C0, N0, hE0, hC0, hN0, h2⟩ := frame_in h1
  show Reach (bprog mpl 13) s0 _
  obtain ⟨sP, hstP, hrunP, hpcP, hspP, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, hvP, w3, A0, hmP,
    hA0, hA0v⟩ := X25519Dalek.basepointTable_mul_base_prologue hP hCL hrun hpc hspS halS h0 h1r h8 hls hl31
      (G := (table ↦ᵣ table_bs) ∗ (out ↦ₛ out_bs) ∗ ((S + 232#64) ↦ₛ E0) ∗ ((S + 392#64) ↦ₛ C0) ∗
        ((S + 552#64) ↦ₛ N0) ∗ memRegion (S + 224#64) 8 ∗ memRegion (S - 912#64) 912 ∗ R) (Satisfies.of_eq h2)
  clear h2
  refine Reach.steps hstP ?_
  have hdl := srd_length scalar_bs
  refine odd_loop hP (table := table) (T := table_bs) (D := scalarRadix16Digits scalar_bs)
    (F := (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (out ↦ₛ out_bs) ∗
      ((S + 672#64) ↦₆₄* [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 28#5, w3, s0.regs.regs 26#5,
        s0.regs.regs 25#5, s0.regs.regs 24#5, s0.regs.regs 23#5, s0.regs.regs 22#5, s0.regs.regs 21#5,
        s0.regs.regs 20#5, s0.regs.regs 19#5]) ∗ memRegion (S + 224#64) 8 ∗ R)
    (r0 := sP.regs.regs) (V0 := VRegFile.calleeSaved s0.vregs) htab hdl halS 32 0
    sP A0 E0 C0 N0 edExtZero rfl
    (libCodeLoaded_keepsFrozen hCL (X25519Dalek.steps_keepsFrozen_v2 hstP)) hrunP (hpcP.trans (if_neg (by decide)).symm)
    hspP e20 e21 e22 e24 e25 e29 e23 (KeepHi.refl _) hvP hA0 hA0v hE0 hC0 hN0 (Satisfies.of_eq hmP) ?_
  intro s1 A1 E1 C1 N1 hCL1 hrun1 hpc1 hsp1 f20 f21 f22 f24 f25 f29 f23 hkh1 hv1 hA1 hAv1 hE1 hC1 hN1 hm1
  clear hmP
  refine reach_eq (s' := mkS s1 (mpl.base 13 + 316#64) s1.regs.regs S s1.pstate s1.mem s1.vregs.regs)
    (by rw [← hpc1, ← hsp1]; rfl) ?_
  refine mainB hP hCL1 hrun1 halS ((hkh1.get 19#5).trans e19) f20 f21 f22 f23 f24 f25
    ((hkh1.get 26#5).trans e26) ((hkh1.get 27#5).trans e27) ((hkh1.get 28#5).trans e28) f29 hv1 hA1 hC1
    hm1 ?_
  intro sb2 r2 ps2 m2 v2 A2 hrun2 kf2 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 hv2 hA2 hAv2 hm2
  clear hm1
  refine even_loop hP (table := table) (T := table_bs) (D := scalarRadix16Digits scalar_bs)
    (r0 := r2) (V0 := VRegFile.calleeSaved s0.vregs) htab hdl halS 32 0
    (mkS sb2 (mpl.base 13 + 416#64) r2 S ps2 m2 v2) A2 E1 A2 N1
    (edDouble4 (edMulBaseLoop table_bs (scalarRadix16Digits scalar_bs) 1 0 32 edExtZero)) rfl
    (libCodeLoaded_keepsFrozen hCL1 kf2) hrun2 (if_neg (by decide)).symm rfl g20 g21 g22 g24 g25 g26 g29 g23
    (KeepHi.refl r2) hv2 hA2 (by rw [hAv2, hAv1]) hE1 hA2.1 hN1 hm2 ?_
  intro s3 A3 E3 C3 N3 hCL3 hrun3 hpc3 hsp3 k20 k21 k22 k24 k25 k26 k29 k23 hkh3 hv3 hA3 hAv3 hE3 hC3 hN3 hm3
  clear hm2
  refine reach_eq (s' := mkS s3 (mpl.base 13 + 580#64) s3.regs.regs S s3.pstate s3.mem s3.vregs.regs)
    (by rw [← hpc3, ← hsp3]; rfl) ?_
  refine mainC (table := table) hP hCL3 hrun3 halS ((hkh3.get 19#5).trans g19) k21 ((hkh3.get 27#5).trans g27) hv3 hA3.1 hlo
    (G := (table ↦ᵣ table_bs) ∗ (S ↦ₛ scalarRadix16Digits scalar_bs) ∗ ((S + 232#64) ↦ₛ E3) ∗
      ((S + 392#64) ↦ₛ C3) ∗ ((S + 552#64) ↦ₛ N3) ∗ memRegion (S - 912#64) 912 ∗
      (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ memRegion (S + 224#64) 8 ∗ R)
    (Satisfies.of_eq hm3) ?_
  intro sb4 r4 ps4 m4 v4 hrun4 kf4 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 hv4 hm4
  clear hm3
  have hsp4 : S + 768#64 = s0.sp := hspS.symm
  left
  refine ⟨⟨?_, hsp4, hrun4⟩, ⟨hsp4, ?_⟩, ?_⟩
  · exact (readGpr_eq s0 30#5 (by decide)).symm
  · have g : ∀ k : BitVec 5, k ≠ 31#5 → (mkS sb4 (s0.regs.regs 30#5) r4 (S + 768#64) ps4 m4 v4).readReg64 (.gpr k) =
        r4 k := fun k hk => readGpr_eq _ k hk
    have g0 : ∀ k : BitVec 5, k ≠ 31#5 → s0.readReg64 (.gpr k) = s0.regs.regs k := fun k hk => readGpr_eq _ k hk
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g _ (by decide), g0 _ (by decide)]; exact q19
    · rw [g _ (by decide), g0 _ (by decide)]; exact q20
    · rw [g _ (by decide), g0 _ (by decide)]; exact q21
    · rw [g _ (by decide), g0 _ (by decide)]; exact q22
    · rw [g _ (by decide), g0 _ (by decide)]; exact q23
    · rw [g _ (by decide), g0 _ (by decide)]; exact q24
    · rw [g _ (by decide), g0 _ (by decide)]; exact q25
    · rw [g _ (by decide), g0 _ (by decide)]; exact q26
    · rw [g _ (by decide), g0 _ (by decide)]; exact q27
    · rw [g _ (by decide), g0 _ (by decide)]; exact q28
    · show (mkS sb4 (s0.regs.regs 30#5) r4 (S + 768#64) ps4 m4 v4).readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5)
      rw [g _ (by decide), g0 _ (by decide)]; exact q29
    · exact hv4
  · have hm5 := frame_out (S := S) (D := scalarRadix16Digits scalar_bs) (A := A3) (E := E3) (C := C3) (N := N3)
      (W := [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 28#5, w3, s0.regs.regs 26#5,
        s0.regs.regs 25#5, s0.regs.regs 24#5, s0.regs.regs 23#5, s0.regs.regs 22#5, s0.regs.regs 21#5,
        s0.regs.regs 20#5, s0.regs.regs 19#5])
      (X := (table ↦ᵣ table_bs) ∗ (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
      (out ↦ₛ A3) ∗ R) hdl hA3.1 hE3 hC3 hN3 rfl (Satisfies.of_eq hm4)
    simp only [MultiPlacedLib.withCodeLoaded, edwardsBasepointTableMulBaseSpec, stackFrame]
    rw [show (mkS sb4 (s0.regs.regs 30#5) r4 (S + 768#64) ps4 m4 v4).sp - BitVec.ofNat 64 1680 = S - 912#64 by
      show S + 768#64 - BitVec.ofNat 64 1680 = S - 912#64
      rw [show (BitVec.ofNat 64 1680 : BitVec 64) = 768#64 + 912#64 from rfl, ← BitVec.sub_sub, BitVec.add_sub_cancel]]
    refine post_intro5 (Satisfies.of_eq hm5) ⟨hA3, ?_⟩
    unfold edMulBase; exact hAv3

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

theorem fnOk_basepointTable_mul_base_dev :
    fnOk
      "<curve25519_dalek::edwards::EdwardsBasepointTable as curve25519_dalek::traits::BasepointTable>::mul_base"
      edwardsBasepointTableMulBaseSpec :=
  mb_ok

end X25519Dalek.EMulB
end

open X25519Dalek in
theorem solution :
    fnOk
      "<curve25519_dalek::edwards::EdwardsBasepointTable as curve25519_dalek::traits::BasepointTable>::mul_base"
      edwardsBasepointTableMulBaseSpec :=
  X25519Dalek.EMulB.fnOk_basepointTable_mul_base_dev
