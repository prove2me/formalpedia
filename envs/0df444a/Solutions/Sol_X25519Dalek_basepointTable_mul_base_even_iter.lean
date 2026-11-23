-- Prove2me | solution 1 for X25519Dalek.basepointTable_mul_base_even_iter
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T20:26:09.245158+00:00
-- url     : https://prove2.me/submissions/2771a4ff-b851-463a-8333-3a74db0bacfc

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.BitVec
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_X25519Dalek_Spec
import Theorems.Thm_X25519Dalek_steps_keepsFrozen_v2
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_X25519Dalek_fnOk_fe51_mul_v2
import Theorems.Thm_X25519Dalek_fnOk_lookupTable_select_v2
import Theorems.Thm_X25519Dalek_fnOk_edwardsPoint_add_affineNiels_v2

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
theorem pointsToBytesRO_cons (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    (a ↦ᵣ (b :: bs)) = (a ↦₈ᵣ b) ∗ ((a + 1#64) ↦ᵣ bs) := rfl
theorem pointsToBytesRO_nil (a : BitVec 64) : (a ↦ᵣ ([] : List (BitVec 8))) = emp := rfl

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

theorem pointsToBytesRO_append (a : BitVec 64) (xs ys : List (BitVec 8)) :
    (a ↦ᵣ (xs ++ ys)) = (a ↦ᵣ xs) ∗ ((a + BitVec.ofNat 64 xs.length) ↦ᵣ ys) := by
  induction xs generalizing a with
  | nil => simp [pointsToBytesRO_nil]
  | cons x xs ih =>
    rw [List.cons_append, pointsToBytesRO_cons, pointsToBytesRO_cons, ih, sepConj_assoc]
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

theorem sat_bytes_access {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (k n : Nat) (h : k + n ≤ bs.length) :
    m.canRead (a + BitVec.ofNat 64 k) n = true ∧ m.canWrite (a + BitVec.ofNat 64 k) n = true := by
  have e : ∀ i, a + BitVec.ofNat 64 k + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (k + i) := by
    intro i; rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨canRead_of (fun i hi => ?_), canWrite_of (fun i hi => ?_)⟩
  · rw [e]; have := sat_bytes_read hs (k + i) (by omega); rw [this.2.1]; exact ⟨rfl, this.2.2⟩
  · rw [e]; exact (sat_bytes_read hs (k + i) (by omega)).2.1

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

theorem sat_pre4 {m : Memory} {φ : Prop} {A B C D F : SepProp} (hφ : φ) (hs : m ⊨ A ∗ B ∗ C ∗ D ∗ F) :
    m ⊨ (⌜φ⌝ ∗ A ∗ B ∗ C ∗ D) ∗ F := by
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

theorem y_addi_r {d a : BitVec 5} {k : BitVec 12} {pc' : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD (.gpr d) (.gpr a) k false))
    (h : Reach p (mkS s0 pc' (upd r d (r a + k.setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha]
  exact h

theorem y_subi_r {d a : BitVec 5} {k : BitVec 12} {pc' : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUB (.gpr d) (.gpr a) k false))
    (h : Reach p (mkS s0 pc' (upd r d (r a - k.setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha]
  exact h

theorem y_addi_sp {d : BitVec 5} {k : BitVec 12} {pc' : BitVec 64} (hd : d ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD (.gpr d) .sp k false))
    (h : Reach p (mkS s0 pc' (upd r d (sp + k.setWidth 64)) sp ps m v) Q) :
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

theorem y_bcond_f {c : CondCode} {off : BitVec 64} {pc' : BitVec 64} (hc : ConditionHolds c ps = false) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
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

theorem y_tbz_t {n : BitVec 5} {nz : Bool} {off : BitVec 64} {pc' : BitVec 64} (hn : n ≠ 31#5) (hb : (r n).getLsbD 0 = nz) (hpc : pc + off = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.tbz .W32 nz (.gpr n) 0 off))
    (h : Reach p (mkS s0 pc' r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hn, hb]
  exact h

theorem y_tbz_f {n : BitVec 5} {nz : Bool} {off : BitVec 64} {pc' : BitVec 64} (hn : n ≠ 31#5) (hb : (r n).getLsbD 0 = !nz) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.tbz .W32 nz (.gpr n) 0 off))
    (h : Reach p (mkS s0 pc' r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hn, hb]
  cases nz <;> exact h

theorem y_lsr1 {d a : BitVec 5} {pc' : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.bitfield .W64 .UBFM (.gpr d) (.gpr a) 1 63))
    (h : Reach p (mkS s0 pc' (upd r d (r a >>> 1)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha]
  exact h

theorem y_madd {d a b c : BitVec 5} {pc' : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hc : c ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.dataProc3 .W64 .MADD (.gpr d) (.gpr a) (.gpr b) (.gpr c)))
    (h : Reach p (mkS s0 pc' (upd r d (r c + r a * r b)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, hb, hc]
  exact h

theorem y_ldrb_ro {d b x : BitVec 5} {A : BitVec 64} {w : BitVec 8} {pc' : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5) (hx : x ≠ 31#5) (hA : r b + r x = A) (c : m.canRead A 1 = true) (e : m.read8 A = w) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W32 .B8 false (.gpr d) (.RegOffset (.gpr b) (.gpr x) .UXTX 0)))
    (h : Reach p (mkS s0 pc' (upd r d (((w.setWidth 64).setWidth 32).setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, hb, hx, hA, c, e, extendVal]
  exact h

theorem y_ldpq_o {t1 t2 b : BitVec 5} {off A A16 lo1 hi1 lo2 hi2 : BitVec 64} {pc' : BitVec 64} (hb : b ≠ 31#5) (hA : r b + off = A) (hA16 : A + 16#64 = A16) (c1 : m.canRead A 16 = true) (c2 : m.canRead A16 16 = true) (e1 : m.read64 A = lo1) (e2 : m.read64 (A + 8#64) = hi1) (e3 : m.read64 A16 = lo2) (e4 : m.read64 (A16 + 8#64) = hi2) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldpSimd .Q128 t1 t2 (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 pc' r sp ps m (upd (upd v t1 (hi1 ++ lo1)) t2 (hi2 ++ lo2))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, hA16, c1, c2, e1, e2, e3, e4]
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

theorem asub (S : BitVec 64) (a b c : Nat) (h : c + b = a) (ha : a < 2 ^ 64) :
    S - BitVec.ofNat 64 a + BitVec.ofNat 64 b = S - BitVec.ofNat 64 c := by
  subst h; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The callee area: `912 = k + n` bytes, the top `n` for the callee. -/
theorem area_split {m : Memory} {S : BitVec 64} {R : SepProp} (k n : Nat) (h : k + n = 912)
    (hs : m ⊨ memRegion (S - 912#64) 912 ∗ R) :
    m ⊨ memRegion (S - BitVec.ofNat 64 n) n ∗ memRegion (S - 912#64) k ∗ R := by
  have hs' : m ⊨ memRegion (S - 912#64) (k + n) ∗ R := by rw [h]; exact hs
  have := sat_mr_split k n (by omega) (S - BitVec.ofNat 64 n)
    (asub S 912 k n (by omega) (by norm_num)) hs'
  exact Satisfies.of_eq this

theorem area_merge {m : Memory} {S : BitVec 64} {R : SepProp} (k n : Nat) (h : k + n = 912)
    (hs : m ⊨ memRegion (S - BitVec.ofNat 64 n) n ∗ memRegion (S - 912#64) k ∗ R) :
    m ⊨ memRegion (S - 912#64) 912 ∗ R := by
  have := sat_mr_merge (a := S - 912#64) k n (by omega) (asub S 912 k n (by omega) (by norm_num)).symm
    (Satisfies.of_eq hs)
  rw [h] at this; exact this

theorem addK (S : BitVec 64) (k : BitVec 12) (n : Nat) (h : k.setWidth 64 = BitVec.ofNat 64 n) :
    S + k.setWidth 64 = S + BitVec.ofNat 64 n := by rw [h]

theorem addK2 (S : BitVec 64) (a : Nat) (k : BitVec 12) (n : Nat) (h : a + k.toNat = n) :
    S + BitVec.ofNat 64 a + k.setWidth 64 = S + BitVec.ofNat 64 n := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_setWidth]; omega

theorem subK2 (S : BitVec 64) (a : Nat) (k : BitVec 12) (n : Nat) (h : n + k.toNat = a) :
    S + BitVec.ofNat 64 a - k.setWidth 64 = S + BitVec.ofNat 64 n := by
  have hk := k.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have : k.toNat % 2 ^ 64 = k.toNat := Nat.mod_eq_of_lt (by omega)
  rw [this]; omega

theorem list20 {α : Type} (l : List α) (h : l.length = 20) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19, l = [a0, a1, a2, a3, a4,
      a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, rfl⟩

theorem pcA (b x y z : BitVec 64) (h : x + y = z) : b + x + y = b + z := by
  rw [BitVec.add_assoc, h]

/-- The callee-saved registers `x19`–`x29` other than the loop counter `x23` agree. -/
def KeepHi (r r0 : BitVec 5 → BitVec 64) : Prop :=
  ∀ k : BitVec 5, k ≠ 23#5 → 19 ≤ k.toNat → k.toNat < 30 → r k = r0 k

theorem KeepHi.refl (r : BitVec 5 → BitVec 64) : KeepHi r r := fun _ _ _ _ => rfl

theorem KeepHi.abs {r r' r0 : BitVec 5 → BitVec 64} {d : BitVec 5} (h : KeepHi r r0)
    (hne : ∀ k, k ≠ d → r' k = r k) (hd : d = 23#5 ∨ d.toNat < 19 ∨ 30 ≤ d.toNat) : KeepHi r' r0 := by
  intro k hk h1 h2
  have hkd : k ≠ d := by
    rintro rfl
    rcases hd with hd | hd | hd
    · exact hk hd
    · omega
    · omega
  rw [hne k hkd]; exact h k hk h1 h2

theorem KeepHi.cs {sf : State} {rf r0 : BitVec 5 → BitVec 64} (hc : CSRegs sf rf) (h : KeepHi rf r0) :
    KeepHi sf.regs.regs r0 := by
  intro k hk h1 h2
  obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29⟩ := hc
  have e : ∀ j : Nat, 19 ≤ j → j < 30 → sf.regs.regs (BitVec.ofNat 5 j) = rf (BitVec.ofNat 5 j) := by
    intro j h1 h2
    interval_cases j
    all_goals assumption
  have hk' : k = BitVec.ofNat 5 k.toNat := by simp
  rw [hk', e _ h1 h2, ← hk']
  exact h k hk h1 h2

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
/-! # Block 13 calls of `select`, `EdwardsPoint + AffineNielsPoint` and `mul` through their
published contracts

Each wrapper takes the caller's memory with the callee's footprint in front, runs the `BL`'s target
through `Reach.callS`, and continues from the return state with the callee's postcondition unpacked. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

abbrev mulName : String :=
  "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul"
abbrev selName : String :=
  "<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::select"
abbrev addName : String :=
  "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::add"

theorem lk_mul : lookupBlockSym mulName x25519CliMultiLib.blocks = some (1, 0) := by decide +kernel
theorem lk_sel : lookupBlockSym selName x25519CliMultiLib.blocks = some (6, 0) := by decide +kernel
theorem lk_add : lookupBlockSym addName x25519CliMultiLib.blocks = some (8, 0) := by decide +kernel

/-- A call of `mul` (block 1): `out ← a * b`, callee frame 224 bytes. -/
theorem call_mul {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {Q : State → Prop}
    {s0 : State} {pc : BitVec 64} {rf : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState}
    {m : Memory} {vf : BitVec 5 → BitVec 128} {out a b : BitVec 64} {O A B : List (BitVec 8)}
    {R : SepProp}
    (hpc : pc = mpl.base 1 + BitVec.ofNat 64 0) (hrun : s0.status = .Running)
    (hal : (sp &&& 15#64) = 0#64) (hCL : x25519CliMultiLib.CodeLoaded mpl m)
    (h8 : rf 8#5 = out) (h0 : rf 0#5 = a) (h1 : rf 1#5 = b)
    (hO : O.length = 40) (hA : fe51LimbsBounded A (2 ^ 54)) (hB : fe51LimbsBounded B (2 ^ 54))
    (hm : m ⊨ (a ↦ₛ A) ∗ (b ↦ₛ B) ∗ (out ↦ₛ O) ∗ memRegion (sp - BitVec.ofNat 64 224) 224 ∗ R)
    (hcont : ∀ (sf : State) (res : List (BitVec 8)), sf.status = .Running → sf.sp = sp →
      CSRegs sf rf → calleeSavedVRegs sf = VRegFile.calleeSaved ⟨vf⟩ →
      (sf.mem ⊨ (out ↦ₛ res) ∗ (a ↦ₛ A) ∗ (b ↦ₛ B) ∗ memRegion (sp - BitVec.ofNat 64 224) 224 ∗ R) →
      m.KeepsFrozen sf.mem → fe51LimbsBounded res (2 ^ 52) →
      fe51ValOfBytes res % p25519 = fe51ValOfBytes A * fe51ValOfBytes B % p25519 →
      Reach (bprog mpl 13) (mkS sf (rf 30#5) sf.regs.regs sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl 13) (mkS s0 pc rf sp ps m vf) Q := by
  have hpre := sat_pre4 (φ := (mkS s0 pc rf sp ps m vf).readReg64 Reg.x8 = out ∧
      (mkS s0 pc rf sp ps m vf).readReg64 Reg.x0 = a ∧ (mkS s0 pc rf sp ps m vf).readReg64 Reg.x1 = b ∧
      O.length = 40 ∧ fe51LimbsBounded A (2 ^ 54) ∧ fe51LimbsBounded B (2 ^ 54))
    ⟨by simp [h8], by simp [h0], by simp [h1], hO, hA, hB⟩ hm
  refine Reach.callS hP 13 fnOk_fe51_mul_v2.1 lk_mul (by decide) (out, a, b, O, A, B) R hpc hrun hal hCL
    hpre ?_ ?_ ?_ ?_
  · intro sf; exact not_sat_false
  · intro c sf; exact not_sat_false
  · intro sf; exact not_sat_false
  intro sf hrunf hspf hcs hv hpost hkf
  simp only [stackFrame, hspf] at hpost
  obtain ⟨res, ⟨hb, hval⟩, hpost⟩ := post_unpack (P := (a ↦ₛ A) ∗ (b ↦ₛ B) ∗
    memRegion (sp - BitVec.ofNat 64 224) 224) (Satisfies.of_eq hpost)
  exact hcont sf res hrunf hspf hcs hv (Satisfies.of_eq hpost) hkf hb hval

/-- A call of `LookupTable::select` (block 6): `out ← select(tab, x)`, callee frame 192 bytes. -/
theorem call_sel {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {Q : State → Prop}
    {s0 : State} {pc : BitVec 64} {rf : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState}
    {m : Memory} {vf : BitVec 5 → BitVec 128} {out tab : BitVec 64} {x : BitVec 8}
    {O T : List (BitVec 8)} {R : SepProp}
    (hpc : pc = mpl.base 6 + BitVec.ofNat 64 0) (hrun : s0.status = .Running)
    (hal : (sp &&& 15#64) = 0#64) (hCL : x25519CliMultiLib.CodeLoaded mpl m)
    (h0 : rf 0#5 = out) (h1 : rf 1#5 = tab) (h2 : BitVec.truncate 8 (BitVec.truncate 32 (rf 2#5)) = x)
    (hO : O.length = 120) (hT : fe51LookupTable8Bounded T (2 ^ 53))
    (hm : m ⊨ (tab ↦ᵣ T) ∗ (out ↦ₛ O) ∗ memRegion (sp - BitVec.ofNat 64 192) 192 ∗ R)
    (hcont : ∀ (sf : State) (res : List (BitVec 8)), sf.status = .Running → sf.sp = sp →
      CSRegs sf rf → calleeSavedVRegs sf = VRegFile.calleeSaved ⟨vf⟩ →
      (sf.mem ⊨ (out ↦ₛ res) ∗ (tab ↦ᵣ T) ∗ memRegion (sp - BitVec.ofNat 64 192) 192 ∗ R) →
      m.KeepsFrozen sf.mem → res.length = 120 → fe51AffineNielsBoundedAt res 0 (2 ^ 53) →
      (fe51ValAt res 0 % p25519, fe51ValAt res 40 % p25519, fe51ValAt res 80 % p25519) =
        edSelectAffineNiels T x →
      Reach (bprog mpl 13) (mkS sf (rf 30#5) sf.regs.regs sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl 13) (mkS s0 pc rf sp ps m vf) Q := by
  have hpre := sat_pre3 (φ := (mkS s0 pc rf sp ps m vf).readReg64 Reg.x0 = out ∧
      (mkS s0 pc rf sp ps m vf).readReg64 Reg.x1 = tab ∧
      BitVec.truncate 8 ((mkS s0 pc rf sp ps m vf).readReg32 Reg.x2) = x ∧
      O.length = 120 ∧ fe51LookupTable8Bounded T (2 ^ 53))
    ⟨by simp [h0], by simp [h1], by simpa [State.readReg32] using h2, hO, hT⟩ hm
  refine Reach.callS hP 13 fnOk_lookupTable_select_v2 lk_sel (by decide) (out, tab, x, O, T) R hpc hrun hal
    hCL hpre ?_ ?_ ?_ ?_
  · intro sf; exact not_sat_false
  · intro c sf; exact not_sat_false
  · intro sf; exact not_sat_false
  intro sf hrunf hspf hcs hv hpost hkf
  simp only [stackFrame, hspf] at hpost
  obtain ⟨res, hφ, hpost⟩ := post_unpack (φ := fun res => res.length = 120 ∧ fe51AffineNielsBoundedAt res 0 (2 ^ 53) ∧
      (fe51ValAt res 0 % p25519, fe51ValAt res 40 % p25519, fe51ValAt res 80 % p25519) =
        edSelectAffineNiels T x) (P := (tab ↦ᵣ T) ∗
    memRegion (sp - BitVec.ofNat 64 192) 192) (Satisfies.of_eq hpost)
  exact hcont sf res hrunf hspf hcs hv (Satisfies.of_eq hpost) hkf hφ.1 hφ.2.1 hφ.2.2

/-- A call of `EdwardsPoint + AffineNielsPoint` (block 8), callee frame 528 bytes. -/
theorem call_add {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {Q : State → Prop}
    {s0 : State} {pc : BitVec 64} {rf : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState}
    {m : Memory} {vf : BitVec 5 → BitVec 128} {out self other : BitVec 64}
    {O A N : List (BitVec 8)} {R : SepProp}
    (hpc : pc = mpl.base 8 + BitVec.ofNat 64 0) (hrun : s0.status = .Running)
    (hal : (sp &&& 15#64) = 0#64) (hCL : x25519CliMultiLib.CodeLoaded mpl m)
    (h8 : rf 8#5 = out) (h0 : rf 0#5 = self) (h1 : rf 1#5 = other)
    (hO : O.length = 160) (hA : fe51Point4Bounded A (2 ^ 52)) (hN : N.length = 120)
    (hNb : fe51AffineNielsBoundedAt N 0 (2 ^ 53))
    (hm : m ⊨ (self ↦ₛ A) ∗ (other ↦ₛ N) ∗ (out ↦ₛ O) ∗ memRegion (sp - BitVec.ofNat 64 528) 528 ∗ R)
    (hcont : ∀ (sf : State) (res : List (BitVec 8)), sf.status = .Running → sf.sp = sp →
      CSRegs sf rf → calleeSavedVRegs sf = VRegFile.calleeSaved ⟨vf⟩ →
      (sf.mem ⊨ (out ↦ₛ res) ∗ (self ↦ₛ A) ∗ (other ↦ₛ N) ∗
        memRegion (sp - BitVec.ofNat 64 528) 528 ∗ R) →
      m.KeepsFrozen sf.mem → res.length = 160 →
      fe51LimbsBoundedAt res 0 (2 ^ 52) → fe51LimbsBoundedAt res 40 (2 ^ 53) →
      fe51LimbsBoundedAt res 80 (2 ^ 54) → fe51LimbsBoundedAt res 120 (2 ^ 52) →
      edExtOfBytes res = edAddAffineNiels (edExtOfBytes A) (fe51ValAt N 0 % p25519)
        (fe51ValAt N 40 % p25519) (fe51ValAt N 80 % p25519) →
      Reach (bprog mpl 13) (mkS sf (rf 30#5) sf.regs.regs sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl 13) (mkS s0 pc rf sp ps m vf) Q := by
  obtain ⟨hAl, hA0, hA40, hA80, hA120⟩ := hA
  obtain ⟨hN0, hN40, hN80⟩ := hNb
  have mono : ∀ {bs : List (BitVec 8)} {off b1 b2 : Nat}, b1 ≤ b2 → fe51LimbsBoundedAt bs off b1 →
      fe51LimbsBoundedAt bs off b2 := by
    intro bs off b1 b2 hb h
    obtain ⟨a0, a1, a2, a3, a4⟩ := h
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hpre := sat_pre4 (φ := (mkS s0 pc rf sp ps m vf).readReg64 Reg.x8 = out ∧
      (mkS s0 pc rf sp ps m vf).readReg64 Reg.x0 = self ∧ (mkS s0 pc rf sp ps m vf).readReg64 Reg.x1 = other ∧
      O.length = 160 ∧ A.length = 160 ∧ N.length = 120 ∧
      fe51LimbsBoundedAt A 0 (2 ^ 53) ∧ fe51LimbsBoundedAt A 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt A 80 (2 ^ 52) ∧ fe51LimbsBoundedAt A 120 (2 ^ 54) ∧
      fe51LimbsBoundedAt N 0 (2 ^ 54) ∧ fe51LimbsBoundedAt N 40 (2 ^ 54) ∧ fe51LimbsBoundedAt N 80 (2 ^ 54))
    ⟨by simp [h8], by simp [h0], by simp [h1], hO, hAl, hN, mono (by norm_num) hA0,
      mono (by norm_num) hA40, hA80, mono (by norm_num) hA120, mono (by norm_num) hN0,
      mono (by norm_num) hN40, mono (by norm_num) hN80⟩ hm
  refine Reach.callS hP 13 fnOk_edwardsPoint_add_affineNiels_v2 lk_add (by decide) (out, self, other, O, A, N) R
    hpc hrun hal hCL hpre ?_ ?_ ?_ ?_
  · intro sf; exact not_sat_false
  · intro c sf; exact not_sat_false
  · intro sf; exact not_sat_false
  intro sf hrunf hspf hcs hv hpost hkf
  simp only [stackFrame, hspf] at hpost
  obtain ⟨res, hφ, hpost⟩ := post_unpack (φ := fun res => res.length = 160 ∧
      fe51LimbsBoundedAt res 0 (2 ^ 52) ∧ fe51LimbsBoundedAt res 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt res 80 (2 ^ 54) ∧ fe51LimbsBoundedAt res 120 (2 ^ 52) ∧
      edExtOfBytes res = edAddAffineNiels (edExtOfBytes A) (fe51ValAt N 0 % p25519)
        (fe51ValAt N 40 % p25519) (fe51ValAt N 80 % p25519)) (P := (self ↦ₛ A) ∗ (other ↦ₛ N) ∗
    memRegion (sp - BitVec.ofNat 64 528) 528) (Satisfies.of_eq hpost)
  exact hcont sf res hrunf hspf hcs hv (Satisfies.of_eq hpost) hkf hφ.1 hφ.2.1 hφ.2.2.1 hφ.2.2.2.1
    hφ.2.2.2.2.1 hφ.2.2.2.2.2

end X25519Dalek.EMulB
end

section
/-! # Block 13: the frame of one loop iteration, reshaped around each call; the limb arithmetic

The iteration's memory is `MemI`: the read-only table, the 64 digits at `S`, the accumulator
(`S + 64`), the extended point (`S + 232`), the completed point (`S + 392`), the selected
`AffineNielsPoint` (`S + 552`), the callees' 912-byte area below `S`, and the caller's frame `F`.
`edAsExtended_of_append4` and the readLE lemmas are ported from DeepMind's `Shared51/SliceBase.lean`
(google-deepmind/code-verification @ 8c8d371f, Apache-2.0). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

/-- The memory of one iteration of the loops of `mul_base`. -/
def MemI (table : BitVec 64) (T : List (BitVec 8)) (S : BitVec 64)
    (D A E C N : List (BitVec 8)) (F : SepProp) : SepProp :=
  (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 232#64) ↦ₛ E) ∗ ((S + 392#64) ↦ₛ C) ∗
    ((S + 552#64) ↦ₛ N) ∗ memRegion (S - 912#64) 912 ∗ F

/-- The table as the `i`-th sub-table and the rest. -/
theorem table_split (table : BitVec 64) (T : List (BitVec 8)) (i : Nat) (hi : i < 32)
    (hT : T.length = 30720) :
    (table ↦ᵣ T) = ((table + BitVec.ofNat 64 (960 * i)) ↦ᵣ ByteSlice.slice T (960 * i) 960) ∗
      (table ↦ᵣ T.take (960 * i)) ∗ ((table + BitVec.ofNat 64 (960 * i + 960)) ↦ᵣ T.drop (960 * i + 960)) := by
  conv_lhs => rw [← List.take_append_drop (960 * i) T]
  rw [pointsToBytesRO_append, List.length_take, Nat.min_eq_left (by omega)]
  conv_lhs => rw [← List.take_append_drop 960 (T.drop (960 * i))]
  rw [pointsToBytesRO_append, List.length_take, List.length_drop, Nat.min_eq_left (by omega),
    List.drop_drop, aadd table (960 * i) 960 (960 * i + 960) rfl]
  unfold ByteSlice.slice
  ac_rfl

/-! ## Around `select` -/

/-- The rest of the iteration's memory during the call of `select`. -/
abbrev RS (table : BitVec 64) (T : List (BitVec 8)) (i : Nat) (S : BitVec 64)
    (D A E C : List (BitVec 8)) (F : SepProp) : SepProp :=
  (table ↦ᵣ T.take (960 * i)) ∗ ((table + BitVec.ofNat 64 (960 * i + 960)) ↦ᵣ T.drop (960 * i + 960)) ∗
    (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 232#64) ↦ₛ E) ∗ ((S + 392#64) ↦ₛ C) ∗
    memRegion (S - 912#64) 720 ∗ F

theorem sel_in {m : Memory} {table S : BitVec 64} {T D A E C N : List (BitVec 8)} {F : SepProp}
    {i : Nat} (hi : i < 32) (hT : T.length = 30720) (hs : m ⊨ MemI table T S D A E C N F) :
    m ⊨ ((table + BitVec.ofNat 64 (960 * i)) ↦ᵣ ByteSlice.slice T (960 * i) 960) ∗
      ((S + 552#64) ↦ₛ N) ∗ memRegion (S - BitVec.ofNat 64 192) 192 ∗ RS table T i S D A E C F := by
  unfold MemI at hs
  rw [table_split table T i hi hT] at hs
  have h1 : m ⊨ memRegion (S - 912#64) 912 ∗ (((table + BitVec.ofNat 64 (960 * i)) ↦ᵣ
      ByteSlice.slice T (960 * i) 960) ∗ ((S + 552#64) ↦ₛ N) ∗ (table ↦ᵣ T.take (960 * i)) ∗
      ((table + BitVec.ofNat 64 (960 * i + 960)) ↦ᵣ T.drop (960 * i + 960)) ∗
      (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 232#64) ↦ₛ E) ∗ ((S + 392#64) ↦ₛ C) ∗ F) :=
    Satisfies.of_eq hs
  have h2 := area_split 720 192 rfl h1
  unfold RS; exact Satisfies.of_eq h2

theorem sel_out {m : Memory} {table S : BitVec 64} {T D A E C N : List (BitVec 8)} {F : SepProp}
    {i : Nat} (hi : i < 32) (hT : T.length = 30720)
    (hs : m ⊨ ((S + 552#64) ↦ₛ N) ∗ ((table + BitVec.ofNat 64 (960 * i)) ↦ᵣ ByteSlice.slice T (960 * i) 960) ∗
      memRegion (S - BitVec.ofNat 64 192) 192 ∗ RS table T i S D A E C F) :
    m ⊨ MemI table T S D A E C N F := by
  unfold RS at hs
  have h1 := area_merge (S := S) 720 192 rfl (Satisfies.of_eq hs (Q := memRegion (S - BitVec.ofNat 64 192) 192 ∗
    memRegion (S - 912#64) 720 ∗ (((table + BitVec.ofNat 64 (960 * i)) ↦ᵣ ByteSlice.slice T (960 * i) 960) ∗
      (table ↦ᵣ T.take (960 * i)) ∗ ((table + BitVec.ofNat 64 (960 * i + 960)) ↦ᵣ T.drop (960 * i + 960)) ∗
      ((S + 552#64) ↦ₛ N) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 232#64) ↦ₛ E) ∗ ((S + 392#64) ↦ₛ C) ∗ F)))
  unfold MemI; rw [table_split table T i hi hT]; exact Satisfies.of_eq h1

/-! ## Around the addition -/

abbrev RA (table : BitVec 64) (T : List (BitVec 8)) (S : BitVec 64) (D E : List (BitVec 8))
    (F : SepProp) : SepProp :=
  (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 232#64) ↦ₛ E) ∗ memRegion (S - 912#64) 384 ∗ F

theorem add_in {m : Memory} {table S : BitVec 64} {T D A E C N : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ MemI table T S D A E C N F) :
    m ⊨ ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N) ∗ ((S + 392#64) ↦ₛ C) ∗
      memRegion (S - BitVec.ofNat 64 528) 528 ∗ RA table T S D E F := by
  unfold MemI at hs
  have h1 := area_split (S := S) 384 528 rfl (Satisfies.of_eq hs (Q := memRegion (S - 912#64) 912 ∗
    ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N) ∗ ((S + 392#64) ↦ₛ C) ∗
      ((table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 232#64) ↦ₛ E) ∗ F)))
  unfold RA; exact Satisfies.of_eq h1

/-! ## Around the four multiplications -/

/-- Bytes `40 j … 40 j + 39` of a 160-byte buffer. -/
abbrev q40 (bs : List (BitVec 8)) (j : Nat) : List (BitVec 8) := (bs.drop (40 * j)).take 40

theorem split160 (bs : List (BitVec 8)) (h : bs.length = 160) :
    bs = q40 bs 0 ++ (q40 bs 1 ++ (q40 bs 2 ++ q40 bs 3)) := by
  have e : ∀ k, bs.drop (40 * k) = q40 bs k ++ bs.drop (40 * (k + 1)) := by
    intro k
    rw [q40, show 40 * (k + 1) = 40 * k + 40 by ring, ← List.drop_drop, List.take_append_drop]
  conv_lhs => rw [show bs = bs.drop (40 * 0) by simp, e 0, e 1, e 2]
  have : bs.drop (40 * (2 + 1)) = q40 bs 3 := by
    simp only [q40]; rw [List.take_of_length_le (by simp [h])]
  rw [this]

theorem q40_length (bs : List (BitVec 8)) (h : bs.length = 160) (j : Nat) (hj : j < 4) :
    (q40 bs j).length = 40 := by
  simp [q40, h]; omega

theorem bytes160_split (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 160) :
    (a ↦ₛ bs) = (a ↦ₛ q40 bs 0) ∗ ((a + 40#64) ↦ₛ q40 bs 1) ∗ ((a + 80#64) ↦ₛ q40 bs 2) ∗
      ((a + 120#64) ↦ₛ q40 bs 3) := by
  conv_lhs => rw [split160 bs h]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, q40_length bs h 0 (by omega),
    q40_length bs h 1 (by omega), q40_length bs h 2 (by omega), BitVec.add_assoc, BitVec.add_assoc]
  rfl

theorem bytes160_merge (a : BitVec 64) (b0 b1 b2 b3 : List (BitVec 8)) (h0 : b0.length = 40)
    (h1 : b1.length = 40) (h2 : b2.length = 40) :
    ((a ↦ₛ b0) ∗ ((a + 40#64) ↦ₛ b1) ∗ ((a + 80#64) ↦ₛ b2) ∗ ((a + 120#64) ↦ₛ b3)) =
      (a ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) := by
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, h0, h1, h2, BitVec.add_assoc,
    BitVec.add_assoc]
  rfl

theorem readLE_append_left (xs ys : List (BitVec 8)) (off n : Nat) (h : off + n ≤ xs.length) :
    ByteSlice.readLE (xs ++ ys) off n = ByteSlice.readLE xs off n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ByteSlice.readLE]
    rw [ih (by omega), List.getD_append _ _ _ _ (by omega)]

theorem readLE_append_right (xs ys : List (BitVec 8)) (off n : Nat) (h : xs.length ≤ off) :
    ByteSlice.readLE (xs ++ ys) off n = ByteSlice.readLE ys (off - xs.length) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ByteSlice.readLE]
    rw [ih, List.getD_append_right _ _ _ _ (by omega), show off + n - xs.length = off - xs.length + n by omega]

theorem readLE_q40 (bs : List (BitVec 8)) (h : bs.length = 160) (j : Nat) (hj : j < 4) (off : Nat)
    (ho : off + 8 ≤ 40) : ByteSlice.readLE (q40 bs j) off 8 = ByteSlice.readLE bs (40 * j + off) 8 := by
  have e : bs = bs.take (40 * j) ++ (q40 bs j ++ bs.drop (40 * j + 40)) := by
    rw [q40, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  conv_rhs => rw [e]
  rw [readLE_append_right _ _ _ _ (by simp only [List.length_take]; omega), List.length_take, Nat.min_eq_left (by omega),
    show 40 * j + off - 40 * j = off by omega, readLE_append_left _ _ _ _ (by rw [q40_length bs h j hj]; omega)]

theorem val_q40 (bs : List (BitVec 8)) (h : bs.length = 160) (j : Nat) (hj : j < 4) :
    fe51ValOfBytes (q40 bs j) = fe51ValAt bs (40 * j) := by
  simp only [fe51ValOfBytes, fe51ValAt]
  rw [readLE_q40 bs h j hj 0 (by omega), readLE_q40 bs h j hj 8 (by omega), readLE_q40 bs h j hj 16 (by omega),
    readLE_q40 bs h j hj 24 (by omega), readLE_q40 bs h j hj 32 (by omega), Nat.add_zero]

theorem bnd_q40 (bs : List (BitVec 8)) (h : bs.length = 160) (j : Nat) (hj : j < 4) (B : Nat)
    (hb : fe51LimbsBoundedAt bs (40 * j) B) : fe51LimbsBounded (q40 bs j) B := by
  obtain ⟨b0, b1, b2, b3, b4⟩ := hb
  refine ⟨q40_length bs h j hj, ?_, ?_, ?_, ?_, ?_⟩
  · rw [readLE_q40 bs h j hj 0 (by omega), Nat.add_zero]; exact b0
  · rw [readLE_q40 bs h j hj 8 (by omega)]; exact b1
  · rw [readLE_q40 bs h j hj 16 (by omega)]; exact b2
  · rw [readLE_q40 bs h j hj 24 (by omega)]; exact b3
  · rw [readLE_q40 bs h j hj 32 (by omega)]; exact b4

/-- DeepMind's `edAsExtended_of_append4`. -/
theorem edAsExtended_of_append4 (w0 w1 w2 w3 : List (BitVec 8)) (C : EdExtPoint)
    (hw0 : fe51LimbsBounded w0 (2 ^ 52)) (hw1 : fe51LimbsBounded w1 (2 ^ 52))
    (hw2 : fe51LimbsBounded w2 (2 ^ 52)) (hw3 : fe51LimbsBounded w3 (2 ^ 52))
    (hv0 : fe51ValOfBytes w0 % p25519 = fpMul C.X C.T) (hv1 : fe51ValOfBytes w1 % p25519 = fpMul C.Y C.Z)
    (hv2 : fe51ValOfBytes w2 % p25519 = fpMul C.Z C.T) (hv3 : fe51ValOfBytes w3 % p25519 = fpMul C.X C.Y) :
    fe51Point4Bounded (w0 ++ (w1 ++ (w2 ++ w3))) (2 ^ 52) ∧
      edExtOfBytes (w0 ++ (w1 ++ (w2 ++ w3))) = edAsExtended C := by
  have hw0_l := hw0.1; have hw1_l := hw1.1; have hw2_l := hw2.1; have hw3_l := hw3.1
  have hlen : (w0 ++ (w1 ++ (w2 ++ w3))).length = 160 := by
    simp [List.length_append, hw0_l, hw1_l, hw2_l, hw3_l]
  have hr0 (off : Nat) (ho : off + 8 ≤ 40) :
      ByteSlice.readLE (w0 ++ (w1 ++ (w2 ++ w3))) off 8 = ByteSlice.readLE w0 off 8 :=
    readLE_append_left w0 _ off 8 (by omega)
  have hr1 (off : Nat) (ho1 : 40 ≤ off) (ho2 : off + 8 ≤ 80) :
      ByteSlice.readLE (w0 ++ (w1 ++ (w2 ++ w3))) off 8 = ByteSlice.readLE w1 (off - 40) 8 := by
    rw [readLE_append_right w0 _ off 8 (by omega), hw0_l,
        readLE_append_left w1 _ (off - 40) 8 (by omega)]
  have hr2 (off : Nat) (ho1 : 80 ≤ off) (ho2 : off + 8 ≤ 120) :
      ByteSlice.readLE (w0 ++ (w1 ++ (w2 ++ w3))) off 8 = ByteSlice.readLE w2 (off - 80) 8 := by
    rw [readLE_append_right w0 _ off 8 (by omega), hw0_l,
        readLE_append_right w1 _ (off - 40) 8 (by omega), hw1_l,
        show off - 40 - 40 = off - 80 by omega,
        readLE_append_left w2 _ (off - 80) 8 (by omega)]
  have hr3 (off : Nat) (ho1 : 120 ≤ off) :
      ByteSlice.readLE (w0 ++ (w1 ++ (w2 ++ w3))) off 8 = ByteSlice.readLE w3 (off - 120) 8 := by
    rw [readLE_append_right w0 _ off 8 (by omega), hw0_l,
        readLE_append_right w1 _ (off - 40) 8 (by omega), hw1_l,
        readLE_append_right w2 _ (off - 40 - 40) 8 (by omega), hw2_l,
        show off - 40 - 40 - 40 = off - 120 by omega]
  unfold fe51Point4Bounded fe51LimbsBoundedAt edExtOfBytes fe51ValAt edAsExtended
  simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceSub, Nat.reduceAdd]
  have f : ∀ w : List (BitVec 8), fe51Val (ByteSlice.readLE w 0 8) (ByteSlice.readLE w 8 8)
      (ByteSlice.readLE w 16 8) (ByteSlice.readLE w 24 8) (ByteSlice.readLE w 32 8) = fe51ValOfBytes w :=
    fun _ => rfl
  rw [f w0, f w1, f w2, f w3, hv0, hv1, hv2, hv3]
  exact ⟨⟨hlen, hw0.2, hw1.2, hw2.2, hw3.2⟩, rfl⟩

theorem mul_val {r a b : List (BitVec 8)} {x y : Nat} (hv : fe51ValOfBytes r % p25519 =
    fe51ValOfBytes a * fe51ValOfBytes b % p25519) (ha : fe51ValOfBytes a = x) (hb : fe51ValOfBytes b = y) :
    fe51ValOfBytes r % p25519 = fpMul (x % p25519) (y % p25519) := by
  rw [hv, ha, hb, fpMul, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod]

end X25519Dalek.EMulB
end

section
/-! # Block 13: helpers for the loop iterations

Register bookkeeping (`KeepHi`, `Reach.absR`), the loop counter's arithmetic for `i < 32`
(decided over `Fin 32`, as in DeepMind's `Shared51/BasepointTable.lean`), and the 128-bit copies
between word lists. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

/-! ## The loop counter -/

abbrev cmpPS (x : BitVec 64) : PState := (AddWithCarry64 x (~~~((0x040#12 : BitVec 12).setWidth 64)) true).2

theorem bit_even {i : Nat} (hi : i < 32) : (BitVec.ofNat 64 (2 * i)).getLsbD 0 = false :=
  (by decide : ∀ k : Fin 32, (BitVec.ofNat 64 (2 * k.val)).getLsbD 0 = false) ⟨i, hi⟩
theorem bit_odd {i : Nat} (hi : i < 32) : (BitVec.ofNat 64 (2 * i + 1)).getLsbD 0 = true :=
  (by decide : ∀ k : Fin 32, (BitVec.ofNat 64 (2 * k.val + 1)).getLsbD 0 = true) ⟨i, hi⟩
theorem bit_even' {i : Nat} (hi : i < 32) : (BitVec.ofNat 64 (2 * i)).getLsbD 0 = !true :=
  bit_even hi
theorem inc_even {i : Nat} (hi : i < 32) :
    BitVec.ofNat 64 (2 * i) + (0x001#12 : BitVec 12).setWidth 64 = BitVec.ofNat 64 (2 * i + 1) :=
  (by decide : ∀ k : Fin 32, BitVec.ofNat 64 (2 * k.val) + (0x001#12 : BitVec 12).setWidth 64 =
    BitVec.ofNat 64 (2 * k.val + 1)) ⟨i, hi⟩
theorem inc_odd {i : Nat} (hi : i < 32) :
    BitVec.ofNat 64 (2 * i + 1) + (0x001#12 : BitVec 12).setWidth 64 = BitVec.ofNat 64 (2 * (i + 1)) :=
  (by decide : ∀ k : Fin 32, BitVec.ofNat 64 (2 * k.val + 1) + (0x001#12 : BitVec 12).setWidth 64 =
    BitVec.ofNat 64 (2 * (k.val + 1))) ⟨i, hi⟩
theorem lsr_even {i : Nat} (hi : i < 32) : BitVec.ofNat 64 (2 * i) >>> 1 = BitVec.ofNat 64 i :=
  (by decide : ∀ k : Fin 32, BitVec.ofNat 64 (2 * k.val) >>> 1 = BitVec.ofNat 64 k.val) ⟨i, hi⟩
theorem mul960 {i : Nat} (hi : i < 32) (t : BitVec 64) :
    t + BitVec.ofNat 64 i * 960#64 = t + BitVec.ofNat 64 (960 * i) := by
  rw [(by decide : ∀ k : Fin 32, BitVec.ofNat 64 k.val * 960#64 = BitVec.ofNat 64 (960 * k.val)) ⟨i, hi⟩]

theorem cs_even {i : Nat} (hi : i < 32) : ConditionHolds .CS (cmpPS (BitVec.ofNat 64 (2 * i))) = false :=
  (by decide : ∀ k : Fin 32, ConditionHolds .CS (cmpPS (BitVec.ofNat 64 (2 * k.val))) = false) ⟨i, hi⟩
theorem ne_odd {i : Nat} (hi : i < 32) : ConditionHolds .NE (cmpPS (BitVec.ofNat 64 (2 * i + 1))) = true :=
  (by decide : ∀ k : Fin 32, ConditionHolds .NE (cmpPS (BitVec.ofNat 64 (2 * k.val + 1))) = true) ⟨i, hi⟩
theorem eq_next {i : Nat} (hi : i < 31) : ConditionHolds .EQ (cmpPS (BitVec.ofNat 64 (2 * (i + 1)))) = false :=
  (by decide : ∀ k : Fin 31, ConditionHolds .EQ (cmpPS (BitVec.ofNat 64 (2 * (k.val + 1)))) = false) ⟨i, hi⟩
theorem eq_last : ConditionHolds .EQ (cmpPS (BitVec.ofNat 64 (2 * (31 + 1)))) = true := by decide

end X25519Dalek.EMulB
end

section
/-! # Block 13: memory reshaping around the four multiplications and the 160-byte copy -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem trunc_byte (w : BitVec 8) :
    BitVec.truncate 8 (BitVec.truncate 32 (((w.setWidth 64).setWidth 32).setWidth 64)) = w := by
  revert w; decide

theorem digit_read {m : Memory} {table S : BitVec 64} {T D A E C N : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ MemI table T S D A E C N F) (j : Nat) (hj : j < D.length) :
    m.read8 (S + BitVec.ofNat 64 j) = D.getD j 0#8 ∧ m.canRead (S + BitVec.ofNat 64 j) 1 = true := by
  unfold MemI at hs
  have h1 : m ⊨ (S ↦ₛ D) ∗ ((table ↦ᵣ T) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 232#64) ↦ₛ E) ∗
      ((S + 392#64) ↦ₛ C) ∗ ((S + 552#64) ↦ₛ N) ∗ memRegion (S - 912#64) 912 ∗ F) := Satisfies.of_eq hs
  refine ⟨?_, (sat_bytes_access h1 j 1 (by omega)).1⟩
  rw [(sat_bytes_read h1 j hj).1, List.getD_eq_getElem _ _ hj]

/-! ## The four multiplications -/

abbrev RM (table : BitVec 64) (T : List (BitVec 8)) (S : BitVec 64) (D A N : List (BitVec 8))
    (F : SepProp) : SepProp :=
  (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N) ∗ memRegion (S - 912#64) 688 ∗ F

/-- The memory during the multiplications: the completed point and the extended point as four
40-byte field elements each. -/
abbrev MulShape (table : BitVec 64) (T : List (BitVec 8)) (S : BitVec 64) (D A N : List (BitVec 8))
    (F : SepProp) (C0 C1 C2 C3 E0 E1 E2 E3 : List (BitVec 8)) : SepProp :=
  ((S + 392#64) ↦ₛ C0) ∗ ((S + 432#64) ↦ₛ C1) ∗ ((S + 472#64) ↦ₛ C2) ∗ ((S + 512#64) ↦ₛ C3) ∗
    ((S + 232#64) ↦ₛ E0) ∗ ((S + 272#64) ↦ₛ E1) ∗ ((S + 312#64) ↦ₛ E2) ∗ ((S + 352#64) ↦ₛ E3) ∗
    memRegion (S - BitVec.ofNat 64 224) 224 ∗ RM table T S D A N F

theorem mul_in {m : Memory} {table S : BitVec 64} {T D A E C N : List (BitVec 8)} {F : SepProp}
    (hC : C.length = 160) (hE : E.length = 160)
    (hs : m ⊨ ((S + 392#64) ↦ₛ C) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N) ∗
      memRegion (S - BitVec.ofNat 64 528) 528 ∗ RA table T S D E F) :
    m ⊨ MulShape table T S D A N F (q40 C 0) (q40 C 1) (q40 C 2) (q40 C 3)
      (q40 E 0) (q40 E 1) (q40 E 2) (q40 E 3) := by
  unfold RA at hs
  have h1 := area_merge (S := S) 384 528 rfl (Satisfies.of_eq hs (Q := memRegion (S - BitVec.ofNat 64 528) 528 ∗
    memRegion (S - 912#64) 384 ∗ (((S + 392#64) ↦ₛ C) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N) ∗
      (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 232#64) ↦ₛ E) ∗ F)))
  have h2 := area_split (S := S) 688 224 rfl h1
  rw [bytes160_split _ C hC, bytes160_split _ E hE, aadd S 392 40 432 rfl, aadd S 392 80 472 rfl,
    aadd S 392 120 512 rfl, aadd S 232 40 272 rfl, aadd S 232 80 312 rfl, aadd S 232 120 352 rfl] at h2
  unfold MulShape RM; exact Satisfies.of_eq h2

/-- The rest of the memory during the 160-byte copy. -/
abbrev RC (table : BitVec 64) (T : List (BitVec 8)) (S : BitVec 64) (D C N : List (BitVec 8))
    (F : SepProp) : SepProp :=
  ((S + 392#64) ↦ₛ C) ∗ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 552#64) ↦ₛ N) ∗ memRegion (S - 912#64) 912 ∗ F

theorem copy_in {m : Memory} {table S : BitVec 64} {T D A C N R0 R1 R2 R3 : List (BitVec 8)}
    {F : SepProp} (hA : A.length = 160) (h0 : R0.length = 40) (h1 : R1.length = 40) (h2 : R2.length = 40)
    (h3 : R3.length = 40)
    (hs : m ⊨ MulShape table T S D A N F (q40 C 0) (q40 C 1) (q40 C 2) (q40 C 3) R0 R1 R2 R3)
    (hC : C.length = 160) :
    m ⊨ ((S + 232#64) ↦₆₄* chunks64 (R0 ++ (R1 ++ (R2 ++ R3))) 20) ∗
      ((S + 64#64) ↦₆₄* chunks64 A 20) ∗ RC table T S D C N F := by
  unfold MulShape RM at hs
  rw [← aadd S 392 40 432 rfl, ← aadd S 392 80 472 rfl, ← aadd S 392 120 512 rfl, ← aadd S 232 40 272 rfl,
    ← aadd S 232 80 312 rfl, ← aadd S 232 120 352 rfl] at hs
  have hm := Satisfies.of_eq hs (Q := memRegion (S - BitVec.ofNat 64 224) 224 ∗ memRegion (S - 912#64) 688 ∗
    ((((S + 392#64) ↦ₛ q40 C 0) ∗ ((S + 392#64 + 40#64) ↦ₛ q40 C 1) ∗ ((S + 392#64 + 80#64) ↦ₛ q40 C 2) ∗
      ((S + 392#64 + 120#64) ↦ₛ q40 C 3)) ∗
      (((S + 232#64) ↦ₛ R0) ∗ ((S + 232#64 + 40#64) ↦ₛ R1) ∗ ((S + 232#64 + 80#64) ↦ₛ R2) ∗
      ((S + 232#64 + 120#64) ↦ₛ R3)) ∗ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗
      ((S + 552#64) ↦ₛ N) ∗ F))
  have hm2 := area_merge (S := S) 688 224 rfl hm
  rw [bytes160_merge _ _ _ _ _ (q40_length C hC 0 (by omega)) (q40_length C hC 1 (by omega))
      (q40_length C hC 2 (by omega)), ← split160 C hC, bytes160_merge _ _ _ _ _ h0 h1 h2] at hm2
  have hl : (R0 ++ (R1 ++ (R2 ++ R3))).length = 8 * 20 := by simp [h0, h1, h2, h3]
  rw [← chunks64_flat 20 _ hl, ← words_eq_bytes, ← chunks64_flat 20 A (by rw [hA]), ← words_eq_bytes] at hm2
  unfold RC; exact Satisfies.of_eq hm2

theorem copy_out {m : Memory} {table S : BitVec 64} {T D C N X : List (BitVec 8)} {F : SepProp}
    (hX : X.length = 160)
    (hs : m ⊨ ((S + 232#64) ↦₆₄* chunks64 X 20) ∗ ((S + 64#64) ↦₆₄* chunks64 X 20) ∗ RC table T S D C N F) :
    m ⊨ MemI table T S D X X C N F := by
  rw [words_eq_bytes, words_eq_bytes, chunks64_flat 20 X (by rw [hX])] at hs
  unfold RC at hs; unfold MemI; exact Satisfies.of_eq hs

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

/-- What one iteration establishes: the loop counter advanced by two, the other callee-saved
registers and vector registers kept, and the accumulator advanced by one `edMulBaseStep`. -/
def IterPost (s : State) (pcEnd S table : BitVec 64) (i par : Nat) (T D A : List (BitVec 8)) (F : SepProp)
    (s' : State) : Prop :=
  s'.status = .Running ∧ s'.pc = pcEnd ∧ s'.sp = S ∧ s'.regs.regs 23#5 = BitVec.ofNat 64 (2 * (i + 1)) ∧
    KeepHi s'.regs.regs s.regs.regs ∧ VRegFile.calleeSaved s'.vregs = VRegFile.calleeSaved s.vregs ∧
    ∃ A' E' C' N' : List (BitVec 8), (s'.mem ⊨ MemI table T S D A' E' C' N' F) ∧
      fe51Point4Bounded A' (2 ^ 52) ∧
      edExtOfBytes A' = edMulBaseStep T i (D.getD (2 * i + par) 0#8) (edExtOfBytes A) ∧
      E'.length = 160 ∧ C'.length = 160 ∧ N'.length = 120

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

theorem c13_404 : (bprog mpl j).fetchMem m (mpl.base 13 + 404#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x17#5) (Reg.gpr 0x17#5) 0x001#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 404) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x17#5) (Reg.gpr 0x17#5) 0x001#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_408 : (bprog mpl j).fetchMem m (mpl.base 13 + 408#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x17#5) 0x040#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 408) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x17#5) 0x040#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_412 : (bprog mpl j).fetchMem m (mpl.base 13 + 412#64) =
    some (Instr.bCond (CondCode.EQ) 0x00000000000000a8#64) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 412) (inst := (Instr.bCond (CondCode.EQ) 0x00000000000000a8#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_416 : (bprog mpl j).fetchMem m (mpl.base 13 + 416#64) =
    some (Instr.tbz (RegWidth.W32) true (Reg.gpr 0x17#5) 0 0xfffffffffffffff4#64) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 416) (inst := (Instr.tbz (RegWidth.W32) true (Reg.gpr 0x17#5) 0 0xfffffffffffffff4#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_420 : (bprog mpl j).fetchMem m (mpl.base 13 + 420#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x00#5) (Reg.gpr 0x17#5) 1 63) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 420) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x00#5) (Reg.gpr 0x17#5) 1 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_424 : (bprog mpl j).fetchMem m (mpl.base 13 + 424#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x17#5) 0x040#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 424) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x17#5) 0x040#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_428 : (bprog mpl j).fetchMem m (mpl.base 13 + 428#64) =
    some (Instr.bCond (CondCode.CS) 0x00000000000000e0#64) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 428) (inst := (Instr.bCond (CondCode.CS) 0x00000000000000e0#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_432 : (bprog mpl j).fetchMem m (mpl.base 13 + 432#64) =
    some (Instr.dataProc3 (RegWidth.W64) (DataProc3Op.MADD) (Reg.gpr 0x01#5) (Reg.gpr 0x00#5) (Reg.gpr 0x19#5) (Reg.gpr 0x14#5)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 432) (inst := (Instr.dataProc3 (RegWidth.W64) (DataProc3Op.MADD) (Reg.gpr 0x01#5) (Reg.gpr 0x00#5) (Reg.gpr 0x19#5) (Reg.gpr 0x14#5))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_436 : (bprog mpl j).fetchMem m (mpl.base 13 + 436#64) =
    some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x02#5) (AddrMode.RegOffset (Reg.gpr 0x1a#5) (Reg.gpr 0x17#5) (ExtendType.UXTX) 0)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 436) (inst := (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x02#5) (AddrMode.RegOffset (Reg.gpr 0x1a#5) (Reg.gpr 0x17#5) (ExtendType.UXTX) 0))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_440 : (bprog mpl j).fetchMem m (mpl.base 13 + 440#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x00#5) (Reg.gpr 0x1d#5) 0x078#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 440) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x00#5) (Reg.gpr 0x1d#5) 0x078#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_444 {j' offj : Nat} (hlk : lookupBlockSym selName x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 13 + 444#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 13 + BitVec.ofNat 64 444))) :=
  fetch_bl hP hCL (i := 13) (by decide) j (off := 444) (name := selName) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c13_448 : (bprog mpl j).fetchMem m (mpl.base 13 + 448#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.sp) 0x188#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 448) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.sp) 0x188#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_452 : (bprog mpl j).fetchMem m (mpl.base 13 + 452#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x040#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 452) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x040#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_456 : (bprog mpl j).fetchMem m (mpl.base 13 + 456#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x01#5) (Reg.gpr 0x1d#5) 0x078#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 456) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x01#5) (Reg.gpr 0x1d#5) 0x078#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_460 {j' offj : Nat} (hlk : lookupBlockSym addName x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 13 + 460#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 13 + BitVec.ofNat 64 460))) :=
  fetch_bl hP hCL (i := 13) (by decide) j (off := 460) (name := addName) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c13_464 : (bprog mpl j).fetchMem m (mpl.base 13 + 464#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.sp) 0x0e8#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 464) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.sp) 0x0e8#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_468 : (bprog mpl j).fetchMem m (mpl.base 13 + 468#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x188#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 468) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x188#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_472 : (bprog mpl j).fetchMem m (mpl.base 13 + 472#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.gpr 0x16#5) 0x078#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 472) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.gpr 0x16#5) 0x078#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_476 {j' offj : Nat} (hlk : lookupBlockSym mulName x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 13 + 476#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 13 + BitVec.ofNat 64 476))) :=
  fetch_bl hP hCL (i := 13) (by decide) j (off := 476) (name := mulName) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c13_480 : (bprog mpl j).fetchMem m (mpl.base 13 + 480#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x18#5) 0x028#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 480) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x18#5) 0x028#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_484 : (bprog mpl j).fetchMem m (mpl.base 13 + 484#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.gpr 0x16#5) 0x028#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 484) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.gpr 0x16#5) 0x028#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_488 : (bprog mpl j).fetchMem m (mpl.base 13 + 488#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.gpr 0x16#5) 0x050#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 488) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.gpr 0x16#5) 0x050#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_492 {j' offj : Nat} (hlk : lookupBlockSym mulName x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 13 + 492#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 13 + BitVec.ofNat 64 492))) :=
  fetch_bl hP hCL (i := 13) (by decide) j (off := 492) (name := mulName) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c13_496 : (bprog mpl j).fetchMem m (mpl.base 13 + 496#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x18#5) 0x050#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 496) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x18#5) 0x050#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_500 : (bprog mpl j).fetchMem m (mpl.base 13 + 500#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.gpr 0x16#5) 0x050#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 500) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.gpr 0x16#5) 0x050#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_504 : (bprog mpl j).fetchMem m (mpl.base 13 + 504#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.gpr 0x16#5) 0x078#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 504) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.gpr 0x16#5) 0x078#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_508 {j' offj : Nat} (hlk : lookupBlockSym mulName x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 13 + 508#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 13 + BitVec.ofNat 64 508))) :=
  fetch_bl hP hCL (i := 13) (by decide) j (off := 508) (name := mulName) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c13_512 : (bprog mpl j).fetchMem m (mpl.base 13 + 512#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x18#5) 0x078#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 512) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x18#5) 0x078#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_516 : (bprog mpl j).fetchMem m (mpl.base 13 + 516#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x188#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 516) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x188#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_520 : (bprog mpl j).fetchMem m (mpl.base 13 + 520#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.gpr 0x16#5) 0x028#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 520) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.gpr 0x16#5) 0x028#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_524 {j' offj : Nat} (hlk : lookupBlockSym mulName x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 13 + 524#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 13 + BitVec.ofNat 64 524))) :=
  fetch_bl hP hCL (i := 13) (by decide) j (off := 524) (name := mulName) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c13_528 : (bprog mpl j).fetchMem m (mpl.base 13 + 528#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000060#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 528) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000060#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_532 : (bprog mpl j).fetchMem m (mpl.base 13 + 532#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x17#5) (Reg.gpr 0x17#5) 0x001#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 532) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x17#5) (Reg.gpr 0x17#5) 0x001#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_536 : (bprog mpl j).fetchMem m (mpl.base 13 + 536#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 536) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_540 : (bprog mpl j).fetchMem m (mpl.base 13 + 540#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x02#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000080#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 540) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x02#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000080#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_544 : (bprog mpl j).fetchMem m (mpl.base 13 + 544#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x02#5 (AddrMode.Offset (Reg.sp) 0x00000000000000c0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 544) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x02#5 (AddrMode.Offset (Reg.sp) 0x00000000000000c0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_548 : (bprog mpl j).fetchMem m (mpl.base 13 + 548#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000020#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 548) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000020#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_552 : (bprog mpl j).fetchMem m (mpl.base 13 + 552#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000060#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 552) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000060#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_556 : (bprog mpl j).fetchMem m (mpl.base 13 + 556#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x02#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 556) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x02#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_560 : (bprog mpl j).fetchMem m (mpl.base 13 + 560#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x02#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000080#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 560) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x02#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000080#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_564 : (bprog mpl j).fetchMem m (mpl.base 13 + 564#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000000#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 564) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000000#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_568 : (bprog mpl j).fetchMem m (mpl.base 13 + 568#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 568) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_572 : (bprog mpl j).fetchMem m (mpl.base 13 + 572#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x17#5) 0x040#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 572) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x17#5) 0x040#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_576 : (bprog mpl j).fetchMem m (mpl.base 13 + 576#64) =
    some (Instr.bCond (CondCode.NE) 0xffffffffffffff60#64) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 576) (inst := (Instr.bCond (CondCode.NE) 0xffffffffffffff60#64)) (by decide) rfl (by decide +kernel) hk
  exact this

end

end X25519Dalek.EMulB
end

section
/-! # Block 13: one even iteration of `mul_base` (generated by tools/gen_iter.py) -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

set_option maxHeartbeats 4000000 in
theorem even_reach {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s : State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S table : BitVec 64} {i : Nat}
    {T D A E C N : List (BitVec 8)} {F : SepProp}
    (hi : i < 32) (hrun : s.status = .Running) (hal : (S &&& 15#64) = 0#64)
    (h20 : s.regs.regs 20#5 = table)
    (h21 : s.regs.regs 21#5 = S + 232#64)
    (h22 : s.regs.regs 22#5 = S + 392#64)
    (h23 : s.regs.regs 23#5 = BitVec.ofNat 64 (2 * i))
    (h24 : s.regs.regs 24#5 = S + 232#64)
    (h25 : s.regs.regs 25#5 = 960#64)
    (h26 : s.regs.regs 26#5 = S)
    (h29 : s.regs.regs 29#5 = S + 672#64)
    (htab : fe51BasepointTable32Bounded T (2 ^ 53)) (hD : D.length = 64)
    (hA : fe51Point4Bounded A (2 ^ 52)) (hE : E.length = 160) (hC : C.length = 160)
    (hN : N.length = 120) (hs : s.mem ⊨ MemI table T S D A E C N F) :
    Reach (bprog mpl 13) (mkS s (mpl.base 13 + 416#64) s.regs.regs S s.pstate s.mem s.vregs.regs)
      (IterPost s (if i = 31 then mpl.base 13 + 580#64 else mpl.base 13 + 416#64) S table i 0 T D A F) := by
  have kf0 : s.mem.KeepsFrozen s.mem := Memory.KeepsFrozen.refl _
  have kh0 : KeepHi s.regs.regs s.regs.regs := KeepHi.refl _
  have hv0 : VRegFile.calleeSaved ⟨s.vregs.regs⟩ = VRegFile.calleeSaved s.vregs := rfl
  -- 416: tb(n)z w23, #0 (not taken)
  refine y_tbz_f (n := 23#5) (by decide) (by rw [h23]; exact bit_even' hi) (pcA _ _ _ (420#64) (by decide)) hrun (c13_416 hP hCL 13 kf0) ?_
  -- 420: lsr x0, x23, #1
  refine y_lsr1 (d := 0#5) (a := 23#5) (by decide) (by decide) (pcA _ _ _ (424#64) (by decide)) hrun (c13_420 hP hCL 13 kf0) ?_
  refine Reach.absR (fun r1 hn1 hw1 => ?_)
  have e20_1 : r1 20#5 = table := (hn1 _ (by decide)).trans h20
  have e21_1 : r1 21#5 = S + 232#64 := (hn1 _ (by decide)).trans h21
  have e22_1 : r1 22#5 = S + 392#64 := (hn1 _ (by decide)).trans h22
  have e23_1 : r1 23#5 = BitVec.ofNat 64 (2 * i) := (hn1 _ (by decide)).trans h23
  have e24_1 : r1 24#5 = S + 232#64 := (hn1 _ (by decide)).trans h24
  have e25_1 : r1 25#5 = 960#64 := (hn1 _ (by decide)).trans h25
  have e26_1 : r1 26#5 = S := (hn1 _ (by decide)).trans h26
  have e29_1 : r1 29#5 = S + 672#64 := (hn1 _ (by decide)).trans h29
  have e0_1 : r1 0#5 = BitVec.ofNat 64 i := (by rw [hw1, h23, lsr_even hi])
  have kh1 : KeepHi r1 s.regs.regs := KeepHi.abs kh0 hn1 (by decide)
  clear hn1 hw1
  -- 424: cmp x23, #64
  refine y_cmpi (n := 23#5) (by decide) (pcA _ _ _ (428#64) (by decide)) hrun (c13_424 hP hCL 13 kf0) ?_
  -- 428: b.cond (not taken)
  refine y_bcond_f (by rw [e23_1]; exact cs_even hi) (pcA _ _ _ (432#64) (by decide)) hrun (c13_428 hP hCL 13 kf0) ?_
  -- 432: madd x1, x0, x25, x20
  refine y_madd (d := 1#5) (a := 0#5) (b := 25#5) (c := 20#5) (by decide) (by decide) (by decide) (by decide) (pcA _ _ _ (436#64) (by decide)) hrun (c13_432 hP hCL 13 kf0) ?_
  refine Reach.absR (fun r2 hn2 hw2 => ?_)
  have e0_2 : r2 0#5 = BitVec.ofNat 64 i := (hn2 _ (by decide)).trans e0_1
  have e20_2 : r2 20#5 = table := (hn2 _ (by decide)).trans e20_1
  have e21_2 : r2 21#5 = S + 232#64 := (hn2 _ (by decide)).trans e21_1
  have e22_2 : r2 22#5 = S + 392#64 := (hn2 _ (by decide)).trans e22_1
  have e23_2 : r2 23#5 = BitVec.ofNat 64 (2 * i) := (hn2 _ (by decide)).trans e23_1
  have e24_2 : r2 24#5 = S + 232#64 := (hn2 _ (by decide)).trans e24_1
  have e25_2 : r2 25#5 = 960#64 := (hn2 _ (by decide)).trans e25_1
  have e26_2 : r2 26#5 = S := (hn2 _ (by decide)).trans e26_1
  have e29_2 : r2 29#5 = S + 672#64 := (hn2 _ (by decide)).trans e29_1
  have e1_2 : r2 1#5 = table + BitVec.ofNat 64 (960 * i) := (by rw [hw2, e20_1, e0_1, e25_1, mul960 hi])
  have kh2 : KeepHi r2 s.regs.regs := KeepHi.abs kh1 hn2 (by decide)
  clear hn2 hw2
  -- 436: ldrb w2, [x26, x23]
  have hdg := digit_read hs (2 * i) (by omega)
  refine y_ldrb_ro (d := 2#5) (b := 26#5) (x := 23#5) (A := S + BitVec.ofNat 64 (2 * i)) (w := D.getD (2 * i) 0#8) (by decide) (by decide) (by decide) (by rw [e26_2, e23_2]) hdg.2 hdg.1 (pcA _ _ _ (440#64) (by decide)) hrun (c13_436 hP hCL 13 kf0) ?_
  clear hdg
  refine Reach.absR (fun r3 hn3 hw3 => ?_)
  have e0_3 : r3 0#5 = BitVec.ofNat 64 i := (hn3 _ (by decide)).trans e0_2
  have e1_3 : r3 1#5 = table + BitVec.ofNat 64 (960 * i) := (hn3 _ (by decide)).trans e1_2
  have e20_3 : r3 20#5 = table := (hn3 _ (by decide)).trans e20_2
  have e21_3 : r3 21#5 = S + 232#64 := (hn3 _ (by decide)).trans e21_2
  have e22_3 : r3 22#5 = S + 392#64 := (hn3 _ (by decide)).trans e22_2
  have e23_3 : r3 23#5 = BitVec.ofNat 64 (2 * i) := (hn3 _ (by decide)).trans e23_2
  have e24_3 : r3 24#5 = S + 232#64 := (hn3 _ (by decide)).trans e24_2
  have e25_3 : r3 25#5 = 960#64 := (hn3 _ (by decide)).trans e25_2
  have e26_3 : r3 26#5 = S := (hn3 _ (by decide)).trans e26_2
  have e29_3 : r3 29#5 = S + 672#64 := (hn3 _ (by decide)).trans e29_2
  have e2_3 : r3 2#5 = ((((D.getD (2 * i) 0#8).setWidth 64).setWidth 32).setWidth 64) := hw3
  have kh3 : KeepHi r3 s.regs.regs := KeepHi.abs kh2 hn3 (by decide)
  clear hn3 hw3
  -- 440: sub x0, x29, #120
  refine y_subi_r (d := 0#5) (a := 29#5) (by decide) (by decide) (pcA _ _ _ (444#64) (by decide)) hrun (c13_440 hP hCL 13 kf0) ?_
  refine Reach.absR (fun r4 hn4 hw4 => ?_)
  have e1_4 : r4 1#5 = table + BitVec.ofNat 64 (960 * i) := (hn4 _ (by decide)).trans e1_3
  have e2_4 : r4 2#5 = ((((D.getD (2 * i) 0#8).setWidth 64).setWidth 32).setWidth 64) := (hn4 _ (by decide)).trans e2_3
  have e20_4 : r4 20#5 = table := (hn4 _ (by decide)).trans e20_3
  have e21_4 : r4 21#5 = S + 232#64 := (hn4 _ (by decide)).trans e21_3
  have e22_4 : r4 22#5 = S + 392#64 := (hn4 _ (by decide)).trans e22_3
  have e23_4 : r4 23#5 = BitVec.ofNat 64 (2 * i) := (hn4 _ (by decide)).trans e23_3
  have e24_4 : r4 24#5 = S + 232#64 := (hn4 _ (by decide)).trans e24_3
  have e25_4 : r4 25#5 = 960#64 := (hn4 _ (by decide)).trans e25_3
  have e26_4 : r4 26#5 = S := (hn4 _ (by decide)).trans e26_3
  have e29_4 : r4 29#5 = S + 672#64 := (hn4 _ (by decide)).trans e29_3
  have e0_4 : r4 0#5 = S + 552#64 := (by rw [hw4, e29_3]; exact subK2 S 672 _ 552 (by decide))
  have kh4 : KeepHi r4 s.regs.regs := KeepHi.abs kh3 hn4 (by decide)
  clear hn4 hw4
  -- 444: bl
  refine y_bl (add_sub_cancel' _ _) (pcA _ _ _ (448#64) (by decide)) hrun (c13_444 hP hCL 13 kf0 lk_sel) ?_
  refine Reach.absR (fun r5 hn5 hw5 => ?_)
  have e0_5 : r5 0#5 = S + 552#64 := (hn5 _ (by decide)).trans e0_4
  have e1_5 : r5 1#5 = table + BitVec.ofNat 64 (960 * i) := (hn5 _ (by decide)).trans e1_4
  have e2_5 : r5 2#5 = ((((D.getD (2 * i) 0#8).setWidth 64).setWidth 32).setWidth 64) := (hn5 _ (by decide)).trans e2_4
  have e20_5 : r5 20#5 = table := (hn5 _ (by decide)).trans e20_4
  have e21_5 : r5 21#5 = S + 232#64 := (hn5 _ (by decide)).trans e21_4
  have e22_5 : r5 22#5 = S + 392#64 := (hn5 _ (by decide)).trans e22_4
  have e23_5 : r5 23#5 = BitVec.ofNat 64 (2 * i) := (hn5 _ (by decide)).trans e23_4
  have e24_5 : r5 24#5 = S + 232#64 := (hn5 _ (by decide)).trans e24_4
  have e25_5 : r5 25#5 = 960#64 := (hn5 _ (by decide)).trans e25_4
  have e26_5 : r5 26#5 = S := (hn5 _ (by decide)).trans e26_4
  have e29_5 : r5 29#5 = S + 672#64 := (hn5 _ (by decide)).trans e29_4
  have e30_5 : r5 30#5 = mpl.base 13 + 448#64 := hw5
  have kh5 : KeepHi r5 s.regs.regs := KeepHi.abs kh4 hn5 (by decide)
  clear hn5 hw5
  refine call_sel (x := D.getD (2 * i) 0#8) hP rfl hrun hal (libCodeLoaded_keepsFrozen hCL kf0) e0_5 e1_5 (by rw [e2_5]; exact trunc_byte _) hN (htab.2 i hi) (sel_in hi htab.1 hs) ?_
  intro sf1 N1 hrun1 hsp1 hcs1 hv1 hm1 hkf1 hN1 hNb1 hNv1
  rw [e30_5]
  have e20_c1 : sf1.regs.regs 20#5 = table := (hcs1.2.1).trans e20_5
  have e21_c1 : sf1.regs.regs 21#5 = S + 232#64 := (hcs1.2.2.1).trans e21_5
  have e22_c1 : sf1.regs.regs 22#5 = S + 392#64 := (hcs1.2.2.2.1).trans e22_5
  have e23_c1 : sf1.regs.regs 23#5 = BitVec.ofNat 64 (2 * i) := (hcs1.2.2.2.2.1).trans e23_5
  have e24_c1 : sf1.regs.regs 24#5 = S + 232#64 := (hcs1.2.2.2.2.2.1).trans e24_5
  have e25_c1 : sf1.regs.regs 25#5 = 960#64 := (hcs1.2.2.2.2.2.2.1).trans e25_5
  have e26_c1 : sf1.regs.regs 26#5 = S := (hcs1.2.2.2.2.2.2.2.1).trans e26_5
  have e29_c1 : sf1.regs.regs 29#5 = S + 672#64 := (hcs1.2.2.2.2.2.2.2.2.2.2).trans e29_5
  have khc1 : KeepHi sf1.regs.regs s.regs.regs := KeepHi.cs hcs1 kh5
  have kfc1 : s.mem.KeepsFrozen sf1.mem := kf0.trans hkf1
  have hvc1 : VRegFile.calleeSaved ⟨sf1.vregs.regs⟩ = VRegFile.calleeSaved s.vregs := hv1.trans hv0
  clear hcs1 hkf1 hv1
  have hmS1 := sel_out hi htab.1 hm1
  clear hm1
  -- 448: add x8, sp, #392
  refine y_addi_sp (d := 8#5) (by decide) (pcA _ _ _ (452#64) (by decide)) hrun1 (c13_448 hP hCL 13 kfc1) ?_
  refine Reach.absR (fun r6 hn6 hw6 => ?_)
  have e20_6 : r6 20#5 = table := (hn6 _ (by decide)).trans e20_c1
  have e21_6 : r6 21#5 = S + 232#64 := (hn6 _ (by decide)).trans e21_c1
  have e22_6 : r6 22#5 = S + 392#64 := (hn6 _ (by decide)).trans e22_c1
  have e23_6 : r6 23#5 = BitVec.ofNat 64 (2 * i) := (hn6 _ (by decide)).trans e23_c1
  have e24_6 : r6 24#5 = S + 232#64 := (hn6 _ (by decide)).trans e24_c1
  have e25_6 : r6 25#5 = 960#64 := (hn6 _ (by decide)).trans e25_c1
  have e26_6 : r6 26#5 = S := (hn6 _ (by decide)).trans e26_c1
  have e29_6 : r6 29#5 = S + 672#64 := (hn6 _ (by decide)).trans e29_c1
  have e8_6 : r6 8#5 = S + 392#64 := (hw6.trans (addK S _ 392 (by decide)))
  have kh6 : KeepHi r6 s.regs.regs := KeepHi.abs khc1 hn6 (by decide)
  clear hn6 hw6
  -- 452: add x0, sp, #64
  refine y_addi_sp (d := 0#5) (by decide) (pcA _ _ _ (456#64) (by decide)) hrun1 (c13_452 hP hCL 13 kfc1) ?_
  refine Reach.absR (fun r7 hn7 hw7 => ?_)
  have e8_7 : r7 8#5 = S + 392#64 := (hn7 _ (by decide)).trans e8_6
  have e20_7 : r7 20#5 = table := (hn7 _ (by decide)).trans e20_6
  have e21_7 : r7 21#5 = S + 232#64 := (hn7 _ (by decide)).trans e21_6
  have e22_7 : r7 22#5 = S + 392#64 := (hn7 _ (by decide)).trans e22_6
  have e23_7 : r7 23#5 = BitVec.ofNat 64 (2 * i) := (hn7 _ (by decide)).trans e23_6
  have e24_7 : r7 24#5 = S + 232#64 := (hn7 _ (by decide)).trans e24_6
  have e25_7 : r7 25#5 = 960#64 := (hn7 _ (by decide)).trans e25_6
  have e26_7 : r7 26#5 = S := (hn7 _ (by decide)).trans e26_6
  have e29_7 : r7 29#5 = S + 672#64 := (hn7 _ (by decide)).trans e29_6
  have e0_7 : r7 0#5 = S + 64#64 := (hw7.trans (addK S _ 64 (by decide)))
  have kh7 : KeepHi r7 s.regs.regs := KeepHi.abs kh6 hn7 (by decide)
  clear hn7 hw7
  -- 456: sub x1, x29, #120
  refine y_subi_r (d := 1#5) (a := 29#5) (by decide) (by decide) (pcA _ _ _ (460#64) (by decide)) hrun1 (c13_456 hP hCL 13 kfc1) ?_
  refine Reach.absR (fun r8 hn8 hw8 => ?_)
  have e0_8 : r8 0#5 = S + 64#64 := (hn8 _ (by decide)).trans e0_7
  have e8_8 : r8 8#5 = S + 392#64 := (hn8 _ (by decide)).trans e8_7
  have e20_8 : r8 20#5 = table := (hn8 _ (by decide)).trans e20_7
  have e21_8 : r8 21#5 = S + 232#64 := (hn8 _ (by decide)).trans e21_7
  have e22_8 : r8 22#5 = S + 392#64 := (hn8 _ (by decide)).trans e22_7
  have e23_8 : r8 23#5 = BitVec.ofNat 64 (2 * i) := (hn8 _ (by decide)).trans e23_7
  have e24_8 : r8 24#5 = S + 232#64 := (hn8 _ (by decide)).trans e24_7
  have e25_8 : r8 25#5 = 960#64 := (hn8 _ (by decide)).trans e25_7
  have e26_8 : r8 26#5 = S := (hn8 _ (by decide)).trans e26_7
  have e29_8 : r8 29#5 = S + 672#64 := (hn8 _ (by decide)).trans e29_7
  have e1_8 : r8 1#5 = S + 552#64 := (by rw [hw8, e29_7]; exact subK2 S 672 _ 552 (by decide))
  have kh8 : KeepHi r8 s.regs.regs := KeepHi.abs kh7 hn8 (by decide)
  clear hn8 hw8
  -- 460: bl
  refine y_bl (add_sub_cancel' _ _) (pcA _ _ _ (464#64) (by decide)) hrun1 (c13_460 hP hCL 13 kfc1 lk_add) ?_
  refine Reach.absR (fun r9 hn9 hw9 => ?_)
  have e0_9 : r9 0#5 = S + 64#64 := (hn9 _ (by decide)).trans e0_8
  have e1_9 : r9 1#5 = S + 552#64 := (hn9 _ (by decide)).trans e1_8
  have e8_9 : r9 8#5 = S + 392#64 := (hn9 _ (by decide)).trans e8_8
  have e20_9 : r9 20#5 = table := (hn9 _ (by decide)).trans e20_8
  have e21_9 : r9 21#5 = S + 232#64 := (hn9 _ (by decide)).trans e21_8
  have e22_9 : r9 22#5 = S + 392#64 := (hn9 _ (by decide)).trans e22_8
  have e23_9 : r9 23#5 = BitVec.ofNat 64 (2 * i) := (hn9 _ (by decide)).trans e23_8
  have e24_9 : r9 24#5 = S + 232#64 := (hn9 _ (by decide)).trans e24_8
  have e25_9 : r9 25#5 = 960#64 := (hn9 _ (by decide)).trans e25_8
  have e26_9 : r9 26#5 = S := (hn9 _ (by decide)).trans e26_8
  have e29_9 : r9 29#5 = S + 672#64 := (hn9 _ (by decide)).trans e29_8
  have e30_9 : r9 30#5 = mpl.base 13 + 464#64 := hw9
  have kh9 : KeepHi r9 s.regs.regs := KeepHi.abs kh8 hn9 (by decide)
  clear hn9 hw9
  refine call_add hP rfl hrun1 hal (libCodeLoaded_keepsFrozen hCL kfc1) e8_9 e0_9 e1_9 hC hA hN1 hNb1 (add_in hmS1) ?_
  intro sf2 Cr hrun2 hsp2 hcs2 hv2 hm2 hkf2 hCl hC0 hC40 hC80 hC120 hCv
  rw [e30_9]
  have e20_c2 : sf2.regs.regs 20#5 = table := (hcs2.2.1).trans e20_9
  have e21_c2 : sf2.regs.regs 21#5 = S + 232#64 := (hcs2.2.2.1).trans e21_9
  have e22_c2 : sf2.regs.regs 22#5 = S + 392#64 := (hcs2.2.2.2.1).trans e22_9
  have e23_c2 : sf2.regs.regs 23#5 = BitVec.ofNat 64 (2 * i) := (hcs2.2.2.2.2.1).trans e23_9
  have e24_c2 : sf2.regs.regs 24#5 = S + 232#64 := (hcs2.2.2.2.2.2.1).trans e24_9
  have e25_c2 : sf2.regs.regs 25#5 = 960#64 := (hcs2.2.2.2.2.2.2.1).trans e25_9
  have e26_c2 : sf2.regs.regs 26#5 = S := (hcs2.2.2.2.2.2.2.2.1).trans e26_9
  have e29_c2 : sf2.regs.regs 29#5 = S + 672#64 := (hcs2.2.2.2.2.2.2.2.2.2.2).trans e29_9
  have khc2 : KeepHi sf2.regs.regs s.regs.regs := KeepHi.cs hcs2 kh9
  have kfc2 : s.mem.KeepsFrozen sf2.mem := kfc1.trans hkf2
  have hvc2 : VRegFile.calleeSaved ⟨sf2.vregs.regs⟩ = VRegFile.calleeSaved s.vregs := hv2.trans hvc1
  clear hcs2 hkf2 hv2
  have hmM : sf2.mem ⊨ ((S + 392#64) ↦ₛ q40 Cr 0) ∗ ((S + 432#64) ↦ₛ q40 Cr 1) ∗ ((S + 472#64) ↦ₛ q40 Cr 2) ∗ ((S + 512#64) ↦ₛ q40 Cr 3) ∗ ((S + 232#64) ↦ₛ q40 E 0) ∗ ((S + 272#64) ↦ₛ q40 E 1) ∗ ((S + 312#64) ↦ₛ q40 E 2) ∗ ((S + 352#64) ↦ₛ q40 E 3) ∗ (memRegion (S - BitVec.ofNat 64 224) 224) ∗ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N1) ∗ (memRegion (S - 912#64) 688) ∗ (F) := by
    have := mul_in hCl hE hm2; unfold MulShape RM at this; exact this
  clear hm2
  have mono : ∀ {bs : List (BitVec 8)} {off b1 b2 : Nat}, b1 ≤ b2 → fe51LimbsBoundedAt bs off b1 →
      fe51LimbsBoundedAt bs off b2 := by
    intro bs off b1 b2 hb h
    obtain ⟨a0, a1, a2, a3, a4⟩ := h
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hc0 : fe51LimbsBounded (q40 Cr 0) (2 ^ 54) := bnd_q40 Cr hCl 0 (by decide) _ (mono (by norm_num) hC0)
  have hc1 : fe51LimbsBounded (q40 Cr 1) (2 ^ 54) := bnd_q40 Cr hCl 1 (by decide) _ (mono (by norm_num) hC40)
  have hc2 : fe51LimbsBounded (q40 Cr 2) (2 ^ 54) := bnd_q40 Cr hCl 2 (by decide) _ hC80
  have hc3 : fe51LimbsBounded (q40 Cr 3) (2 ^ 54) := bnd_q40 Cr hCl 3 (by decide) _ (mono (by norm_num) hC120)
  -- 464: add x8, sp, #232
  refine y_addi_sp (d := 8#5) (by decide) (pcA _ _ _ (468#64) (by decide)) hrun2 (c13_464 hP hCL 13 kfc2) ?_
  refine Reach.absR (fun r10 hn10 hw10 => ?_)
  have e20_10 : r10 20#5 = table := (hn10 _ (by decide)).trans e20_c2
  have e21_10 : r10 21#5 = S + 232#64 := (hn10 _ (by decide)).trans e21_c2
  have e22_10 : r10 22#5 = S + 392#64 := (hn10 _ (by decide)).trans e22_c2
  have e23_10 : r10 23#5 = BitVec.ofNat 64 (2 * i) := (hn10 _ (by decide)).trans e23_c2
  have e24_10 : r10 24#5 = S + 232#64 := (hn10 _ (by decide)).trans e24_c2
  have e25_10 : r10 25#5 = 960#64 := (hn10 _ (by decide)).trans e25_c2
  have e26_10 : r10 26#5 = S := (hn10 _ (by decide)).trans e26_c2
  have e29_10 : r10 29#5 = S + 672#64 := (hn10 _ (by decide)).trans e29_c2
  have e8_10 : r10 8#5 = S + 232#64 := (hw10.trans (addK S _ 232 (by decide)))
  have kh10 : KeepHi r10 s.regs.regs := KeepHi.abs khc2 hn10 (by decide)
  clear hn10 hw10
  -- 468: add x0, sp, #392
  refine y_addi_sp (d := 0#5) (by decide) (pcA _ _ _ (472#64) (by decide)) hrun2 (c13_468 hP hCL 13 kfc2) ?_
  refine Reach.absR (fun r11 hn11 hw11 => ?_)
  have e8_11 : r11 8#5 = S + 232#64 := (hn11 _ (by decide)).trans e8_10
  have e20_11 : r11 20#5 = table := (hn11 _ (by decide)).trans e20_10
  have e21_11 : r11 21#5 = S + 232#64 := (hn11 _ (by decide)).trans e21_10
  have e22_11 : r11 22#5 = S + 392#64 := (hn11 _ (by decide)).trans e22_10
  have e23_11 : r11 23#5 = BitVec.ofNat 64 (2 * i) := (hn11 _ (by decide)).trans e23_10
  have e24_11 : r11 24#5 = S + 232#64 := (hn11 _ (by decide)).trans e24_10
  have e25_11 : r11 25#5 = 960#64 := (hn11 _ (by decide)).trans e25_10
  have e26_11 : r11 26#5 = S := (hn11 _ (by decide)).trans e26_10
  have e29_11 : r11 29#5 = S + 672#64 := (hn11 _ (by decide)).trans e29_10
  have e0_11 : r11 0#5 = S + 392#64 := (hw11.trans (addK S _ 392 (by decide)))
  have kh11 : KeepHi r11 s.regs.regs := KeepHi.abs kh10 hn11 (by decide)
  clear hn11 hw11
  -- 472: add x1, x22, #120
  refine y_addi_r (d := 1#5) (a := 22#5) (by decide) (by decide) (pcA _ _ _ (476#64) (by decide)) hrun2 (c13_472 hP hCL 13 kfc2) ?_
  refine Reach.absR (fun r12 hn12 hw12 => ?_)
  have e0_12 : r12 0#5 = S + 392#64 := (hn12 _ (by decide)).trans e0_11
  have e8_12 : r12 8#5 = S + 232#64 := (hn12 _ (by decide)).trans e8_11
  have e20_12 : r12 20#5 = table := (hn12 _ (by decide)).trans e20_11
  have e21_12 : r12 21#5 = S + 232#64 := (hn12 _ (by decide)).trans e21_11
  have e22_12 : r12 22#5 = S + 392#64 := (hn12 _ (by decide)).trans e22_11
  have e23_12 : r12 23#5 = BitVec.ofNat 64 (2 * i) := (hn12 _ (by decide)).trans e23_11
  have e24_12 : r12 24#5 = S + 232#64 := (hn12 _ (by decide)).trans e24_11
  have e25_12 : r12 25#5 = 960#64 := (hn12 _ (by decide)).trans e25_11
  have e26_12 : r12 26#5 = S := (hn12 _ (by decide)).trans e26_11
  have e29_12 : r12 29#5 = S + 672#64 := (hn12 _ (by decide)).trans e29_11
  have e1_12 : r12 1#5 = S + 512#64 := (by rw [hw12, e22_11]; exact addK2 S 392 _ 512 (by decide))
  have kh12 : KeepHi r12 s.regs.regs := KeepHi.abs kh11 hn12 (by decide)
  clear hn12 hw12
  -- 476: bl
  refine y_bl (add_sub_cancel' _ _) (pcA _ _ _ (480#64) (by decide)) hrun2 (c13_476 hP hCL 13 kfc2 lk_mul) ?_
  refine Reach.absR (fun r13 hn13 hw13 => ?_)
  have e0_13 : r13 0#5 = S + 392#64 := (hn13 _ (by decide)).trans e0_12
  have e1_13 : r13 1#5 = S + 512#64 := (hn13 _ (by decide)).trans e1_12
  have e8_13 : r13 8#5 = S + 232#64 := (hn13 _ (by decide)).trans e8_12
  have e20_13 : r13 20#5 = table := (hn13 _ (by decide)).trans e20_12
  have e21_13 : r13 21#5 = S + 232#64 := (hn13 _ (by decide)).trans e21_12
  have e22_13 : r13 22#5 = S + 392#64 := (hn13 _ (by decide)).trans e22_12
  have e23_13 : r13 23#5 = BitVec.ofNat 64 (2 * i) := (hn13 _ (by decide)).trans e23_12
  have e24_13 : r13 24#5 = S + 232#64 := (hn13 _ (by decide)).trans e24_12
  have e25_13 : r13 25#5 = 960#64 := (hn13 _ (by decide)).trans e25_12
  have e26_13 : r13 26#5 = S := (hn13 _ (by decide)).trans e26_12
  have e29_13 : r13 29#5 = S + 672#64 := (hn13 _ (by decide)).trans e29_12
  have e30_13 : r13 30#5 = mpl.base 13 + 480#64 := hw13
  have kh13 : KeepHi r13 s.regs.regs := KeepHi.abs kh12 hn13 (by decide)
  clear hn13 hw13
  refine call_mul hP rfl hrun2 hal (libCodeLoaded_keepsFrozen hCL kfc2) e8_13 e0_13 e1_13 (q40_length E hE 0 (by decide)) hc0 hc3 (Satisfies.of_eq hmM (Q := ((S + 392#64) ↦ₛ q40 Cr 0) ∗ ((S + 512#64) ↦ₛ q40 Cr 3) ∗ ((S + 232#64) ↦ₛ q40 E 0) ∗ (memRegion (S - BitVec.ofNat 64 224) 224) ∗ ((S + 432#64) ↦ₛ q40 Cr 1) ∗ ((S + 472#64) ↦ₛ q40 Cr 2) ∗ ((S + 272#64) ↦ₛ q40 E 1) ∗ ((S + 312#64) ↦ₛ q40 E 2) ∗ ((S + 352#64) ↦ₛ q40 E 3) ∗ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N1) ∗ (memRegion (S - 912#64) 688) ∗ (F))) ?_
  intro sf3 R0 hrun3 hsp3 hcs3 hv3 hm3 hkf3 hRb3 hRv3
  rw [e30_13]
  have e20_c3 : sf3.regs.regs 20#5 = table := (hcs3.2.1).trans e20_13
  have e21_c3 : sf3.regs.regs 21#5 = S + 232#64 := (hcs3.2.2.1).trans e21_13
  have e22_c3 : sf3.regs.regs 22#5 = S + 392#64 := (hcs3.2.2.2.1).trans e22_13
  have e23_c3 : sf3.regs.regs 23#5 = BitVec.ofNat 64 (2 * i) := (hcs3.2.2.2.2.1).trans e23_13
  have e24_c3 : sf3.regs.regs 24#5 = S + 232#64 := (hcs3.2.2.2.2.2.1).trans e24_13
  have e25_c3 : sf3.regs.regs 25#5 = 960#64 := (hcs3.2.2.2.2.2.2.1).trans e25_13
  have e26_c3 : sf3.regs.regs 26#5 = S := (hcs3.2.2.2.2.2.2.2.1).trans e26_13
  have e29_c3 : sf3.regs.regs 29#5 = S + 672#64 := (hcs3.2.2.2.2.2.2.2.2.2.2).trans e29_13
  have khc3 : KeepHi sf3.regs.regs s.regs.regs := KeepHi.cs hcs3 kh13
  have kfc3 : s.mem.KeepsFrozen sf3.mem := kfc2.trans hkf3
  have hvc3 : VRegFile.calleeSaved ⟨sf3.vregs.regs⟩ = VRegFile.calleeSaved s.vregs := hv3.trans hvc2
  clear hcs3 hkf3 hv3
  replace hm3 : sf3.mem ⊨ ((S + 392#64) ↦ₛ q40 Cr 0) ∗ ((S + 432#64) ↦ₛ q40 Cr 1) ∗ ((S + 472#64) ↦ₛ q40 Cr 2) ∗ ((S + 512#64) ↦ₛ q40 Cr 3) ∗ ((S + 232#64) ↦ₛ R0) ∗ ((S + 272#64) ↦ₛ q40 E 1) ∗ ((S + 312#64) ↦ₛ q40 E 2) ∗ ((S + 352#64) ↦ₛ q40 E 3) ∗ (memRegion (S - BitVec.ofNat 64 224) 224) ∗ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N1) ∗ (memRegion (S - 912#64) 688) ∗ (F) := Satisfies.of_eq hm3
  -- 480: add x8, x24, #40
  refine y_addi_r (d := 8#5) (a := 24#5) (by decide) (by decide) (pcA _ _ _ (484#64) (by decide)) hrun3 (c13_480 hP hCL 13 kfc3) ?_
  refine Reach.absR (fun r14 hn14 hw14 => ?_)
  have e20_14 : r14 20#5 = table := (hn14 _ (by decide)).trans e20_c3
  have e21_14 : r14 21#5 = S + 232#64 := (hn14 _ (by decide)).trans e21_c3
  have e22_14 : r14 22#5 = S + 392#64 := (hn14 _ (by decide)).trans e22_c3
  have e23_14 : r14 23#5 = BitVec.ofNat 64 (2 * i) := (hn14 _ (by decide)).trans e23_c3
  have e24_14 : r14 24#5 = S + 232#64 := (hn14 _ (by decide)).trans e24_c3
  have e25_14 : r14 25#5 = 960#64 := (hn14 _ (by decide)).trans e25_c3
  have e26_14 : r14 26#5 = S := (hn14 _ (by decide)).trans e26_c3
  have e29_14 : r14 29#5 = S + 672#64 := (hn14 _ (by decide)).trans e29_c3
  have e8_14 : r14 8#5 = S + 272#64 := (by rw [hw14, e24_c3]; exact addK2 S 232 _ 272 (by decide))
  have kh14 : KeepHi r14 s.regs.regs := KeepHi.abs khc3 hn14 (by decide)
  clear hn14 hw14
  -- 484: add x0, x22, #40
  refine y_addi_r (d := 0#5) (a := 22#5) (by decide) (by decide) (pcA _ _ _ (488#64) (by decide)) hrun3 (c13_484 hP hCL 13 kfc3) ?_
  refine Reach.absR (fun r15 hn15 hw15 => ?_)
  have e8_15 : r15 8#5 = S + 272#64 := (hn15 _ (by decide)).trans e8_14
  have e20_15 : r15 20#5 = table := (hn15 _ (by decide)).trans e20_14
  have e21_15 : r15 21#5 = S + 232#64 := (hn15 _ (by decide)).trans e21_14
  have e22_15 : r15 22#5 = S + 392#64 := (hn15 _ (by decide)).trans e22_14
  have e23_15 : r15 23#5 = BitVec.ofNat 64 (2 * i) := (hn15 _ (by decide)).trans e23_14
  have e24_15 : r15 24#5 = S + 232#64 := (hn15 _ (by decide)).trans e24_14
  have e25_15 : r15 25#5 = 960#64 := (hn15 _ (by decide)).trans e25_14
  have e26_15 : r15 26#5 = S := (hn15 _ (by decide)).trans e26_14
  have e29_15 : r15 29#5 = S + 672#64 := (hn15 _ (by decide)).trans e29_14
  have e0_15 : r15 0#5 = S + 432#64 := (by rw [hw15, e22_14]; exact addK2 S 392 _ 432 (by decide))
  have kh15 : KeepHi r15 s.regs.regs := KeepHi.abs kh14 hn15 (by decide)
  clear hn15 hw15
  -- 488: add x1, x22, #80
  refine y_addi_r (d := 1#5) (a := 22#5) (by decide) (by decide) (pcA _ _ _ (492#64) (by decide)) hrun3 (c13_488 hP hCL 13 kfc3) ?_
  refine Reach.absR (fun r16 hn16 hw16 => ?_)
  have e0_16 : r16 0#5 = S + 432#64 := (hn16 _ (by decide)).trans e0_15
  have e8_16 : r16 8#5 = S + 272#64 := (hn16 _ (by decide)).trans e8_15
  have e20_16 : r16 20#5 = table := (hn16 _ (by decide)).trans e20_15
  have e21_16 : r16 21#5 = S + 232#64 := (hn16 _ (by decide)).trans e21_15
  have e22_16 : r16 22#5 = S + 392#64 := (hn16 _ (by decide)).trans e22_15
  have e23_16 : r16 23#5 = BitVec.ofNat 64 (2 * i) := (hn16 _ (by decide)).trans e23_15
  have e24_16 : r16 24#5 = S + 232#64 := (hn16 _ (by decide)).trans e24_15
  have e25_16 : r16 25#5 = 960#64 := (hn16 _ (by decide)).trans e25_15
  have e26_16 : r16 26#5 = S := (hn16 _ (by decide)).trans e26_15
  have e29_16 : r16 29#5 = S + 672#64 := (hn16 _ (by decide)).trans e29_15
  have e1_16 : r16 1#5 = S + 472#64 := (by rw [hw16, e22_15]; exact addK2 S 392 _ 472 (by decide))
  have kh16 : KeepHi r16 s.regs.regs := KeepHi.abs kh15 hn16 (by decide)
  clear hn16 hw16
  -- 492: bl
  refine y_bl (add_sub_cancel' _ _) (pcA _ _ _ (496#64) (by decide)) hrun3 (c13_492 hP hCL 13 kfc3 lk_mul) ?_
  refine Reach.absR (fun r17 hn17 hw17 => ?_)
  have e0_17 : r17 0#5 = S + 432#64 := (hn17 _ (by decide)).trans e0_16
  have e1_17 : r17 1#5 = S + 472#64 := (hn17 _ (by decide)).trans e1_16
  have e8_17 : r17 8#5 = S + 272#64 := (hn17 _ (by decide)).trans e8_16
  have e20_17 : r17 20#5 = table := (hn17 _ (by decide)).trans e20_16
  have e21_17 : r17 21#5 = S + 232#64 := (hn17 _ (by decide)).trans e21_16
  have e22_17 : r17 22#5 = S + 392#64 := (hn17 _ (by decide)).trans e22_16
  have e23_17 : r17 23#5 = BitVec.ofNat 64 (2 * i) := (hn17 _ (by decide)).trans e23_16
  have e24_17 : r17 24#5 = S + 232#64 := (hn17 _ (by decide)).trans e24_16
  have e25_17 : r17 25#5 = 960#64 := (hn17 _ (by decide)).trans e25_16
  have e26_17 : r17 26#5 = S := (hn17 _ (by decide)).trans e26_16
  have e29_17 : r17 29#5 = S + 672#64 := (hn17 _ (by decide)).trans e29_16
  have e30_17 : r17 30#5 = mpl.base 13 + 496#64 := hw17
  have kh17 : KeepHi r17 s.regs.regs := KeepHi.abs kh16 hn17 (by decide)
  clear hn17 hw17
  refine call_mul hP rfl hrun3 hal (libCodeLoaded_keepsFrozen hCL kfc3) e8_17 e0_17 e1_17 (q40_length E hE 1 (by decide)) hc1 hc2 (Satisfies.of_eq hm3 (Q := ((S + 432#64) ↦ₛ q40 Cr 1) ∗ ((S + 472#64) ↦ₛ q40 Cr 2) ∗ ((S + 272#64) ↦ₛ q40 E 1) ∗ (memRegion (S - BitVec.ofNat 64 224) 224) ∗ ((S + 392#64) ↦ₛ q40 Cr 0) ∗ ((S + 512#64) ↦ₛ q40 Cr 3) ∗ ((S + 232#64) ↦ₛ R0) ∗ ((S + 312#64) ↦ₛ q40 E 2) ∗ ((S + 352#64) ↦ₛ q40 E 3) ∗ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N1) ∗ (memRegion (S - 912#64) 688) ∗ (F))) ?_
  intro sf4 R1 hrun4 hsp4 hcs4 hv4 hm4 hkf4 hRb4 hRv4
  rw [e30_17]
  have e20_c4 : sf4.regs.regs 20#5 = table := (hcs4.2.1).trans e20_17
  have e21_c4 : sf4.regs.regs 21#5 = S + 232#64 := (hcs4.2.2.1).trans e21_17
  have e22_c4 : sf4.regs.regs 22#5 = S + 392#64 := (hcs4.2.2.2.1).trans e22_17
  have e23_c4 : sf4.regs.regs 23#5 = BitVec.ofNat 64 (2 * i) := (hcs4.2.2.2.2.1).trans e23_17
  have e24_c4 : sf4.regs.regs 24#5 = S + 232#64 := (hcs4.2.2.2.2.2.1).trans e24_17
  have e25_c4 : sf4.regs.regs 25#5 = 960#64 := (hcs4.2.2.2.2.2.2.1).trans e25_17
  have e26_c4 : sf4.regs.regs 26#5 = S := (hcs4.2.2.2.2.2.2.2.1).trans e26_17
  have e29_c4 : sf4.regs.regs 29#5 = S + 672#64 := (hcs4.2.2.2.2.2.2.2.2.2.2).trans e29_17
  have khc4 : KeepHi sf4.regs.regs s.regs.regs := KeepHi.cs hcs4 kh17
  have kfc4 : s.mem.KeepsFrozen sf4.mem := kfc3.trans hkf4
  have hvc4 : VRegFile.calleeSaved ⟨sf4.vregs.regs⟩ = VRegFile.calleeSaved s.vregs := hv4.trans hvc3
  clear hcs4 hkf4 hv4
  replace hm4 : sf4.mem ⊨ ((S + 392#64) ↦ₛ q40 Cr 0) ∗ ((S + 432#64) ↦ₛ q40 Cr 1) ∗ ((S + 472#64) ↦ₛ q40 Cr 2) ∗ ((S + 512#64) ↦ₛ q40 Cr 3) ∗ ((S + 232#64) ↦ₛ R0) ∗ ((S + 272#64) ↦ₛ R1) ∗ ((S + 312#64) ↦ₛ q40 E 2) ∗ ((S + 352#64) ↦ₛ q40 E 3) ∗ (memRegion (S - BitVec.ofNat 64 224) 224) ∗ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N1) ∗ (memRegion (S - 912#64) 688) ∗ (F) := Satisfies.of_eq hm4
  -- 496: add x8, x24, #80
  refine y_addi_r (d := 8#5) (a := 24#5) (by decide) (by decide) (pcA _ _ _ (500#64) (by decide)) hrun4 (c13_496 hP hCL 13 kfc4) ?_
  refine Reach.absR (fun r18 hn18 hw18 => ?_)
  have e20_18 : r18 20#5 = table := (hn18 _ (by decide)).trans e20_c4
  have e21_18 : r18 21#5 = S + 232#64 := (hn18 _ (by decide)).trans e21_c4
  have e22_18 : r18 22#5 = S + 392#64 := (hn18 _ (by decide)).trans e22_c4
  have e23_18 : r18 23#5 = BitVec.ofNat 64 (2 * i) := (hn18 _ (by decide)).trans e23_c4
  have e24_18 : r18 24#5 = S + 232#64 := (hn18 _ (by decide)).trans e24_c4
  have e25_18 : r18 25#5 = 960#64 := (hn18 _ (by decide)).trans e25_c4
  have e26_18 : r18 26#5 = S := (hn18 _ (by decide)).trans e26_c4
  have e29_18 : r18 29#5 = S + 672#64 := (hn18 _ (by decide)).trans e29_c4
  have e8_18 : r18 8#5 = S + 312#64 := (by rw [hw18, e24_c4]; exact addK2 S 232 _ 312 (by decide))
  have kh18 : KeepHi r18 s.regs.regs := KeepHi.abs khc4 hn18 (by decide)
  clear hn18 hw18
  -- 500: add x0, x22, #80
  refine y_addi_r (d := 0#5) (a := 22#5) (by decide) (by decide) (pcA _ _ _ (504#64) (by decide)) hrun4 (c13_500 hP hCL 13 kfc4) ?_
  refine Reach.absR (fun r19 hn19 hw19 => ?_)
  have e8_19 : r19 8#5 = S + 312#64 := (hn19 _ (by decide)).trans e8_18
  have e20_19 : r19 20#5 = table := (hn19 _ (by decide)).trans e20_18
  have e21_19 : r19 21#5 = S + 232#64 := (hn19 _ (by decide)).trans e21_18
  have e22_19 : r19 22#5 = S + 392#64 := (hn19 _ (by decide)).trans e22_18
  have e23_19 : r19 23#5 = BitVec.ofNat 64 (2 * i) := (hn19 _ (by decide)).trans e23_18
  have e24_19 : r19 24#5 = S + 232#64 := (hn19 _ (by decide)).trans e24_18
  have e25_19 : r19 25#5 = 960#64 := (hn19 _ (by decide)).trans e25_18
  have e26_19 : r19 26#5 = S := (hn19 _ (by decide)).trans e26_18
  have e29_19 : r19 29#5 = S + 672#64 := (hn19 _ (by decide)).trans e29_18
  have e0_19 : r19 0#5 = S + 472#64 := (by rw [hw19, e22_18]; exact addK2 S 392 _ 472 (by decide))
  have kh19 : KeepHi r19 s.regs.regs := KeepHi.abs kh18 hn19 (by decide)
  clear hn19 hw19
  -- 504: add x1, x22, #120
  refine y_addi_r (d := 1#5) (a := 22#5) (by decide) (by decide) (pcA _ _ _ (508#64) (by decide)) hrun4 (c13_504 hP hCL 13 kfc4) ?_
  refine Reach.absR (fun r20 hn20 hw20 => ?_)
  have e0_20 : r20 0#5 = S + 472#64 := (hn20 _ (by decide)).trans e0_19
  have e8_20 : r20 8#5 = S + 312#64 := (hn20 _ (by decide)).trans e8_19
  have e20_20 : r20 20#5 = table := (hn20 _ (by decide)).trans e20_19
  have e21_20 : r20 21#5 = S + 232#64 := (hn20 _ (by decide)).trans e21_19
  have e22_20 : r20 22#5 = S + 392#64 := (hn20 _ (by decide)).trans e22_19
  have e23_20 : r20 23#5 = BitVec.ofNat 64 (2 * i) := (hn20 _ (by decide)).trans e23_19
  have e24_20 : r20 24#5 = S + 232#64 := (hn20 _ (by decide)).trans e24_19
  have e25_20 : r20 25#5 = 960#64 := (hn20 _ (by decide)).trans e25_19
  have e26_20 : r20 26#5 = S := (hn20 _ (by decide)).trans e26_19
  have e29_20 : r20 29#5 = S + 672#64 := (hn20 _ (by decide)).trans e29_19
  have e1_20 : r20 1#5 = S + 512#64 := (by rw [hw20, e22_19]; exact addK2 S 392 _ 512 (by decide))
  have kh20 : KeepHi r20 s.regs.regs := KeepHi.abs kh19 hn20 (by decide)
  clear hn20 hw20
  -- 508: bl
  refine y_bl (add_sub_cancel' _ _) (pcA _ _ _ (512#64) (by decide)) hrun4 (c13_508 hP hCL 13 kfc4 lk_mul) ?_
  refine Reach.absR (fun r21 hn21 hw21 => ?_)
  have e0_21 : r21 0#5 = S + 472#64 := (hn21 _ (by decide)).trans e0_20
  have e1_21 : r21 1#5 = S + 512#64 := (hn21 _ (by decide)).trans e1_20
  have e8_21 : r21 8#5 = S + 312#64 := (hn21 _ (by decide)).trans e8_20
  have e20_21 : r21 20#5 = table := (hn21 _ (by decide)).trans e20_20
  have e21_21 : r21 21#5 = S + 232#64 := (hn21 _ (by decide)).trans e21_20
  have e22_21 : r21 22#5 = S + 392#64 := (hn21 _ (by decide)).trans e22_20
  have e23_21 : r21 23#5 = BitVec.ofNat 64 (2 * i) := (hn21 _ (by decide)).trans e23_20
  have e24_21 : r21 24#5 = S + 232#64 := (hn21 _ (by decide)).trans e24_20
  have e25_21 : r21 25#5 = 960#64 := (hn21 _ (by decide)).trans e25_20
  have e26_21 : r21 26#5 = S := (hn21 _ (by decide)).trans e26_20
  have e29_21 : r21 29#5 = S + 672#64 := (hn21 _ (by decide)).trans e29_20
  have e30_21 : r21 30#5 = mpl.base 13 + 512#64 := hw21
  have kh21 : KeepHi r21 s.regs.regs := KeepHi.abs kh20 hn21 (by decide)
  clear hn21 hw21
  refine call_mul hP rfl hrun4 hal (libCodeLoaded_keepsFrozen hCL kfc4) e8_21 e0_21 e1_21 (q40_length E hE 2 (by decide)) hc2 hc3 (Satisfies.of_eq hm4 (Q := ((S + 472#64) ↦ₛ q40 Cr 2) ∗ ((S + 512#64) ↦ₛ q40 Cr 3) ∗ ((S + 312#64) ↦ₛ q40 E 2) ∗ (memRegion (S - BitVec.ofNat 64 224) 224) ∗ ((S + 392#64) ↦ₛ q40 Cr 0) ∗ ((S + 432#64) ↦ₛ q40 Cr 1) ∗ ((S + 232#64) ↦ₛ R0) ∗ ((S + 272#64) ↦ₛ R1) ∗ ((S + 352#64) ↦ₛ q40 E 3) ∗ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N1) ∗ (memRegion (S - 912#64) 688) ∗ (F))) ?_
  intro sf5 R2 hrun5 hsp5 hcs5 hv5 hm5 hkf5 hRb5 hRv5
  rw [e30_21]
  have e20_c5 : sf5.regs.regs 20#5 = table := (hcs5.2.1).trans e20_21
  have e21_c5 : sf5.regs.regs 21#5 = S + 232#64 := (hcs5.2.2.1).trans e21_21
  have e22_c5 : sf5.regs.regs 22#5 = S + 392#64 := (hcs5.2.2.2.1).trans e22_21
  have e23_c5 : sf5.regs.regs 23#5 = BitVec.ofNat 64 (2 * i) := (hcs5.2.2.2.2.1).trans e23_21
  have e24_c5 : sf5.regs.regs 24#5 = S + 232#64 := (hcs5.2.2.2.2.2.1).trans e24_21
  have e25_c5 : sf5.regs.regs 25#5 = 960#64 := (hcs5.2.2.2.2.2.2.1).trans e25_21
  have e26_c5 : sf5.regs.regs 26#5 = S := (hcs5.2.2.2.2.2.2.2.1).trans e26_21
  have e29_c5 : sf5.regs.regs 29#5 = S + 672#64 := (hcs5.2.2.2.2.2.2.2.2.2.2).trans e29_21
  have khc5 : KeepHi sf5.regs.regs s.regs.regs := KeepHi.cs hcs5 kh21
  have kfc5 : s.mem.KeepsFrozen sf5.mem := kfc4.trans hkf5
  have hvc5 : VRegFile.calleeSaved ⟨sf5.vregs.regs⟩ = VRegFile.calleeSaved s.vregs := hv5.trans hvc4
  clear hcs5 hkf5 hv5
  replace hm5 : sf5.mem ⊨ ((S + 392#64) ↦ₛ q40 Cr 0) ∗ ((S + 432#64) ↦ₛ q40 Cr 1) ∗ ((S + 472#64) ↦ₛ q40 Cr 2) ∗ ((S + 512#64) ↦ₛ q40 Cr 3) ∗ ((S + 232#64) ↦ₛ R0) ∗ ((S + 272#64) ↦ₛ R1) ∗ ((S + 312#64) ↦ₛ R2) ∗ ((S + 352#64) ↦ₛ q40 E 3) ∗ (memRegion (S - BitVec.ofNat 64 224) 224) ∗ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N1) ∗ (memRegion (S - 912#64) 688) ∗ (F) := Satisfies.of_eq hm5
  -- 512: add x8, x24, #120
  refine y_addi_r (d := 8#5) (a := 24#5) (by decide) (by decide) (pcA _ _ _ (516#64) (by decide)) hrun5 (c13_512 hP hCL 13 kfc5) ?_
  refine Reach.absR (fun r22 hn22 hw22 => ?_)
  have e20_22 : r22 20#5 = table := (hn22 _ (by decide)).trans e20_c5
  have e21_22 : r22 21#5 = S + 232#64 := (hn22 _ (by decide)).trans e21_c5
  have e22_22 : r22 22#5 = S + 392#64 := (hn22 _ (by decide)).trans e22_c5
  have e23_22 : r22 23#5 = BitVec.ofNat 64 (2 * i) := (hn22 _ (by decide)).trans e23_c5
  have e24_22 : r22 24#5 = S + 232#64 := (hn22 _ (by decide)).trans e24_c5
  have e25_22 : r22 25#5 = 960#64 := (hn22 _ (by decide)).trans e25_c5
  have e26_22 : r22 26#5 = S := (hn22 _ (by decide)).trans e26_c5
  have e29_22 : r22 29#5 = S + 672#64 := (hn22 _ (by decide)).trans e29_c5
  have e8_22 : r22 8#5 = S + 352#64 := (by rw [hw22, e24_c5]; exact addK2 S 232 _ 352 (by decide))
  have kh22 : KeepHi r22 s.regs.regs := KeepHi.abs khc5 hn22 (by decide)
  clear hn22 hw22
  -- 516: add x0, sp, #392
  refine y_addi_sp (d := 0#5) (by decide) (pcA _ _ _ (520#64) (by decide)) hrun5 (c13_516 hP hCL 13 kfc5) ?_
  refine Reach.absR (fun r23 hn23 hw23 => ?_)
  have e8_23 : r23 8#5 = S + 352#64 := (hn23 _ (by decide)).trans e8_22
  have e20_23 : r23 20#5 = table := (hn23 _ (by decide)).trans e20_22
  have e21_23 : r23 21#5 = S + 232#64 := (hn23 _ (by decide)).trans e21_22
  have e22_23 : r23 22#5 = S + 392#64 := (hn23 _ (by decide)).trans e22_22
  have e23_23 : r23 23#5 = BitVec.ofNat 64 (2 * i) := (hn23 _ (by decide)).trans e23_22
  have e24_23 : r23 24#5 = S + 232#64 := (hn23 _ (by decide)).trans e24_22
  have e25_23 : r23 25#5 = 960#64 := (hn23 _ (by decide)).trans e25_22
  have e26_23 : r23 26#5 = S := (hn23 _ (by decide)).trans e26_22
  have e29_23 : r23 29#5 = S + 672#64 := (hn23 _ (by decide)).trans e29_22
  have e0_23 : r23 0#5 = S + 392#64 := (hw23.trans (addK S _ 392 (by decide)))
  have kh23 : KeepHi r23 s.regs.regs := KeepHi.abs kh22 hn23 (by decide)
  clear hn23 hw23
  -- 520: add x1, x22, #40
  refine y_addi_r (d := 1#5) (a := 22#5) (by decide) (by decide) (pcA _ _ _ (524#64) (by decide)) hrun5 (c13_520 hP hCL 13 kfc5) ?_
  refine Reach.absR (fun r24 hn24 hw24 => ?_)
  have e0_24 : r24 0#5 = S + 392#64 := (hn24 _ (by decide)).trans e0_23
  have e8_24 : r24 8#5 = S + 352#64 := (hn24 _ (by decide)).trans e8_23
  have e20_24 : r24 20#5 = table := (hn24 _ (by decide)).trans e20_23
  have e21_24 : r24 21#5 = S + 232#64 := (hn24 _ (by decide)).trans e21_23
  have e22_24 : r24 22#5 = S + 392#64 := (hn24 _ (by decide)).trans e22_23
  have e23_24 : r24 23#5 = BitVec.ofNat 64 (2 * i) := (hn24 _ (by decide)).trans e23_23
  have e24_24 : r24 24#5 = S + 232#64 := (hn24 _ (by decide)).trans e24_23
  have e25_24 : r24 25#5 = 960#64 := (hn24 _ (by decide)).trans e25_23
  have e26_24 : r24 26#5 = S := (hn24 _ (by decide)).trans e26_23
  have e29_24 : r24 29#5 = S + 672#64 := (hn24 _ (by decide)).trans e29_23
  have e1_24 : r24 1#5 = S + 432#64 := (by rw [hw24, e22_23]; exact addK2 S 392 _ 432 (by decide))
  have kh24 : KeepHi r24 s.regs.regs := KeepHi.abs kh23 hn24 (by decide)
  clear hn24 hw24
  -- 524: bl
  refine y_bl (add_sub_cancel' _ _) (pcA _ _ _ (528#64) (by decide)) hrun5 (c13_524 hP hCL 13 kfc5 lk_mul) ?_
  refine Reach.absR (fun r25 hn25 hw25 => ?_)
  have e0_25 : r25 0#5 = S + 392#64 := (hn25 _ (by decide)).trans e0_24
  have e1_25 : r25 1#5 = S + 432#64 := (hn25 _ (by decide)).trans e1_24
  have e8_25 : r25 8#5 = S + 352#64 := (hn25 _ (by decide)).trans e8_24
  have e20_25 : r25 20#5 = table := (hn25 _ (by decide)).trans e20_24
  have e21_25 : r25 21#5 = S + 232#64 := (hn25 _ (by decide)).trans e21_24
  have e22_25 : r25 22#5 = S + 392#64 := (hn25 _ (by decide)).trans e22_24
  have e23_25 : r25 23#5 = BitVec.ofNat 64 (2 * i) := (hn25 _ (by decide)).trans e23_24
  have e24_25 : r25 24#5 = S + 232#64 := (hn25 _ (by decide)).trans e24_24
  have e25_25 : r25 25#5 = 960#64 := (hn25 _ (by decide)).trans e25_24
  have e26_25 : r25 26#5 = S := (hn25 _ (by decide)).trans e26_24
  have e29_25 : r25 29#5 = S + 672#64 := (hn25 _ (by decide)).trans e29_24
  have e30_25 : r25 30#5 = mpl.base 13 + 528#64 := hw25
  have kh25 : KeepHi r25 s.regs.regs := KeepHi.abs kh24 hn25 (by decide)
  clear hn25 hw25
  refine call_mul hP rfl hrun5 hal (libCodeLoaded_keepsFrozen hCL kfc5) e8_25 e0_25 e1_25 (q40_length E hE 3 (by decide)) hc0 hc1 (Satisfies.of_eq hm5 (Q := ((S + 392#64) ↦ₛ q40 Cr 0) ∗ ((S + 432#64) ↦ₛ q40 Cr 1) ∗ ((S + 352#64) ↦ₛ q40 E 3) ∗ (memRegion (S - BitVec.ofNat 64 224) 224) ∗ ((S + 472#64) ↦ₛ q40 Cr 2) ∗ ((S + 512#64) ↦ₛ q40 Cr 3) ∗ ((S + 232#64) ↦ₛ R0) ∗ ((S + 272#64) ↦ₛ R1) ∗ ((S + 312#64) ↦ₛ R2) ∗ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N1) ∗ (memRegion (S - 912#64) 688) ∗ (F))) ?_
  intro sf6 R3 hrun6 hsp6 hcs6 hv6 hm6 hkf6 hRb6 hRv6
  rw [e30_25]
  have e20_c6 : sf6.regs.regs 20#5 = table := (hcs6.2.1).trans e20_25
  have e21_c6 : sf6.regs.regs 21#5 = S + 232#64 := (hcs6.2.2.1).trans e21_25
  have e22_c6 : sf6.regs.regs 22#5 = S + 392#64 := (hcs6.2.2.2.1).trans e22_25
  have e23_c6 : sf6.regs.regs 23#5 = BitVec.ofNat 64 (2 * i) := (hcs6.2.2.2.2.1).trans e23_25
  have e24_c6 : sf6.regs.regs 24#5 = S + 232#64 := (hcs6.2.2.2.2.2.1).trans e24_25
  have e25_c6 : sf6.regs.regs 25#5 = 960#64 := (hcs6.2.2.2.2.2.2.1).trans e25_25
  have e26_c6 : sf6.regs.regs 26#5 = S := (hcs6.2.2.2.2.2.2.2.1).trans e26_25
  have e29_c6 : sf6.regs.regs 29#5 = S + 672#64 := (hcs6.2.2.2.2.2.2.2.2.2.2).trans e29_25
  have khc6 : KeepHi sf6.regs.regs s.regs.regs := KeepHi.cs hcs6 kh25
  have kfc6 : s.mem.KeepsFrozen sf6.mem := kfc5.trans hkf6
  have hvc6 : VRegFile.calleeSaved ⟨sf6.vregs.regs⟩ = VRegFile.calleeSaved s.vregs := hv6.trans hvc5
  clear hcs6 hkf6 hv6
  replace hm6 : sf6.mem ⊨ ((S + 392#64) ↦ₛ q40 Cr 0) ∗ ((S + 432#64) ↦ₛ q40 Cr 1) ∗ ((S + 472#64) ↦ₛ q40 Cr 2) ∗ ((S + 512#64) ↦ₛ q40 Cr 3) ∗ ((S + 232#64) ↦ₛ R0) ∗ ((S + 272#64) ↦ₛ R1) ∗ ((S + 312#64) ↦ₛ R2) ∗ ((S + 352#64) ↦ₛ R3) ∗ (memRegion (S - BitVec.ofNat 64 224) 224) ∗ (table ↦ᵣ T) ∗ (S ↦ₛ D) ∗ ((S + 64#64) ↦ₛ A) ∗ ((S + 552#64) ↦ₛ N1) ∗ (memRegion (S - 912#64) 688) ∗ (F) := Satisfies.of_eq hm6
  have hmX : sf6.mem ⊨ MulShape table T S D A N1 F (q40 Cr 0) (q40 Cr 1) (q40 Cr 2) (q40 Cr 3) R0 R1 R2 R3 := by
    unfold MulShape RM; exact Satisfies.of_eq hm6
  clear hm6
  have hmC := copy_in hA.1 hRb3.1 hRb4.1 hRb5.1 hRb6.1 hmX hCl
  clear hmX
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, hx⟩ := list20 (chunks64 (R0 ++ (R1 ++ (R2 ++ R3))) 20) (chunks64_length _ _)
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, ha⟩ := list20 (chunks64 A 20) (chunks64_length _ _)
  rw [hx, ha] at hmC
  -- 528: ldp q0, q1, [x21, #96]
  refine x_ldpq_w (t1 := 0#5) (t2 := 1#5) (k := 12) (lo1 := x12) (hi1 := x13) (lo2 := x14) (hi2 := x15) (by decide) hrun6 (c13_528 hP hCL 13 kfc6) (pcA _ _ _ (532#64) (by decide)) e21_c6 (by rfl) hmC (by simp) rfl rfl rfl rfl ?_
  have hvq0 := cs_upd (i := 1#5) (x := x15 ++ x14) (by decide) (cs_upd (i := 0#5) (x := x13 ++ x12) (by decide) hvc6)
  -- 532: add x23, x23, #1
  refine y_addi_r (d := 23#5) (a := 23#5) (by decide) (by decide) (pcA _ _ _ (536#64) (by decide)) hrun6 (c13_532 hP hCL 13 kfc6) ?_
  refine Reach.absR (fun r26 hn26 hw26 => ?_)
  have e20_26 : r26 20#5 = table := (hn26 _ (by decide)).trans e20_c6
  have e21_26 : r26 21#5 = S + 232#64 := (hn26 _ (by decide)).trans e21_c6
  have e22_26 : r26 22#5 = S + 392#64 := (hn26 _ (by decide)).trans e22_c6
  have e24_26 : r26 24#5 = S + 232#64 := (hn26 _ (by decide)).trans e24_c6
  have e25_26 : r26 25#5 = 960#64 := (hn26 _ (by decide)).trans e25_c6
  have e26_26 : r26 26#5 = S := (hn26 _ (by decide)).trans e26_c6
  have e29_26 : r26 29#5 = S + 672#64 := (hn26 _ (by decide)).trans e29_c6
  have e23_26 : r26 23#5 = BitVec.ofNat 64 (2 * i + 1) := (by rw [hw26, e23_c6, inc_even hi])
  have kh26 : KeepHi r26 s.regs.regs := KeepHi.abs khc6 hn26 (by decide)
  clear hn26 hw26
  -- 536: stp q0, q1, [sp, #160]
  refine x_stpq_w2 (k := 12) (lo1 := x12) (hi1 := x13) (lo2 := x14) (hi2 := x15) hal hrun6 (c13_536 hP hCL 13 kfc6) (pcA _ _ _ (540#64) (by decide)) (aadd S 64 (8 * 12) 160 rfl).symm hmC (by simp) (by simp) (by simp) ?_
  intro mq0 hmq0 hkq0
  simp only [List.set_cons_succ, List.set_cons_zero] at hmq0
  have kfq0 := kfc6.trans hkq0
  clear hmC hkq0
  -- 540: ldp q0, q2, [x21, #128]
  refine x_ldpq_w (t1 := 0#5) (t2 := 2#5) (k := 16) (lo1 := x16) (hi1 := x17) (lo2 := x18) (hi2 := x19) (by decide) hrun6 (c13_540 hP hCL 13 kfq0) (pcA _ _ _ (544#64) (by decide)) e21_26 (by rfl) hmq0 (by simp) rfl rfl rfl rfl ?_
  have hvq1 := cs_upd (i := 2#5) (x := x19 ++ x18) (by decide) (cs_upd (i := 0#5) (x := x17 ++ x16) (by decide) hvq0)
  -- 544: stp q0, q2, [sp, #192]
  refine x_stpq_w2 (k := 16) (lo1 := x16) (hi1 := x17) (lo2 := x18) (hi2 := x19) hal hrun6 (c13_544 hP hCL 13 kfq0) (pcA _ _ _ (548#64) (by decide)) (aadd S 64 (8 * 16) 192 rfl).symm hmq0 (by simp) (by simp) (by simp) ?_
  intro mq1 hmq1 hkq1
  simp only [List.set_cons_succ, List.set_cons_zero] at hmq1
  have kfq1 := kfq0.trans hkq1
  clear hmq0 hkq1
  -- 548: ldp q1, q0, [x21, #32]
  refine x_ldpq_w (t1 := 1#5) (t2 := 0#5) (k := 4) (lo1 := x4) (hi1 := x5) (lo2 := x6) (hi2 := x7) (by decide) hrun6 (c13_548 hP hCL 13 kfq1) (pcA _ _ _ (552#64) (by decide)) e21_26 (by rfl) hmq1 (by simp) rfl rfl rfl rfl ?_
  have hvq2 := cs_upd (i := 0#5) (x := x7 ++ x6) (by decide) (cs_upd (i := 1#5) (x := x5 ++ x4) (by decide) hvq1)
  -- 552: stp q1, q0, [sp, #96]
  refine x_stpq_w2 (k := 4) (lo1 := x4) (hi1 := x5) (lo2 := x6) (hi2 := x7) hal hrun6 (c13_552 hP hCL 13 kfq1) (pcA _ _ _ (556#64) (by decide)) (aadd S 64 (8 * 4) 96 rfl).symm hmq1 (by simp) (by simp) (by simp) ?_
  intro mq2 hmq2 hkq2
  simp only [List.set_cons_succ, List.set_cons_zero] at hmq2
  have kfq2 := kfq1.trans hkq2
  clear hmq1 hkq2
  -- 556: ldp q2, q0, [x21, #64]
  refine x_ldpq_w (t1 := 2#5) (t2 := 0#5) (k := 8) (lo1 := x8) (hi1 := x9) (lo2 := x10) (hi2 := x11) (by decide) hrun6 (c13_556 hP hCL 13 kfq2) (pcA _ _ _ (560#64) (by decide)) e21_26 (by rfl) hmq2 (by simp) rfl rfl rfl rfl ?_
  have hvq3 := cs_upd (i := 0#5) (x := x11 ++ x10) (by decide) (cs_upd (i := 2#5) (x := x9 ++ x8) (by decide) hvq2)
  -- 560: stp q2, q0, [sp, #128]
  refine x_stpq_w2 (k := 8) (lo1 := x8) (hi1 := x9) (lo2 := x10) (hi2 := x11) hal hrun6 (c13_560 hP hCL 13 kfq2) (pcA _ _ _ (564#64) (by decide)) (aadd S 64 (8 * 8) 128 rfl).symm hmq2 (by simp) (by simp) (by simp) ?_
  intro mq3 hmq3 hkq3
  simp only [List.set_cons_succ, List.set_cons_zero] at hmq3
  have kfq3 := kfq2.trans hkq3
  clear hmq2 hkq3
  -- 564: ldp q1, q0, [x21, #0]
  refine x_ldpq_w (t1 := 1#5) (t2 := 0#5) (k := 0) (lo1 := x0) (hi1 := x1) (lo2 := x2) (hi2 := x3) (by decide) hrun6 (c13_564 hP hCL 13 kfq3) (pcA _ _ _ (568#64) (by decide)) e21_26 (by rfl) hmq3 (by simp) rfl rfl rfl rfl ?_
  have hvq4 := cs_upd (i := 0#5) (x := x3 ++ x2) (by decide) (cs_upd (i := 1#5) (x := x1 ++ x0) (by decide) hvq3)
  -- 568: stp q1, q0, [sp, #64]
  refine x_stpq_w2 (k := 0) (lo1 := x0) (hi1 := x1) (lo2 := x2) (hi2 := x3) hal hrun6 (c13_568 hP hCL 13 kfq3) (pcA _ _ _ (572#64) (by decide)) (aadd S 64 (8 * 0) 64 rfl).symm hmq3 (by simp) (by simp) (by simp) ?_
  intro mq4 hmq4 hkq4
  simp only [List.set_cons_succ, List.set_cons_zero] at hmq4
  have kfq4 := kfq3.trans hkq4
  clear hmq3 hkq4
  rw [← hx] at hmq4
  have hXl : (R0 ++ (R1 ++ (R2 ++ R3))).length = 160 := by simp [hRb3.1, hRb4.1, hRb5.1, hRb6.1]
  have hmF := copy_out hXl hmq4
  have hval : fe51Point4Bounded (R0 ++ (R1 ++ (R2 ++ R3))) (2 ^ 52) ∧
      edExtOfBytes (R0 ++ (R1 ++ (R2 ++ R3))) = edAsExtended (edExtOfBytes Cr) :=
    edAsExtended_of_append4 R0 R1 R2 R3 (edExtOfBytes Cr) hRb3 hRb4 hRb5 hRb6
      (mul_val hRv3 (val_q40 Cr hCl 0 (by decide)) (val_q40 Cr hCl 3 (by decide)))
      (mul_val hRv4 (val_q40 Cr hCl 1 (by decide)) (val_q40 Cr hCl 2 (by decide)))
      (mul_val hRv5 (val_q40 Cr hCl 2 (by decide)) (val_q40 Cr hCl 3 (by decide)))
      (mul_val hRv6 (val_q40 Cr hCl 0 (by decide)) (val_q40 Cr hCl 1 (by decide)))
  -- 572: cmp x23, #64
  refine y_cmpi (n := 23#5) (by decide) (pcA _ _ _ (576#64) (by decide)) hrun6 (c13_572 hP hCL 13 kfq4) ?_
  -- 576: b.cond (taken)
  refine y_bcond_t (by rw [e23_26]; exact ne_odd hi) (pcA _ _ _ (416#64) (by decide)) hrun6 (c13_576 hP hCL 13 kfq4) ?_
  -- 416: tb(n)z w23, #0 (taken)
  refine y_tbz_t (n := 23#5) (by decide) (by rw [e23_26]; exact bit_odd hi) (pcA _ _ _ (404#64) (by decide)) hrun6 (c13_416 hP hCL 13 kfq4) ?_
  -- 404: add x23, x23, #1
  refine y_addi_r (d := 23#5) (a := 23#5) (by decide) (by decide) (pcA _ _ _ (408#64) (by decide)) hrun6 (c13_404 hP hCL 13 kfq4) ?_
  refine Reach.absR (fun r27 hn27 hw27 => ?_)
  have e20_27 : r27 20#5 = table := (hn27 _ (by decide)).trans e20_26
  have e21_27 : r27 21#5 = S + 232#64 := (hn27 _ (by decide)).trans e21_26
  have e22_27 : r27 22#5 = S + 392#64 := (hn27 _ (by decide)).trans e22_26
  have e24_27 : r27 24#5 = S + 232#64 := (hn27 _ (by decide)).trans e24_26
  have e25_27 : r27 25#5 = 960#64 := (hn27 _ (by decide)).trans e25_26
  have e26_27 : r27 26#5 = S := (hn27 _ (by decide)).trans e26_26
  have e29_27 : r27 29#5 = S + 672#64 := (hn27 _ (by decide)).trans e29_26
  have e23_27 : r27 23#5 = BitVec.ofNat 64 (2 * (i + 1)) := (by rw [hw27, e23_26, inc_odd hi])
  have kh27 : KeepHi r27 s.regs.regs := KeepHi.abs kh26 hn27 (by decide)
  clear hn27 hw27
  -- 408: cmp x23, #64
  refine y_cmpi (n := 23#5) (by decide) (pcA _ _ _ (412#64) (by decide)) hrun6 (c13_408 hP hCL 13 kfq4) ?_
  by_cases h31 : i = 31
  · subst h31
    rw [if_pos rfl]
    refine y_bcond_t (by rw [e23_27]; exact eq_last) (pcA _ _ _ (580#64) (by decide)) hrun6 (c13_412 hP hCL 13 kfq4) ?_
    refine Reach.done ⟨hrun6, rfl, rfl, e23_27, kh27, hvq4, _, _, _, _, hmF, hval.1, ?_, hXl, hCl, hN1⟩
    rw [hval.2, hCv]; unfold edMulBaseStep; rw [Nat.add_zero, ← hNv1]
  · rw [if_neg h31]
    refine y_bcond_f (by rw [e23_27]; exact eq_next (by omega)) (pcA _ _ _ (416#64) (by decide)) hrun6 (c13_412 hP hCL 13 kfq4) ?_
    refine Reach.done ⟨hrun6, rfl, rfl, e23_27, kh27, hvq4, _, _, _, _, hmF, hval.1, ?_, hXl, hCl, hN1⟩
    rw [hval.2, hCv]; unfold edMulBaseStep; rw [Nat.add_zero, ← hNv1]

end X25519Dalek.EMulB
end

section
/-! # Block 13: the even loop iteration as a `Steps` statement -/

set_option autoImplicit false

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem basepointTable_mul_base_even_iter_dev {mpl : Arm64.Obj.MultiPlacement}
    (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S table : BitVec 64} {i : Nat}
    {table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8)} {F : Arm64.SepProp}
    (hi : i < 32) (hrun : s.status = .Running) (hpc : s.pc = mpl.base 13 + 416#64) (hsp : s.sp = S)
    (hal : (S &&& 15#64) = 0#64)
    (h20 : s.regs.regs 20#5 = table)
    (h21 : s.regs.regs 21#5 = S + 232#64)
    (h22 : s.regs.regs 22#5 = S + 392#64)
    (h23 : s.regs.regs 23#5 = BitVec.ofNat 64 (2 * i))
    (h24 : s.regs.regs 24#5 = S + 232#64)
    (h25 : s.regs.regs 25#5 = 960#64)
    (h26 : s.regs.regs 26#5 = S)
    (h29 : s.regs.regs 29#5 = S + 672#64)
    (htab : fe51BasepointTable32Bounded table_bs (2 ^ 53)) (hdig : digits.length = 64)
    (hacc : fe51Point4Bounded acc_bs (2 ^ 52)) (hext : ext_bs.length = 160)
    (hcomp : comp_bs.length = 160) (hniels : niels_bs.length = 120)
    (hs : s.mem ⊨ (table ↦ᵣ table_bs) ∗ (S ↦ₛ digits) ∗ ((S + 64#64) ↦ₛ acc_bs) ∗
      ((S + 232#64) ↦ₛ ext_bs) ∗ ((S + 392#64) ↦ₛ comp_bs) ∗ ((S + 552#64) ↦ₛ niels_bs) ∗
      Arm64.memRegion (S - 912#64) 912 ∗ F) :
    ∃ s' : Arm64.State, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 13) s s' ∧
      s'.status = .Running ∧
      s'.pc = (if i = 31 then mpl.base 13 + 580#64 else mpl.base 13 + 416#64) ∧ s'.sp = S ∧
      s'.regs.regs 23#5 = BitVec.ofNat 64 (2 * (i + 1)) ∧
      (∀ k : BitVec 5, k ≠ 23#5 → 19 ≤ k.toNat → k.toNat < 30 → s'.regs.regs k = s.regs.regs k) ∧
      Arm64.VRegFile.calleeSaved s'.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ acc' ext' comp' niels' : List (BitVec 8),
        (s'.mem ⊨ (table ↦ᵣ table_bs) ∗ (S ↦ₛ digits) ∗ ((S + 64#64) ↦ₛ acc') ∗
          ((S + 232#64) ↦ₛ ext') ∗ ((S + 392#64) ↦ₛ comp') ∗ ((S + 552#64) ↦ₛ niels') ∗
          Arm64.memRegion (S - 912#64) 912 ∗ F) ∧
        fe51Point4Bounded acc' (2 ^ 52) ∧
        edExtOfBytes acc' = edMulBaseStep table_bs i (digits.getD (2 * i) 0#8) (edExtOfBytes acc_bs) ∧
        ext'.length = 160 ∧ comp'.length = 160 ∧ niels'.length = 120 := by
  have hs' : s.mem ⊨ MemI table table_bs S digits acc_bs ext_bs comp_bs niels_bs F := hs
  have e : mkS s s.pc s.regs.regs s.sp s.pstate s.mem s.vregs.regs = s := rfl
  rw [hpc, hsp] at e
  have h := even_reach hP hCL hi hrun hal h20 h21 h22 h23 h24 h25 h26 h29 htab hdig hacc hext hcomp hniels hs'
  rw [e] at h
  obtain ⟨s', hst, hrun', hpc', hsp', h23', hkh, hv, A', E', C', N', hm, hb, hval, hE, hC, hN⟩ := h
  exact ⟨s', hst, hrun', hpc', hsp', h23', fun k a b c => hkh k a b c, hv, A', E', C', N', hm, hb, hval, hE, hC, hN⟩

end X25519Dalek.EMulB
end

section
open X25519Dalek

theorem solution {mpl : Arm64.Obj.MultiPlacement}
    (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S table : BitVec 64} {i : Nat}
    {table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8)} {F : Arm64.SepProp}
    (hi : i < 32) (hrun : s.status = .Running) (hpc : s.pc = mpl.base 13 + 416#64) (hsp : s.sp = S)
    (hal : (S &&& 15#64) = 0#64)
    (h20 : s.regs.regs 20#5 = table)
    (h21 : s.regs.regs 21#5 = S + 232#64)
    (h22 : s.regs.regs 22#5 = S + 392#64)
    (h23 : s.regs.regs 23#5 = BitVec.ofNat 64 (2 * i))
    (h24 : s.regs.regs 24#5 = S + 232#64)
    (h25 : s.regs.regs 25#5 = 960#64)
    (h26 : s.regs.regs 26#5 = S)
    (h29 : s.regs.regs 29#5 = S + 672#64)
    (htab : fe51BasepointTable32Bounded table_bs (2 ^ 53)) (hdig : digits.length = 64)
    (hacc : fe51Point4Bounded acc_bs (2 ^ 52)) (hext : ext_bs.length = 160)
    (hcomp : comp_bs.length = 160) (hniels : niels_bs.length = 120)
    (hs : s.mem ⊨ (table ↦ᵣ table_bs) ∗ (S ↦ₛ digits) ∗ ((S + 64#64) ↦ₛ acc_bs) ∗
      ((S + 232#64) ↦ₛ ext_bs) ∗ ((S + 392#64) ↦ₛ comp_bs) ∗ ((S + 552#64) ↦ₛ niels_bs) ∗
      Arm64.memRegion (S - 912#64) 912 ∗ F) :
    ∃ s' : Arm64.State, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 13) s s' ∧
      s'.status = .Running ∧
      s'.pc = (if i = 31 then mpl.base 13 + 580#64 else mpl.base 13 + 416#64) ∧ s'.sp = S ∧
      s'.regs.regs 23#5 = BitVec.ofNat 64 (2 * (i + 1)) ∧
      (∀ k : BitVec 5, k ≠ 23#5 → 19 ≤ k.toNat → k.toNat < 30 → s'.regs.regs k = s.regs.regs k) ∧
      Arm64.VRegFile.calleeSaved s'.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ acc' ext' comp' niels' : List (BitVec 8),
        (s'.mem ⊨ (table ↦ᵣ table_bs) ∗ (S ↦ₛ digits) ∗ ((S + 64#64) ↦ₛ acc') ∗
          ((S + 232#64) ↦ₛ ext') ∗ ((S + 392#64) ↦ₛ comp') ∗ ((S + 552#64) ↦ₛ niels') ∗
          Arm64.memRegion (S - 912#64) 912 ∗ F) ∧
        fe51Point4Bounded acc' (2 ^ 52) ∧
        edExtOfBytes acc' = edMulBaseStep table_bs i (digits.getD (2 * i) 0#8) (edExtOfBytes acc_bs) ∧
        ext'.length = 160 ∧ comp'.length = 160 ∧ niels'.length = 120 :=
  X25519Dalek.EMulB.basepointTable_mul_base_even_iter_dev hP hCL hi hrun hpc hsp hal h20 h21 h22 h23 h24 h25 h26 h29 htab hdig hacc hext hcomp hniels hs

end
