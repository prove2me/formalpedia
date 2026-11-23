-- Prove2me | solution 1 for X25519Dalek.fnOk_projectivePoint_as_affine
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T14:59:07.95948+00:00
-- url     : https://prove2.me/submissions/21002c46-a7ad-480d-bf26-252ed727e628

import Definitions.Def_X25519Dalek_PlacedObj
import Definitions.Def_X25519Dalek_Rfc7748
import Definitions.Def_X25519Dalek_Spec
import Theorems.Thm_X25519Dalek_steps_keepsFrozen
import Theorems.Thm_X25519Dalek_fnOk_fe51_mul
import Theorems.Thm_X25519Dalek_fnOk_fe51_pow2k
import Theorems.Thm_X25519Dalek_fnOk_fe51_pow22501
import Theorems.Thm_X25519Dalek_projectivePoint_as_affine_tail
import Mathlib

section
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
end

section
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
end

section
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
end

section
section
/-! # 64-bit cells and byte reads: values and permissions from ownership -/

set_option autoImplicit false

namespace Arm64

theorem concat8_extract (v : BitVec 64) :
    v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 32 8 ++
      v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

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
end

section
section
/-! # Instruction fetch in the placed x25519 library, and execution by backward chaining

`Step` does not depend on which block's program runs it when no hooks are installed, so a callee's
contract (stated for its own block) is usable from the caller's block. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

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
  interval_cases i <;> simp

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

end X25519Dalek.LP

end
end

section
section
/-! # Abstract machine states

Every state inside a block proof is `mkS s0 pc r sp ps m v`: the state `s0` with the program
counter, the general registers, the stack pointer, the flags, the memory and the vector registers
replaced. The instruction evaluators map such states to such states, and these lemmas let `simp`
compute the result without unfolding `State`. -/

set_option autoImplicit false

namespace X25519Dalek.LP

open Arm64

def upd {α : Type} (r : BitVec 5 → α) (i : BitVec 5) (v : α) : BitVec 5 → α :=
  fun j => if j = i then v else r j

@[simp] theorem upd_same {α : Type} (r : BitVec 5 → α) (i : BitVec 5) (v : α) : upd r i v i = v := by
  simp [upd]

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

end X25519Dalek.LP

end
end

section
section
/-! # Code stays loaded; stepping on abstract states; small stack frames -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

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

theorem unpack64_pack64 (l : List (BitVec 8)) (h : l.length = 8) : unpack64 (pack64 l) = l := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    simp only [pack64, unpack64, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq,
      and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
      interval_cases i <;> simp

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

/-- Focus-free consequences of owning one 64-bit cell at the head. -/
theorem cell_write {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F)
    (w : BitVec 64) :
    m.canWrite a 8 = true ∧ m.KeepsFrozen (m.write64 a w) ∧ (m.write64 a w ⊨ (a ↦₆₄ w) ∗ F) := by
  have h := sat64_read hs
  exact ⟨h.2.2, keepsFrozen_write64_of_rw (fun i hi => (sat64_byte hs i hi).2.1) w, sat64_write hs w⟩

end X25519Dalek.LP

end
end

section
section
/-! # Arithmetic facts for the instruction evaluators and byte encodings -/

set_option autoImplicit false

namespace X25519Dalek.LP

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

end X25519Dalek.LP

namespace X25519Dalek.LP
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

end X25519Dalek.LP

end
end

section
section
/-! # Relocated `BL` words and calls to other blocks -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

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
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem lo_bits2 (D : BitVec 64) (h : D.toNat % 4 = 0) : ∀ i, i < 2 → D.getLsbD i = false := by
  intro i hi
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize D.toNat = n at h ⊢
  interval_cases i <;> simp <;> omega

theorem bw_mask (D : BitVec 64) :
    ((0x94000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32)) &&&
      0xfc000000#32 = 0x94000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  interval_cases i <;> simp

theorem bw_off (D : BitVec 64) (hlo : ∀ i, i < 2 → D.getLsbD i = false)
    (hhi : ∀ i, 27 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 27) :
    ((((0x94000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32))).extractLsb' 0 26).signExtend 64 <<< 2 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.msb, BitVec.getMsbD]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | exact (hlo _ (by omega)).symm | exact hlo _ (by omega) | rfl |
      exact (hhi _ (by omega) (by omega)).symm | exact hhi _ (by omega) (by omega)

/-- A relocated `bl` decodes to a branch-with-link whose offset reaches the target, when the
target is in range. -/
theorem decode_branchWord (place target : BitVec 64) (h : BranchInRange place target) :
    decode (branchWord 0x94000000#32 place target) = some (.bl (target - place)) := by
  unfold branchWord
  rw [decode_bl_class _ (bw_mask _)]
  congr 2
  exact bw_off _ (lo_bits2 _ h.1) (hi_bits27 _ h.2.1 h.2.2)

end X25519Dalek.LP

namespace X25519Dalek.LP

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

end X25519Dalek.LP

namespace X25519Dalek.LP

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
  have hkf := X25519Dalek.steps_keepsFrozen hst
  have hst' : Steps (bprog mpl k) s sf := bsteps_transfer (i := j) hst
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨_, hp⟩ | ⟨c, _, hp⟩ | ⟨_, hp⟩
  · exact Reach.steps hst' (hcont sf hpcf hspf hrunf hcs hpost hkf)
  · exact absurd hp (hpanic sf)
  · exact absurd hp (hexit c sf)
  · exact absurd hp (hoom sf)

theorem not_sat_false {m : Memory} {R : SepProp} : ¬ (m ⊨ (⌜False⌝ : SepProp) ∗ R) := by
  rw [sat_pure_sep]; exact fun h => h.1

end X25519Dalek.LP

end
end

section
section
/-! # Stack frames as lists of 64-bit words

`a ↦₆₄* ws` owns the words `ws` at `a, a + 8, …`; indexed reads and writes; conversions to and
from byte slices and `memRegion`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

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

theorem memRegion_words (a : BitVec 64) (k : Nat) (hk : 8 * k < 2 ^ 64) :
    memRegion a (8 * k) ⊢ ∃∗ ws, ⌜ws.length = k⌝ ∗ (a ↦₆₄* ws) := by
  intro h hh
  obtain ⟨bs, hb⟩ := memRegion_entails_bytes a (8 * k) hk h hh
  obtain ⟨hl, hb⟩ := pure_sepConj_holds.mp hb
  refine ⟨chunks64 bs k, pure_sepConj_holds.mpr ⟨chunks64_length bs k, ?_⟩⟩
  rw [words_eq_bytes, chunks64_flat k bs hl]
  exact hb

end X25519Dalek.LP

namespace X25519Dalek.LP
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

theorem sat_words_access {m : Memory} {a : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (k n : Nat) (h : k + n ≤ 8 * ws.length) :
    m.canRead (a + BitVec.ofNat 64 k) n = true ∧ m.canWrite (a + BitVec.ofNat 64 k) n = true := by
  rw [words_eq_bytes] at hs
  exact sat_bytes_access hs k n (by rw [flatMap_unpack64_length]; exact h)

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

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem zext12_lit (n : Nat) : BitVec.zeroExtend 64 (BitVec.ofNat 12 n) = BitVec.ofNat 64 (n % 4096) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

theorem zext16_lit (n : Nat) : BitVec.zeroExtend 64 (BitVec.ofNat 16 n) = BitVec.ofNat 64 (n % 65536) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

@[simp] theorem bf_beq_1 : (BitfieldOp.BFM == BitfieldOp.UBFM) = false := by decide
@[simp] theorem bf_beq_2 : (BitfieldOp.BFM == BitfieldOp.SBFM) = false := by decide
@[simp] theorem bf_beq_3 : (BitfieldOp.UBFM == BitfieldOp.SBFM) = false := by decide
@[simp] theorem bf_beq_4 : (BitfieldOp.SBFM == BitfieldOp.UBFM) = false := by decide
@[simp] theorem bf_beq_5 : (BitfieldOp.UBFM == BitfieldOp.UBFM) = true := by decide
@[simp] theorem bf_beq_6 : (BitfieldOp.SBFM == BitfieldOp.SBFM) = true := by decide

end X25519Dalek.LP

namespace X25519Dalek.LP
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

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem add_sub_cancel' (a b : BitVec 64) : a + (b - a) = b := by bv_omega
theorem sub_add_cancel' (a : BitVec 64) (k : Nat) : a - BitVec.ofNat 64 k + BitVec.ofNat 64 k = a := by
  bv_omega

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP
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

theorem memRegion_words' (a : BitVec 64) (k : Nat) (hk : 8 * k < 2 ^ 64) {m : Memory} {F : SepProp}
    (hs : m ⊨ memRegion a (8 * k) ∗ F) : ∃ ws, ws.length = k ∧ (m ⊨ (a ↦₆₄* ws) ∗ F) := by
  have h := sat_sep_mono hs (memRegion_words a k hk)
  rw [sepExists_sepConj, sat_sepExists] at h
  obtain ⟨ws, h⟩ := h
  rw [sepConj_assoc, sat_pure_sep] at h
  exact ⟨ws, h.1, h.2⟩

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem addr_sub_add (x : BitVec 64) (a b : Nat) (hb : b < 2 ^ 64) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b = x - BitVec.ofNat 64 ((a + (2 ^ 64 - b)) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem addr_sub_sub (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 ((a + b) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem sat_mr_split {m : Memory} {a : BitVec 64} {F : SepProp} (n k : Nat) (h : n + k < 2 ^ 64)
    (b : BitVec 64) (hb : a + BitVec.ofNat 64 n = b) (hs : m ⊨ memRegion a (n + k) ∗ F) :
    m ⊨ memRegion a n ∗ memRegion b k ∗ F := by
  have := sat_sep_mono hs (memRegion_split a n k h)
  rw [sepConj_assoc, hb] at this; exact this

end X25519Dalek.LP

namespace X25519Dalek.LP

theorem list6 {α : Type} (l : List α) (h : l.length = 6) :
    ∃ a b c d e f, l = [a, b, c, d, e, f] := by
  match l, h with
  | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩

end X25519Dalek.LP

namespace X25519Dalek.LP
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

end X25519Dalek.LP

namespace X25519Dalek.LP
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

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem sat_pre3 {m : Memory} {φ : Prop} {A B C F : SepProp} (hφ : φ) (hs : m ⊨ A ∗ B ∗ C ∗ F) :
    m ⊨ (⌜φ⌝ ∗ A ∗ B ∗ C) ∗ F := by
  rw [sepConj_assoc, sat_pure_sep]; exact ⟨hφ, by simpa only [sepConj_assoc] using hs⟩

theorem sat_pre4 {m : Memory} {φ : Prop} {A B C D F : SepProp} (hφ : φ) (hs : m ⊨ A ∗ B ∗ C ∗ D ∗ F) :
    m ⊨ (⌜φ⌝ ∗ A ∗ B ∗ C ∗ D) ∗ F := by
  rw [sepConj_assoc, sat_pure_sep]; exact ⟨hφ, by simpa only [sepConj_assoc] using hs⟩

end X25519Dalek.LP

namespace X25519Dalek.LP
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

end X25519Dalek.LP

namespace X25519Dalek.LP
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

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem sat_mr_bytes {m : Memory} {a b : BitVec 64} {bs : List (BitVec 8)} {F : SepProp} (n : Nat)
    (hn : n < 2 ^ 64) (hb : b = a + BitVec.ofNat 64 n) (hs : m ⊨ memRegion a n ∗ (b ↦ₛ bs) ∗ F) :
    m ⊨ memRegion a (n + bs.length) ∗ F := by
  subst hb
  rw [← sepConj_assoc] at hs
  exact sat_sep_mono hs (memRegion_append a n bs hn)

end X25519Dalek.LP

namespace X25519Dalek.LP

theorem addr_eq (x : BitVec 64) (a b n : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : b = a + n) :
    x - BitVec.ofNat 64 a = x - BitVec.ofNat 64 b + BitVec.ofNat 64 n := by
  subst h; bv_omega

end X25519Dalek.LP

end
end

section
section
/-! # Block 11: per-offset instruction fetch (generated by tools_ladder/gen_code.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

abbrev callee11_0 : String := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul"

abbrev callee11_1 : String := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501"

abbrev callee11_2 : String := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k"

theorem blk11 : blk 11 = x25519CliBlk11 := rfl

theorem len11 : x25519CliBlk11.code.length = 520 := by decide +kernel

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (j : Nat) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem c11_0 : (bprog mpl j).fetchMem m (mpl.base 11) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.sp) (Reg.sp) 0x110#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 0) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.sp) (Reg.sp) 0x110#12 false)) (by decide) rfl (by decide +kernel) hk
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

theorem c11_4 : (bprog mpl j).fetchMem m (mpl.base 11 + 4#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.Offset (Reg.sp) 0x00000000000000e0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 4) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.Offset (Reg.sp) 0x00000000000000e0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_8 : (bprog mpl j).fetchMem m (mpl.base 11 + 8#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1c#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x00000000000000f0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 8) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x1c#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x00000000000000f0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_12 : (bprog mpl j).fetchMem m (mpl.base 11 + 12#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000100#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 12) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000100#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_16 : (bprog mpl j).fetchMem m (mpl.base 11 + 16#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1d#5) (Reg.sp) 0x0e0#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 16) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1d#5) (Reg.sp) 0x0e0#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_20 : (bprog mpl j).fetchMem m (mpl.base 11 + 20#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x14#5) (Reg.xzr) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 20) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x14#5) (Reg.xzr) (Reg.gpr 0x00#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_24 : (bprog mpl j).fetchMem m (mpl.base 11 + 24#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x00#5) (Reg.gpr 0x1d#5) 0x050#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 24) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x00#5) (Reg.gpr 0x1d#5) 0x050#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_28 : (bprog mpl j).fetchMem m (mpl.base 11 + 28#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x13#5) (Reg.xzr) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 28) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x13#5) (Reg.xzr) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_32 : (bprog mpl j).fetchMem m (mpl.base 11 + 32#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.gpr 0x14#5) 0x028#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 32) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.gpr 0x14#5) 0x028#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_36 : (bprog mpl j).fetchMem m (mpl.base 11 + 36#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x15#5) (Reg.gpr 0x1d#5) 0x050#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 36) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x15#5) (Reg.gpr 0x1d#5) 0x050#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_44 : (bprog mpl j).fetchMem m (mpl.base 11 + 44#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000000#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 44) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x15#5) 0x0000000000000000#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_48 : (bprog mpl j).fetchMem m (mpl.base 11 + 48#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x030#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 48) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x030#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_52 : (bprog mpl j).fetchMem m (mpl.base 11 + 52#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x08#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffd0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 52) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x08#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffd0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_56 : (bprog mpl j).fetchMem m (mpl.base 11 + 56#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x09#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xfffffffffffffff8#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 56) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x09#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xfffffffffffffff8#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_60 : (bprog mpl j).fetchMem m (mpl.base 11 + 60#64) =
    some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x01#5) 0x0005#16 0) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 60) (inst := (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x01#5) 0x0005#16 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_64 : (bprog mpl j).fetchMem m (mpl.base 11 + 64#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x0000000000000030#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 64) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x0000000000000030#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_68 : (bprog mpl j).fetchMem m (mpl.base 11 + 68#64) =
    some (Instr.ldrSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x15#5) 0x0000000000000028#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 68) (inst := (Instr.ldrSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x15#5) 0x0000000000000028#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_72 : (bprog mpl j).fetchMem m (mpl.base 11 + 72#64) =
    some (Instr.ldrSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.UnscaledOffset (Reg.gpr 0x15#5) 0x0000000000000038#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 72) (inst := (Instr.ldrSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.UnscaledOffset (Reg.gpr 0x15#5) 0x0000000000000038#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_76 : (bprog mpl j).fetchMem m (mpl.base 11 + 76#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 76) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_80 : (bprog mpl j).fetchMem m (mpl.base 11 + 80#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x1d#5) 0x050#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 80) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x1d#5) 0x050#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_84 : (bprog mpl j).fetchMem m (mpl.base 11 + 84#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x0000000000000060#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 84) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x0000000000000060#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_88 : (bprog mpl j).fetchMem m (mpl.base 11 + 88#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x0000000000000080#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 88) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x0000000000000080#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_96 : (bprog mpl j).fetchMem m (mpl.base 11 + 96#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.sp) 0x008#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 96) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.sp) 0x008#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_100 : (bprog mpl j).fetchMem m (mpl.base 11 + 100#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x00#5) (Reg.gpr 0x1d#5) 0x050#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 100) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x00#5) (Reg.gpr 0x1d#5) 0x050#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_104 : (bprog mpl j).fetchMem m (mpl.base 11 + 104#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.sp) 0x060#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 104) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.sp) 0x060#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_112 : (bprog mpl j).fetchMem m (mpl.base 11 + 112#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x1d#5) 0x050#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 112) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x1d#5) 0x050#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_116 : (bprog mpl j).fetchMem m (mpl.base 11 + 116#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.sp) 0x008#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 116) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.sp) 0x008#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_120 : (bprog mpl j).fetchMem m (mpl.base 11 + 120#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x00#5) (Reg.xzr) (Reg.gpr 0x14#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 120) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x00#5) (Reg.xzr) (Reg.gpr 0x14#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_40 {j' offj : Nat} (hlk : lookupBlockSym callee11_1 x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 11 + 40#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 11 + BitVec.ofNat 64 40))) :=
  fetch_bl hP hCL (i := 11) (by decide) j (off := 40) (name := callee11_1) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c11_92 {j' offj : Nat} (hlk : lookupBlockSym callee11_2 x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 11 + 92#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 11 + BitVec.ofNat 64 92))) :=
  fetch_bl hP hCL (i := 11) (by decide) j (off := 92) (name := callee11_2) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c11_108 {j' offj : Nat} (hlk : lookupBlockSym callee11_0 x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 11 + 108#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 11 + BitVec.ofNat 64 108))) :=
  fetch_bl hP hCL (i := 11) (by decide) j (off := 108) (name := callee11_0) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c11_124 {j' offj : Nat} (hlk : lookupBlockSym callee11_0 x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 11 + 124#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 11 + BitVec.ofNat 64 124))) :=
  fetch_bl hP hCL (i := 11) (by decide) j (off := 124) (name := callee11_0) (by decide +kernel)
    (by decide +kernel) hlk hk

end

end X25519Dalek.LP

end
end

section
section
/-! # `FieldElement51` buffers: limbs, words, values -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64

theorem cat8_eq_or (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 =
      0#64 ||| b0.zeroExtend 64 <<< 0 ||| b1.zeroExtend 64 <<< 8 ||| b2.zeroExtend 64 <<< 16 |||
      b3.zeroExtend 64 <<< 24 ||| b4.zeroExtend 64 <<< 32 ||| b5.zeroExtend 64 <<< 40 |||
      b6.zeroExtend 64 <<< 48 ||| b7.zeroExtend 64 <<< 56 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  interval_cases i <;> simp only [BitVec.getLsbD_append] <;> simp

theorem readLE8_eq (bs : List (BitVec 8)) (off : Nat) :
    ByteSlice.readLE bs off 8 =
      bs.getD (off + 7) 0 ++ bs.getD (off + 6) 0 ++ bs.getD (off + 5) 0 ++ bs.getD (off + 4) 0 ++
      bs.getD (off + 3) 0 ++ bs.getD (off + 2) 0 ++ bs.getD (off + 1) 0 ++ bs.getD (off + 0) 0 := by
  rw [cat8_eq_or]
  simp only [ByteSlice.readLE, Nat.reduceMul, Nat.add_zero]
  rfl

theorem pack64_drop_take (bs : List (BitVec 8)) (off : Nat) :
    pack64 ((bs.drop off).take 8) = ByteSlice.readLE bs off 8 := by
  rw [readLE8_eq]
  simp only [pack64, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  simp

theorem readLE_drop (bs : List (BitVec 8)) (k off : Nat) :
    ByteSlice.readLE (bs.drop k) off 8 = ByteSlice.readLE bs (k + off) 8 := by
  rw [readLE8_eq, readLE8_eq]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_assoc]

theorem chunks64_getElem : ∀ (k : Nat) (bs : List (BitVec 8)) (i : Nat) (hi : i < (chunks64 bs k).length),
    (chunks64 bs k)[i] = ByteSlice.readLE bs (8 * i) 8
  | 0, _, i, hi => by simp [chunks64] at hi
  | k + 1, bs, 0, _ => by
    simp only [chunks64, List.getElem_cons_zero]
    rw [← pack64_drop_take]; rfl
  | k + 1, bs, i + 1, hi => by
    rw [chunks64_length] at hi
    simp only [chunks64, List.getElem_cons_succ]
    rw [chunks64_getElem k (bs.drop 8) i (by rw [chunks64_length]; omega), readLE_drop]
    congr 1; omega

theorem readLE_take (bs : List (BitVec 8)) (n off : Nat) (h : off + 8 ≤ n) :
    ByteSlice.readLE (bs.take n) off 8 = ByteSlice.readLE bs off 8 := by
  rw [readLE8_eq, readLE8_eq]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  repeat rw [if_pos (by omega)]

theorem montProj_take40 (bs : List (BitVec 8)) (B : Nat) (h : montProjBounded bs B) :
    fe51LimbsBounded (bs.take 40) B ∧ fe51ValOfBytes (bs.take 40) % p25519 = (montProjOfBytes bs).U := by
  obtain ⟨hlen, ⟨h0, h8, h16, h24, h32⟩, _⟩ := h
  unfold fe51LimbsBounded fe51ValOfBytes montProjOfBytes montFe51ValAt fe51ValAt
  rw [readLE_take bs 40 0 (by omega), readLE_take bs 40 8 (by omega), readLE_take bs 40 16 (by omega),
    readLE_take bs 40 24 (by omega), readLE_take bs 40 32 (by omega)]
  exact ⟨⟨by simp [hlen], h0, h8, h16, h24, h32⟩, rfl⟩

theorem montProj_drop40 (bs : List (BitVec 8)) (B : Nat) (h : montProjBounded bs B) :
    fe51LimbsBounded (bs.drop 40) B ∧ fe51ValOfBytes (bs.drop 40) % p25519 = (montProjOfBytes bs).W := by
  obtain ⟨hlen, _, ⟨h0, h8, h16, h24, h32⟩⟩ := h
  unfold fe51LimbsBounded fe51ValOfBytes montProjOfBytes montFe51ValAt fe51ValAt
  rw [readLE_drop bs 40 0, readLE_drop bs 40 8, readLE_drop bs 40 16, readLE_drop bs 40 24,
    readLE_drop bs 40 32]
  exact ⟨⟨by simp [hlen], h0, h8, h16, h24, h32⟩, rfl⟩

theorem fe51LimbsBounded_mono {bs : List (BitVec 8)} {b1 b2 : Nat} (h : fe51LimbsBounded bs b1)
    (hb : b1 ≤ b2) : fe51LimbsBounded bs b2 := by
  obtain ⟨hl, h0, h1, h2, h3, h4⟩ := h
  exact ⟨hl, by omega, by omega, by omega, by omega, by omega⟩

/-! ## Field arithmetic -/

theorem modPowLoop_eq (fuel : Nat) :
    ∀ (base exp m acc : Nat), exp < 2 ^ fuel → modPowLoop fuel base exp m acc = (acc * base ^ exp) % m := by
  induction fuel with
  | zero => intro base exp m acc hexp; (have h0 : exp = 0 := by omega); subst h0; simp [modPowLoop]
  | succ fuel ih =>
    intro base exp m acc hexp; unfold modPowLoop
    by_cases h0 : exp = 0
    · subst h0; simp
    · have hne : (exp == 0) = false := beq_false_of_ne h0
      have hdiv : exp / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hexp; omega
      rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hsq : ((base * base) % m) ^ (exp / 2) % m = base ^ (2 * (exp / 2)) % m := by
        rw [← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      rcases Nat.mod_two_eq_zero_or_one exp with heven | hodd
      · have hmod : (exp % 2 == 1) = false := by rw [heven]; rfl
        rw [hmod]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod, hsq, show 2 * (exp / 2) = exp by omega, ← Nat.mul_mod]
      · have hmod : (exp % 2 == 1) = true := by rw [hodd]; rfl
        rw [hmod]; simp only [↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod ((acc * base) % m), Nat.mod_mod, hsq, ← Nat.mul_mod,
            Nat.mul_assoc acc, ← Nat.pow_succ', show (2 * (exp / 2)).succ = exp by omega]

theorem fpPow_eq_pow_mod (a e : Nat) (he : e < 2 ^ 256) : fpPow a e = a ^ e % p25519 := by
  unfold fpPow modPow
  rw [modPowLoop_eq 256 (a % p25519) e p25519 1 he, Nat.one_mul, ← Nat.pow_mod]

theorem fpPow_mod_eq_pow_mod (a e : Nat) (he : e < 2 ^ 256) :
    fpPow (a % p25519) e = a ^ e % p25519 := by
  unfold fpPow modPow
  rw [Nat.mod_mod, modPowLoop_eq 256 (a % p25519) e p25519 1 he, Nat.one_mul, ← Nat.pow_mod a e p25519]

theorem mul_mod_eq_fpMul (a b : Nat) :
    (a * b) % p25519 = fpMul (a % p25519) (b % p25519) := by
  unfold fpMul
  rw [Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem compress_recip_eq_fpInv (z t19 t3 t2_5 recip : Nat)
    (ht19 : t19 % p25519 = fpPow (z % p25519) (2 ^ 250 - 1))
    (ht3 : t3 % p25519 = fpPow (z % p25519) 11)
    (ht2_5 : t2_5 % p25519 = fpPow (t19 % p25519) (2 ^ 5))
    (hrecip : recip % p25519 = (t2_5 * t3) % p25519) :
    recip % p25519 = fpInv (z % p25519) := by
  unfold fpInv
  have h1 : 2 ^ 250 - 1 < 2 ^ 256 := by decide +kernel
  have h2 : 11 < 2 ^ 256 := by decide +kernel
  have h3 : 2 ^ 5 < 2 ^ 256 := by decide +kernel
  have h4 : p25519 - 2 < 2 ^ 256 := by decide +kernel
  have heq : (2 ^ 250 - 1) * (2 ^ 5) + 11 = p25519 - 2 := by decide +kernel
  generalize (2 ^ 250 - 1) = e1 at ht19 h1 heq
  generalize (11 : Nat) = e2 at ht3 h2 heq
  generalize (2 ^ 5) = e3 at ht2_5 h3 heq
  generalize (p25519 - 2) = e4 at h4 heq ⊢
  rw [hrecip, Nat.mul_mod, ht2_5, ht3, ht19, fpPow_eq_pow_mod _ _ h3, fpPow_mod_eq_pow_mod _ _ h1,
      fpPow_mod_eq_pow_mod _ _ h2, fpPow_mod_eq_pow_mod _ _ h4,
      ← Nat.pow_mod, ← Nat.pow_mul, ← Nat.mul_mod, ← Nat.pow_add, heq]

theorem as_affine_val_eq (bs t19 t3 t2_5 recip u_aff : List (BitVec 8))
    (hU : fe51ValOfBytes (bs.take 40) % p25519 = (montProjOfBytes bs).U)
    (hW : fe51ValOfBytes (bs.drop 40) % p25519 = (montProjOfBytes bs).W)
    (ht19 : fe51ValOfBytes t19 % p25519 = fpPow (fe51ValOfBytes (bs.drop 40) % p25519) (2 ^ 250 - 1))
    (ht3 : fe51ValOfBytes t3 % p25519 = fpPow (fe51ValOfBytes (bs.drop 40) % p25519) 11)
    (ht2_5 : fe51ValOfBytes t2_5 % p25519 = fpPow (fe51ValOfBytes t19 % p25519) (2 ^ (5#32).toNat))
    (hrecip : fe51ValOfBytes recip % p25519 = (fe51ValOfBytes t2_5 * fe51ValOfBytes t3) % p25519)
    (hu_aff : fe51ValOfBytes u_aff % p25519 = (fe51ValOfBytes (bs.take 40) * fe51ValOfBytes recip) % p25519) :
    fe51ValOfBytes u_aff % p25519 = fpMul (montProjOfBytes bs).U (fpInv (montProjOfBytes bs).W) := by
  have hinv : fe51ValOfBytes recip % p25519 = fpInv (montProjOfBytes bs).W := by
    rw [← hW]
    exact compress_recip_eq_fpInv (fe51ValOfBytes (bs.drop 40)) (fe51ValOfBytes t19)
      (fe51ValOfBytes t3) (fe51ValOfBytes t2_5) (fe51ValOfBytes recip)
      ht19 ht3 (by simpa using ht2_5) hrecip
  rw [hu_aff, mul_mod_eq_fpMul, hU, hinv]

theorem readLE_append_left (a b : List (BitVec 8)) (off : Nat) (h : off + 8 ≤ a.length) :
    ByteSlice.readLE (a ++ b) off 8 = ByteSlice.readLE a off 8 := by
  rw [← readLE_take (a ++ b) a.length off h, List.take_left]

theorem readLE_append_right (a b : List (BitVec 8)) (off : Nat) :
    ByteSlice.readLE (a ++ b) (a.length + off) 8 = ByteSlice.readLE b off 8 := by
  rw [← readLE_drop, List.drop_left]

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem list5 {α : Type} (l : List α) (h : l.length = 5) : ∃ a b c d e, l = [a, b, c, d, e] := by
  match l, h with
  | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩

/-- The first five words of the words of `a ++ b` (`|a| = 40`) are the words of `a`. -/
theorem chunks_left (a b : List (BitVec 8)) (ha : a.length = 40) (hb : b.length = 40)
    (h0 h1 h2 h3 h4) :
    [(chunks64 (a ++ b) 10)[0]'h0, (chunks64 (a ++ b) 10)[1]'h1, (chunks64 (a ++ b) 10)[2]'h2,
      (chunks64 (a ++ b) 10)[3]'h3, (chunks64 (a ++ b) 10)[4]'h4] = chunks64 a 5 := by
  apply List.ext_getElem (by simp [chunks64_length])
  intro i hi1 hi2
  simp at hi1
  rw [chunks64_getElem 5 a i hi2]
  interval_cases i <;> simp only [List.getElem_cons_zero, List.getElem_cons_succ, chunks64_getElem] <;>
    exact readLE_append_left _ _ _ (by omega)

theorem chunks_right (a b : List (BitVec 8)) (ha : a.length = 40) (hb : b.length = 40)
    (h5 h6 h7 h8 h9) :
    [(chunks64 (a ++ b) 10)[5]'h5, (chunks64 (a ++ b) 10)[6]'h6, (chunks64 (a ++ b) 10)[7]'h7,
      (chunks64 (a ++ b) 10)[8]'h8, (chunks64 (a ++ b) 10)[9]'h9] = chunks64 b 5 := by
  apply List.ext_getElem (by simp [chunks64_length])
  intro i hi1 hi2
  simp at hi1
  rw [chunks64_getElem 5 b i hi2]
  interval_cases i <;> simp only [List.getElem_cons_zero, List.getElem_cons_succ, chunks64_getElem] <;>
    (rw [← readLE_append_right a b, ha])

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem chunks_left' (a b : List (BitVec 8)) (ha : a.length = 40) (hb : b.length = 40)
    (cw : List (BitVec 64)) (hcw : cw = chunks64 (a ++ b) 10) (h0 h1 h2 h3 h4) :
    [cw[0]'h0, cw[1]'h1, cw[2]'h2, cw[3]'h3, cw[4]'h4] = chunks64 a 5 := by
  subst hcw; exact chunks_left a b ha hb _ _ _ _ _

theorem chunks_right' (a b : List (BitVec 8)) (ha : a.length = 40) (hb : b.length = 40)
    (cw : List (BitVec 64)) (hcw : cw = chunks64 (a ++ b) 10) (h5 h6 h7 h8 h9) :
    [cw[5]'h5, cw[6]'h6, cw[7]'h7, cw[8]'h8, cw[9]'h9] = chunks64 b 5 := by
  subst hcw; exact chunks_right a b ha hb _ _ _ _ _

end X25519Dalek.LP

namespace X25519Dalek.LP

end X25519Dalek.LP

namespace X25519Dalek.LP

end X25519Dalek.LP

end
end

section
section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

abbrev aaName : String := "<curve25519_dalek::montgomery::ProjectivePoint>::as_affine"

theorem aa_lookup : lookupBlockSym aaName x25519CliMultiLib.blocks = some (11, 0) := by decide +kernel
theorem lk_mul11 : lookupBlockSym callee11_0 x25519CliMultiLib.blocks = some (1, 0) := by decide +kernel
theorem lk_p22501 : lookupBlockSym callee11_1 x25519CliMultiLib.blocks = some (5, 0) := by decide +kernel
theorem lk_pow2k : lookupBlockSym callee11_2 x25519CliMultiLib.blocks = some (2, 0) := by decide +kernel


set_option maxHeartbeats 4000000 in
theorem aa_ok : fnOk aaName (fun _ => montProjectiveAsAffineSpec) := by
  refine ⟨11, 0, aa_lookup, fun mpl hP => ?_⟩
  intro x R s0 hpc hrun hpre hal hCLp
  obtain ⟨out, self, out_bs, self_bs⟩ := x
  have hfa : x25519CliMultiLib.fnAddr mpl aaName = mpl.base 11 := by
    simp [MultiPlacedLib.fnAddr, aa_lookup]
  rw [hfa] at hpc
  simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at hpre
  have h1 := Satisfies.of_eq hpre
    (Q := ⌜s0.readReg64 Reg.x8 = out ∧ s0.readReg64 Reg.x0 = self ∧ out_bs.length = 32 ∧
        montProjBounded self_bs (2 ^ 54)⌝ ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝ ∗ stackFrame s0 1312 ∗ (self ↦ₛ self_bs) ∗
      (out ↦ₛ out_bs) ∗ R) (by ac_rfl)
  rw [sat_pure_sep, sat_pure_sep] at h1
  obtain ⟨⟨hx8, hx0, hlo, hsb⟩, hCL, h1⟩ := h1
  have hsl : self_bs.length = 80 := hsb.1
  obtain ⟨hUb, hUv⟩ := montProj_take40 self_bs _ hsb
  obtain ⟨hWb, hWv⟩ := montProj_drop40 self_bs _ hsb
  -- the stack frame: 1040 bytes for callees, then the locals
  simp only [stackFrame] at h1
  have h2 := sat_mr_split (a := s0.sp - BitVec.ofNat 64 1312) 1040 272 (by norm_num) (s0.sp - 272#64)
    (by clear * -; bv_omega) h1
  rw [← sepConj_assoc, sepConj_comm (memRegion _ 1040), sepConj_assoc] at h2
  replace h2 := sat_mr_split 8 264 (by norm_num) (s0.sp - 264#64) (by clear * -; bv_omega) h2
  rw [sepConj_left_comm] at h2
  replace h2 := sat_mr_split 40 224 (by norm_num) (s0.sp - 224#64) (by clear * -; bv_omega) h2
  rw [sepConj_left_comm] at h2
  replace h2 := sat_mr_split 40 184 (by norm_num) (s0.sp - 184#64) (by clear * -; bv_omega) h2
  rw [sepConj_left_comm] at h2
  replace h2 := sat_mr_split 8 176 (by norm_num) (s0.sp - 176#64) (by clear * -; bv_omega) h2
  rw [sepConj_left_comm] at h2
  replace h2 := sat_mr_split 40 136 (by norm_num) (s0.sp - 136#64) (by clear * -; bv_omega) h2
  rw [sepConj_left_comm] at h2
  replace h2 := sat_mr_split 8 128 (by norm_num) (s0.sp - 128#64) (by clear * -; bv_omega) h2
  rw [sepConj_left_comm] at h2
  replace h2 := sat_mr_split 80 48 (by norm_num) (s0.sp - 48#64) (by clear * -; bv_omega) h2
  rw [sepConj_left_comm] at h2
  -- the six saved registers
  obtain ⟨sv, hsvl, h2⟩ := memRegion_words' (s0.sp - 48#64) 6 (by norm_num) h2
  obtain ⟨g0, g1, g2, g3, g4, g5, rfl⟩ := list6 sv hsvl
  clear hpre h1
  -- the run
  have e0 : mkS s0 (mpl.base 11) s0.regs.regs s0.sp s0.pstate s0.mem s0.vregs.regs = s0 := by
    rw [← hpc]; rfl
  show Reach _ s0 _
  conv => enter [2]; rw [← e0]
  generalize hQ : SubroutineOutcome _ _ _ _ = Q
  have hal' : (s0.sp &&& 15#64 == 0#64) = true := hal
  have hal272 := aligned_sub hal' 272 (by decide) (by decide)
  have hr0 : s0.regs.regs 0#5 = self := by rw [← readGpr_eq s0 0#5 (by decide)]; exact hx0
  have hr8 : s0.regs.regs 8#5 = out := by rw [← readGpr_eq s0 8#5 (by decide)]; exact hx8
  -- 0: sub sp, sp, #272
  refine Reach.mk hrun (c11_0 hP hCL 11 (Memory.KeepsFrozen.refl _)) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, hr0, hr8]
  have hS := h2
  -- 4: stp
  obtain ⟨-, -, cwa⟩ := sat_words_read hS 0 (by simp)
  obtain ⟨-, -, cwb⟩ := sat_words_read hS 1 (by simp)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cwa cwb
  refine Reach.mk hrun (c11_4 hP hCL 11 (Memory.KeepsFrozen.refl _)) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, hr0, hr8, hal272, cwa, cwb]
  refine Reach.wr64x2 0 hS (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp)
    (fun m1 hS' kf => ?_)
  simp only [List.set_cons_zero, List.set_cons_succ] at hS'
  clear hS cwa cwb; have hS := hS'; clear hS'
  have kf1 := kf
  -- 8: stp
  obtain ⟨-, -, cwa⟩ := sat_words_read hS 2 (by simp)
  obtain ⟨-, -, cwb⟩ := sat_words_read hS 3 (by simp)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cwa cwb
  refine Reach.mk hrun (c11_8 hP hCL 11 kf1) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, hr0, hr8, hal272, cwa, cwb]
  refine Reach.wr64x2 2 hS (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp)
    (fun m2 hS' kf => ?_)
  simp only [List.set_cons_zero, List.set_cons_succ] at hS'
  clear hS cwa cwb; have hS := hS'; clear hS'
  have kf2 := kf1.trans kf
  clear kf
  -- 12: stp
  obtain ⟨-, -, cwa⟩ := sat_words_read hS 4 (by simp)
  obtain ⟨-, -, cwb⟩ := sat_words_read hS 5 (by simp)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cwa cwb
  refine Reach.mk hrun (c11_12 hP hCL 11 kf2) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, hr0, hr8, hal272, cwa, cwb]
  refine Reach.wr64x2 4 hS (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp)
    (fun m3 hS' kf => ?_)
  simp only [List.set_cons_zero, List.set_cons_succ] at hS'
  clear hS cwa cwb; have hS := hS'; clear hS'
  have kf3 := kf2.trans kf
  clear kf
  refine Reach.mk hrun (c11_16 hP hCL 11 kf3) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, hr0, hr8]
  refine Reach.mk hrun (c11_20 hP hCL 11 kf3) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, hr0, hr8]
  refine Reach.mk hrun (c11_24 hP hCL 11 kf3) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, hr0, hr8]
  refine Reach.mk hrun (c11_28 hP hCL 11 kf3) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, hr0, hr8]
  refine Reach.mk hrun (c11_32 hP hCL 11 kf3) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, hr0, hr8]
  refine Reach.mk hrun (c11_36 hP hCL 11 kf3) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, hr0, hr8]
  -- 40: bl pow22501
  refine Reach.mk hrun (c11_40 hP hCL 11 kf3 lk_p22501) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, hr0, hr8]
  generalize hrf : upd _ (30#5) (mpl.base 11 + 44#64) = rf
  have f : rf 0#5 = s0.sp - 128#64 ∧ rf 1#5 = self + 40#64 ∧ rf 19#5 = out ∧ rf 20#5 = self ∧
      rf 21#5 = s0.sp - 128#64 ∧ rf 29#5 = s0.sp - 48#64 ∧ rf 30#5 = mpl.base 11 + 44#64 ∧
      rf 22#5 = s0.regs.regs 22#5 ∧ rf 23#5 = s0.regs.regs 23#5 ∧ rf 24#5 = s0.regs.regs 24#5 ∧
      rf 25#5 = s0.regs.regs 25#5 ∧ rf 26#5 = s0.regs.regs 26#5 ∧ rf 27#5 = s0.regs.regs 27#5 ∧
      rf 28#5 = s0.regs.regs 28#5 := by
    rw [← hrf]; simp [hr0, hr8]
  clear hrf
  -- pieces for pow22501: W = self + 40, its 80-byte output, the 1040-byte callee frame
  rw [pointsToBytes_split self self_bs 40 (by omega)] at hS
  simp only [sepConj_assoc] at hS
  simp only [sepConj_left_comm _ (memRegion (s0.sp - 1312#64) _)] at hS
  simp only [sepConj_left_comm _ (memRegion (s0.sp - 128#64) _)] at hS
  obtain ⟨ob, hobl, hS⟩ := memRegion_bytes (s0.sp - 128#64) 80 (by norm_num) hS
  simp only [sepConj_left_comm _ ((self + BitVec.ofNat 64 40) ↦ₛ _)] at hS
  rw [show s0.sp - 1312#64 = s0.sp - 272#64 - BitVec.ofNat 64 1040 by clear * -; bv_omega] at hS
  have hpre := sat_pre3 (φ := (mkS s0 (mpl.base 5) rf (s0.sp - 272#64) s0.pstate m3 s0.vregs.regs).readReg64
      Reg.x0 = s0.sp - 128#64 ∧ (mkS s0 (mpl.base 5) rf (s0.sp - 272#64) s0.pstate m3
      s0.vregs.regs).readReg64 Reg.x1 = self + 40#64 ∧ ob.length = 80 ∧
      fe51LimbsBounded (self_bs.drop 40) (2 ^ 54)) ⟨by simp [f], by simp [f], hobl, hWb⟩ hS
  refine Reach.callS hP 11 fnOk_fe51_pow22501 lk_p22501 (by decide)
    (s0.sp - 128#64, self + 40#64, ob, self_bs.drop 40) _ (by simp) hrun hal272
    (libCodeLoaded_keepsFrozen hCL kf3) hpre ?_ ?_ ?_ ?_
  · intro sf; exact not_sat_false
  · intro c sf; exact not_sat_false
  · intro sf; exact not_sat_false
  · intro sf hrunf hspf hcsf hvf1 hpost hkf
    obtain ⟨f0, f1, f19, f20, f21, f29, f30, f22, f23, f24, f25, f26, f27, f28⟩ := f
    obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29⟩ := hcsf
    rw [f19] at c19; rw [f20] at c20; rw [f21] at c21; rw [f29] at c29; rw [f30]
    rw [f22] at c22; rw [f23] at c23; rw [f24] at c24; rw [f25] at c25; rw [f26] at c26
    rw [f27] at c27; rw [f28] at c28
    have kf4 := kf3.trans hkf
    -- unpack the post of pow22501
    simp only [ToBaseSpec.toSpec, stackFrame, mkS_sp, hspf, addr_sub_sub, Nat.reduceAdd, Nat.reduceMod,
      Nat.reducePow] at hpost
    simp only [sepConj_assoc] at hpost
    simp only [sepConj_left_comm _ (sepExists _)] at hpost
    rw [sepExists_sepConj, sat_sepExists] at hpost
    obtain ⟨t19, hpost⟩ := hpost
    rw [sepExists_sepConj, sat_sepExists] at hpost
    obtain ⟨t3, hpost⟩ := hpost
    simp only [sepConj_assoc] at hpost
    simp only [sepConj_left_comm _ (SepProp.pure _)] at hpost
    rw [sat_pure_sep] at hpost
    obtain ⟨⟨h19b, h3b, h19v, h3v⟩, hpost⟩ := hpost
    have h19l : t19.length = 40 := h19b.1
    have h3l : t3.length = 40 := h3b.1
    -- the 80-byte output as ten words; the two copy buffers as words
    rw [← chunks64_flat 10 (t19 ++ t3) (by simp; omega), ← words_eq_bytes] at hpost
    set cw := chunks64 (t19 ++ t3) 10 with hcw
    have hcwl : cw.length = 10 := chunks64_length _ _
    simp only [sepConj_left_comm _ (memRegion (s0.sp - 224#64) _)] at hpost
    obtain ⟨b19, hb19l, hpost⟩ := memRegion_words' (s0.sp - 224#64) 5 (by norm_num) hpost
    simp only [sepConj_left_comm _ (memRegion (s0.sp - 176#64) _)] at hpost
    obtain ⟨b3, hb3l, hpost⟩ := memRegion_words' (s0.sp - 176#64) 5 (by norm_num) hpost
    simp only [sepConj_left_comm _ ((s0.sp - 128#64) ↦₆₄* _)] at hpost
    obtain ⟨r0, -, -⟩ := sat_words_read hpost 0 (by omega)
    obtain ⟨r1, -, -⟩ := sat_words_read hpost 1 (by omega)
    obtain ⟨r2, -, -⟩ := sat_words_read hpost 2 (by omega)
    obtain ⟨r3, -, -⟩ := sat_words_read hpost 3 (by omega)
    obtain ⟨r4, cr4, -⟩ := sat_words_read hpost 4 (by omega)
    obtain ⟨r5, -, -⟩ := sat_words_read hpost 5 (by omega)
    obtain ⟨r6, -, -⟩ := sat_words_read hpost 6 (by omega)
    obtain ⟨r7, -, -⟩ := sat_words_read hpost 7 (by omega)
    obtain ⟨r8, -, -⟩ := sat_words_read hpost 8 (by omega)
    obtain ⟨r9, cr9, -⟩ := sat_words_read hpost 9 (by omega)
    have cq0 := (sat_words_access hpost 0 16 (by omega)).1
    have cq1 := (sat_words_access hpost 16 16 (by omega)).1
    have cq2 := (sat_words_access hpost 40 16 (by omega)).1
    have cq3 := (sat_words_access hpost 56 16 (by omega)).1
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 cr4 cr9 cq0 cq1 cq2 cq3
    -- 44 .. 60
    refine Reach.mk hrunf (c11_44 hP hCL 11 kf4) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, c19, c20, c21, c29, r0, r1, r2, r3, cq0, cq1]
    refine Reach.mk hrunf (c11_48 hP hCL 11 kf4) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, c19, c20, c21, c29]
    refine Reach.mk hrunf (c11_52 hP hCL 11 kf4) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, c19, c20, c21, c29, r4, cr4]
    refine Reach.mk hrunf (c11_56 hP hCL 11 kf4) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, c19, c20, c21, c29, r9, cr9]
    refine Reach.mk hrunf (c11_60 hP hCL 11 kf4) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, c19, c20, c21, c29]
    -- 64: stp q0, q1, [sp, #48]
    have hT := hpost
    simp only [sepConj_left_comm _ ((s0.sp - 224#64) ↦₆₄* _)] at hT
    have cw0 := (sat_words_access hT 0 16 (by omega)).2
    have cw1 := (sat_words_access hT 16 16 (by omega)).2
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw0 cw1
    refine Reach.mk hrunf (c11_64 hP hCL 11 kf4) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, c19, c20, c21, c29, hal272, cw0, cw1]
    refine Reach.wr64x4 0 hT (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero])
      (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by omega) (fun m5 hT5 kf => ?_)
    have kf5 := kf4.trans kf
    clear kf hT hpost
    simp only [Nat.reduceAdd] at hT5
    have hR := hT5
    simp only [sepConj_left_comm _ ((s0.sp - 128#64) ↦₆₄* _)] at hR
    obtain ⟨r5, -, -⟩ := sat_words_read hR 5 (by omega)
    obtain ⟨r6, -, -⟩ := sat_words_read hR 6 (by omega)
    obtain ⟨r7, -, -⟩ := sat_words_read hR 7 (by omega)
    obtain ⟨r8, -, -⟩ := sat_words_read hR 8 (by omega)
    have cq2 := (sat_words_access hR 40 16 (by omega)).1
    have cq3 := (sat_words_access hR 56 16 (by omega)).1
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at r5 r6 r7 r8 cq2 cq3
    clear hR
    refine Reach.mk hrunf (c11_68 hP hCL 11 kf5) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, c19, c20, c21, c29, r5, r6, cq2]
    refine Reach.mk hrunf (c11_72 hP hCL 11 kf5) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, c19, c20, c21, c29, r7, r8, cq3]
    -- 76: str x8, [sp, #80]
    obtain ⟨-, -, cw4⟩ := sat_words_read hT5 4 (by simp [hb19l])
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw4
    refine Reach.mk hrunf (c11_76 hP hCL 11 kf5) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, c19, c20, c21, c29, hal272, cw4]
    refine Reach.wr64 4 hT5 (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hb19l]) (fun m6 hT6 kf => ?_)
    have kf6 := kf5.trans kf
    clear kf
    refine Reach.mk hrunf (c11_80 hP hCL 11 kf6) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, c19, c20, c21, c29]
    -- 84: stp q0, q1, [sp, #96]
    have hU := hT6
    simp only [sepConj_left_comm _ ((s0.sp - 176#64) ↦₆₄* _)] at hU
    have cu0 := (sat_words_access hU 0 16 (by omega)).2
    have cu1 := (sat_words_access hU 16 16 (by omega)).2
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cu0 cu1
    refine Reach.mk hrunf (c11_84 hP hCL 11 kf6) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, c19, c20, c21, c29, hal272, cu0, cu1]
    refine Reach.wr64x4 0 hU (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero])
      (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by omega) (fun m7 hU7 kf => ?_)
    have kf7 := kf6.trans kf
    clear kf
    simp only [Nat.reduceAdd] at hU7
    -- 88: str x9, [sp, #128]
    obtain ⟨-, -, cu4⟩ := sat_words_read hU7 4 (by simp [hb3l])
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cu4
    refine Reach.mk hrunf (c11_88 hP hCL 11 kf7) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, c19, c20, c21, c29, hal272, cu4]
    refine Reach.wr64 4 hU7 (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hb3l]) (fun m8 hU8 kf => ?_)
    have kf8 := kf7.trans kf
    clear kf
    -- 92: bl pow2k
    refine Reach.mk hrunf (c11_92 hP hCL 11 kf8 lk_pow2k) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, c19, c20, c21, c29]
    -- buffers as bytes again: t19 copy, t3 copy, and the output split into t19 and t3
    obtain ⟨y0, y1, y2, y3, y4, rfl⟩ := list5 b19 hb19l
    obtain ⟨z0, z1, z2, z3, z4, rfl⟩ := list5 b3 hb3l
    simp only [List.set_cons_zero, List.set_cons_succ] at hU8
    rw [chunks_left' t19 t3 h19l h3l cw hcw, chunks_right' t19 t3 h19l h3l cw hcw] at hU8
    rw [words_eq_bytes, words_eq_bytes, chunks64_flat 5 _ (by omega), chunks64_flat 5 _ (by omega)] at hU8
    rw [words_eq_bytes, hcw, chunks64_flat 10 _ (by simp; omega), pointsToBytes_append, h19l,
      show s0.sp - 128#64 + BitVec.ofNat 64 40 = s0.sp - 88#64 by clear * -; bv_omega] at hU8
    simp only [sepConj_assoc] at hU8
    -- the 96-byte frame for pow2k
    simp only [sepConj_left_comm _ (memRegion (s0.sp - 1312#64) _)] at hU8
    replace hU8 := sat_mr_split 944 96 (by norm_num) (s0.sp - 272#64 - BitVec.ofNat 64 96) (by clear * -; bv_omega) hU8
    rw [sepConj_left_comm] at hU8
    simp only [sepConj_left_comm _ ((s0.sp - 128#64) ↦ₛ t19)] at hU8
    simp only [sepConj_left_comm _ ((s0.sp - 224#64) ↦ₛ t19)] at hU8
    generalize hrf : upd _ (30#5) (mpl.base 11 + 96#64) = rf2
    generalize hvf : upd _ (1#5) (cw[8] ++ cw[7]) = vf2
    have g : rf2 8#5 = s0.sp - 128#64 ∧ rf2 0#5 = s0.sp - 224#64 ∧ rf2 1#5 = 5#64 ∧
        rf2 30#5 = mpl.base 11 + 96#64 ∧ CSRegs sf rf2 := by
      rw [← hrf]; simp [CSRegs]
    clear hrf
    have hpre := sat_pre3 (φ := (mkS sf (mpl.base 2) rf2 (s0.sp - 272#64) sf.pstate m8 vf2).readReg64
        Reg.x8 = s0.sp - 128#64 ∧ (mkS sf (mpl.base 2) rf2 (s0.sp - 272#64) sf.pstate m8 vf2).readReg64
        Reg.x0 = s0.sp - 224#64 ∧ (mkS sf (mpl.base 2) rf2 (s0.sp - 272#64) sf.pstate m8 vf2).readReg32
        Reg.x1 = 5#32 ∧ t19.length = 40 ∧ fe51LimbsBounded t19 (2 ^ 54) ∧ 0 < (5#32).toNat ∧
        (5#32).toNat < 256)
      ⟨by simp [g.1], by simp [g.2.1], by simp [State.readReg32, g.2.2.1], h19l,
        fe51LimbsBounded_mono h19b (by norm_num), by decide, by decide⟩ hU8
    refine Reach.callS hP 11 fnOk_fe51_pow2k lk_pow2k (by decide)
      (s0.sp - 128#64, s0.sp - 224#64, 5#32, t19, t19) _ (by simp) hrunf hal272
      (libCodeLoaded_keepsFrozen hCL kf8) hpre ?_ ?_ ?_ ?_
    · intro sf; exact not_sat_false
    · intro c sf; exact not_sat_false
    · intro sf; exact not_sat_false
    intro sf2 hrun2 hsp2 hcs2 hv2 hpost2 hkf2
    have kf9 := kf8.trans hkf2
    obtain ⟨g8, g0, g1, g30, gcs⟩ := g
    have d19 : sf2.regs.regs 19#5 = out := hcs2.1.trans (gcs.1.symm.trans c19)
    have d20 : sf2.regs.regs 20#5 = self := hcs2.2.1.trans (gcs.2.1.symm.trans c20)
    have d21 : sf2.regs.regs 21#5 = s0.sp - 128#64 := hcs2.2.2.1.trans (gcs.2.2.1.symm.trans c21)
    have d29 : sf2.regs.regs 29#5 = s0.sp - 48#64 :=
      hcs2.2.2.2.2.2.2.2.2.2.2.trans (gcs.2.2.2.2.2.2.2.2.2.2.symm.trans c29)
    rw [g30]
    simp only [ToBaseSpec.toSpec, stackFrame, mkS_sp, hsp2] at hpost2
    simp only [sepConj_assoc] at hpost2
    simp only [sepConj_left_comm _ (sepExists _)] at hpost2
    rw [sepExists_sepConj, sat_sepExists] at hpost2
    obtain ⟨t25, hpost2⟩ := hpost2
    simp only [sepConj_assoc] at hpost2
    simp only [sepConj_left_comm _ (SepProp.pure _)] at hpost2
    rw [sat_pure_sep] at hpost2
    obtain ⟨⟨h25b, h25v⟩, hpost2⟩ := hpost2
    have h25l : t25.length = 40 := h25b.1
    refine Reach.mk hrun2 (c11_96 hP hCL 11 kf9) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, d19, d20, d21, d29]
    refine Reach.mk hrun2 (c11_100 hP hCL 11 kf9) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, d19, d20, d21, d29]
    refine Reach.mk hrun2 (c11_104 hP hCL 11 kf9) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, d19, d20, d21, d29]
    refine Reach.mk hrun2 (c11_108 hP hCL 11 kf9 lk_mul11) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, d19, d20, d21, d29]
    -- frame for mul: merge back to 1040, split 816 + 224
    simp only [sepConj_left_comm _ (memRegion (s0.sp - 272#64 - BitVec.ofNat 64 96) _)] at hpost2
    simp only [sepConj_left_comm _ (memRegion (s0.sp - 1312#64) _)] at hpost2
    replace hpost2 := sat_mr_merge (a := s0.sp - 1312#64) (b := s0.sp - 272#64 - BitVec.ofNat 64 96)
      944 96 (by norm_num) (by clear * -; bv_omega) hpost2
    have e816 : s0.sp - 1312#64 + BitVec.ofNat 64 816 = s0.sp - 272#64 - BitVec.ofNat 64 224 := by
      clear * -; bv_omega
    simp only [Nat.reduceAdd] at hpost2
    replace hpost2 := sat_mr_split (a := s0.sp - 1312#64) (n := 816) (k := 224) (by norm_num)
      (s0.sp - 272#64 - BitVec.ofNat 64 224) e816 hpost2
    rw [sepConj_left_comm] at hpost2
    simp only [sepConj_left_comm _ (memRegion (s0.sp - 264#64) _)] at hpost2
    obtain ⟨rj, hrjl, hpost2⟩ := memRegion_bytes (s0.sp - 264#64) 40 (by norm_num) hpost2
    simp only [sepConj_left_comm _ ((s0.sp - 176#64) ↦ₛ t3)] at hpost2
    simp only [sepConj_left_comm _ ((s0.sp - 128#64) ↦ₛ t25)] at hpost2
    generalize hrf : upd _ (30#5) (mpl.base 11 + 112#64) = rf3
    have g3 : rf3 8#5 = s0.sp - 264#64 ∧ rf3 0#5 = s0.sp - 128#64 ∧ rf3 1#5 = s0.sp - 176#64 ∧
        rf3 30#5 = mpl.base 11 + 112#64 ∧ CSRegs sf2 rf3 := by
      rw [← hrf]; simp [CSRegs]
    clear hrf
    have hpre3 := sat_pre4 (φ := (mkS sf2 (mpl.base 1) rf3 (s0.sp - 272#64) sf2.pstate sf2.mem
        sf2.vregs.regs).readReg64 Reg.x8 = s0.sp - 264#64 ∧ (mkS sf2 (mpl.base 1) rf3 (s0.sp - 272#64)
        sf2.pstate sf2.mem sf2.vregs.regs).readReg64 Reg.x0 = s0.sp - 128#64 ∧ (mkS sf2 (mpl.base 1) rf3
        (s0.sp - 272#64) sf2.pstate sf2.mem sf2.vregs.regs).readReg64 Reg.x1 = s0.sp - 176#64 ∧
        rj.length = 40 ∧ fe51LimbsBounded t25 (2 ^ 54) ∧ fe51LimbsBounded t3 (2 ^ 54))
      ⟨by simp [g3.1], by simp [g3.2.1], by simp [g3.2.2.1], hrjl, fe51LimbsBounded_mono h25b (by norm_num),
        fe51LimbsBounded_mono h3b (by norm_num)⟩ hpost2
    refine Reach.callS hP 11 fnOk_fe51_mul.1 lk_mul11 (by decide)
      (s0.sp - 264#64, s0.sp - 128#64, s0.sp - 176#64, rj, t25, t3) _ (by simp) hrun2 hal272
      (libCodeLoaded_keepsFrozen hCL kf9) hpre3 ?_ ?_ ?_ ?_
    · intro sf; exact not_sat_false
    · intro c sf; exact not_sat_false
    · intro sf; exact not_sat_false
    intro sf3 hrun3 hsp3 hcs3 hv3 hpost3 hkf3
    have kf10 := kf9.trans hkf3
    obtain ⟨g38, g30', g31, g330, gcs3⟩ := g3
    have e19 : sf3.regs.regs 19#5 = out := hcs3.1.trans (gcs3.1.symm.trans d19)
    have e20 : sf3.regs.regs 20#5 = self := hcs3.2.1.trans (gcs3.2.1.symm.trans d20)
    have e21 : sf3.regs.regs 21#5 = s0.sp - 128#64 := hcs3.2.2.1.trans (gcs3.2.2.1.symm.trans d21)
    have e29 : sf3.regs.regs 29#5 = s0.sp - 48#64 :=
      hcs3.2.2.2.2.2.2.2.2.2.2.trans (gcs3.2.2.2.2.2.2.2.2.2.2.symm.trans d29)
    rw [g330]
    simp only [ToBaseSpec.toSpec, stackFrame, mkS_sp, hsp3] at hpost3
    simp only [sepConj_assoc] at hpost3
    simp only [sepConj_left_comm _ (sepExists _)] at hpost3
    rw [sepExists_sepConj, sat_sepExists] at hpost3
    obtain ⟨recip, hpost3⟩ := hpost3
    simp only [sepConj_assoc] at hpost3
    simp only [sepConj_left_comm _ (SepProp.pure _)] at hpost3
    rw [sat_pure_sep] at hpost3
    obtain ⟨⟨hrb, hrv⟩, hpost3⟩ := hpost3
    -- 112, 116, 120, 124: mul (out = s0.sp - 128, a = self, b = recip)
    refine Reach.mk hrun3 (c11_112 hP hCL 11 kf10) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, e19, e20, e21, e29]
    refine Reach.mk hrun3 (c11_116 hP hCL 11 kf10) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, e19, e20, e21, e29]
    refine Reach.mk hrun3 (c11_120 hP hCL 11 kf10) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, e19, e20, e21, e29]
    refine Reach.mk hrun3 (c11_124 hP hCL 11 kf10 lk_mul11) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, e19, e20, e21, e29]
    simp only [sepConj_left_comm _ (memRegion (s0.sp - 272#64 - 224#64) _)] at hpost3
    simp only [sepConj_left_comm _ ((s0.sp - 128#64) ↦ₛ t25)] at hpost3
    simp only [sepConj_left_comm _ ((s0.sp - 264#64) ↦ₛ recip)] at hpost3
    simp only [sepConj_left_comm _ (self ↦ₛ List.take 40 self_bs)] at hpost3
    generalize hrf : upd _ (30#5) (mpl.base 11 + 128#64) = rf4
    have g4 : rf4 8#5 = s0.sp - 128#64 ∧ rf4 0#5 = self ∧ rf4 1#5 = s0.sp - 264#64 ∧
        rf4 30#5 = mpl.base 11 + 128#64 ∧ CSRegs sf3 rf4 := by
      rw [← hrf]; simp [CSRegs, e20]
    clear hrf
    have hpre4 := sat_pre4 (φ := (mkS sf3 (mpl.base 1) rf4 (s0.sp - 272#64) sf3.pstate sf3.mem
        sf3.vregs.regs).readReg64 Reg.x8 = s0.sp - 128#64 ∧ (mkS sf3 (mpl.base 1) rf4 (s0.sp - 272#64)
        sf3.pstate sf3.mem sf3.vregs.regs).readReg64 Reg.x0 = self ∧ (mkS sf3 (mpl.base 1) rf4
        (s0.sp - 272#64) sf3.pstate sf3.mem sf3.vregs.regs).readReg64 Reg.x1 = s0.sp - 264#64 ∧
        t25.length = 40 ∧ fe51LimbsBounded (self_bs.take 40) (2 ^ 54) ∧ fe51LimbsBounded recip (2 ^ 54))
      ⟨by simp [g4.1], by simp [g4.2.1], by simp [g4.2.2.1], h25l, hUb,
        fe51LimbsBounded_mono hrb (by norm_num)⟩ hpost3
    refine Reach.callS hP 11 fnOk_fe51_mul.1 lk_mul11 (by decide)
      (s0.sp - 128#64, self, s0.sp - 264#64, t25, self_bs.take 40, recip) _ (by simp) hrun3 hal272
      (libCodeLoaded_keepsFrozen hCL kf10) hpre4 ?_ ?_ ?_ ?_
    · intro sf; exact not_sat_false
    · intro c sf; exact not_sat_false
    · intro sf; exact not_sat_false
    intro sf4 hrun4 hsp4 hcs4 hv4 hpost4 hkf4
    have kf11 := kf10.trans hkf4
    obtain ⟨g48, g40, g41, g430, gcs4⟩ := g4
    have i19 : sf4.regs.regs 19#5 = out := hcs4.1.trans (gcs4.1.symm.trans e19)
    have i29 : sf4.regs.regs 29#5 = s0.sp - 48#64 :=
      hcs4.2.2.2.2.2.2.2.2.2.2.trans (gcs4.2.2.2.2.2.2.2.2.2.2.symm.trans e29)
    rw [g430]
    simp only [ToBaseSpec.toSpec, stackFrame, mkS_sp, hsp4] at hpost4
    simp only [sepConj_assoc] at hpost4
    simp only [sepConj_left_comm _ (sepExists _)] at hpost4
    rw [sepExists_sepConj, sat_sepExists] at hpost4
    obtain ⟨uaff, hpost4⟩ := hpost4
    simp only [sepConj_assoc] at hpost4
    simp only [sepConj_left_comm _ (SepProp.pure _)] at hpost4
    rw [sat_pure_sep] at hpost4
    obtain ⟨⟨hub, huv⟩, hpost4⟩ := hpost4
    have hval := as_affine_val_eq self_bs t19 t3 t25 recip uaff hUv hWv h19v h3v h25v hrv huv
    simp only [sepConj_left_comm _ ((s0.sp - 48#64) ↦₆₄* _)] at hpost4
    simp only [sepConj_left_comm _ (out ↦ₛ out_bs)] at hpost4
    simp only [sepConj_left_comm _ ((s0.sp - 128#64) ↦ₛ uaff)] at hpost4
    have v2eq : VRegFile.calleeSaved ⟨vf2⟩ = VRegFile.calleeSaved ⟨sf.vregs.regs⟩ := by
      rw [← hvf]; simp [VRegFile.calleeSaved, VRegFile.read]
    obtain ⟨rfin, ps, m', hst, r19, r20, r21, r28, r29, r22, r23, r24, r25, r26, r27, hF⟩ :=
      X25519Dalek.projectivePoint_as_affine_tail
        (s := mkS sf4 (mpl.base 11 + 128#64) sf4.regs.regs (s0.sp - 272#64) sf4.pstate _ sf4.vregs.regs)
        hP (libCodeLoaded_keepsFrozen hCL kf11) hrun4 rfl rfl hal272 i19 i29 hub hlo hpost4
    have kfin : s0.mem.KeepsFrozen m' := kf11.trans (X25519Dalek.steps_keepsFrozen hst)
    change rfin 22#5 = sf4.regs.regs 22#5 at r22
    change rfin 23#5 = sf4.regs.regs 23#5 at r23
    change rfin 24#5 = sf4.regs.regs 24#5 at r24
    change rfin 25#5 = sf4.regs.regs 25#5 at r25
    change rfin 26#5 = sf4.regs.regs 26#5 at r26
    change rfin 27#5 = sf4.regs.regs 27#5 at r27
    refine ⟨_, hst, ?_⟩
    change Q (mkS sf4 _ rfin s0.sp ps m' sf4.vregs.regs)
    rw [← hQ]
    left
    refine ⟨⟨?_, by simp, by simpa using hrun4⟩, ⟨by simp, ?_⟩, ?_⟩
    · simp [readGpr_eq]
    · -- callee-saved registers: x19-x21, x28, x29 from the stack; x22-x27 through the four calls
      have k22 : sf4.regs.regs 22#5 = s0.regs.regs 22#5 := hcs4.2.2.2.1.trans (gcs4.2.2.2.1.symm.trans
        (hcs3.2.2.2.1.trans (gcs3.2.2.2.1.symm.trans (hcs2.2.2.2.1.trans (gcs.2.2.2.1.symm.trans c22)))))
      have k23 : sf4.regs.regs 23#5 = s0.regs.regs 23#5 := hcs4.2.2.2.2.1.trans (gcs4.2.2.2.2.1.symm.trans
        (hcs3.2.2.2.2.1.trans (gcs3.2.2.2.2.1.symm.trans (hcs2.2.2.2.2.1.trans (gcs.2.2.2.2.1.symm.trans c23)))))
      have k24 : sf4.regs.regs 24#5 = s0.regs.regs 24#5 := hcs4.2.2.2.2.2.1.trans
        (gcs4.2.2.2.2.2.1.symm.trans (hcs3.2.2.2.2.2.1.trans (gcs3.2.2.2.2.2.1.symm.trans
        (hcs2.2.2.2.2.2.1.trans (gcs.2.2.2.2.2.1.symm.trans c24)))))
      have k25 : sf4.regs.regs 25#5 = s0.regs.regs 25#5 := hcs4.2.2.2.2.2.2.1.trans
        (gcs4.2.2.2.2.2.2.1.symm.trans (hcs3.2.2.2.2.2.2.1.trans (gcs3.2.2.2.2.2.2.1.symm.trans
        (hcs2.2.2.2.2.2.2.1.trans (gcs.2.2.2.2.2.2.1.symm.trans c25)))))
      have k26 : sf4.regs.regs 26#5 = s0.regs.regs 26#5 := hcs4.2.2.2.2.2.2.2.1.trans
        (gcs4.2.2.2.2.2.2.2.1.symm.trans (hcs3.2.2.2.2.2.2.2.1.trans (gcs3.2.2.2.2.2.2.2.1.symm.trans
        (hcs2.2.2.2.2.2.2.2.1.trans (gcs.2.2.2.2.2.2.2.1.symm.trans c26)))))
      have k27 : sf4.regs.regs 27#5 = s0.regs.regs 27#5 := hcs4.2.2.2.2.2.2.2.2.1.trans
        (gcs4.2.2.2.2.2.2.2.2.1.symm.trans (hcs3.2.2.2.2.2.2.2.2.1.trans (gcs3.2.2.2.2.2.2.2.2.1.symm.trans
        (hcs2.2.2.2.2.2.2.2.2.1.trans (gcs.2.2.2.2.2.2.2.2.1.symm.trans c27)))))
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try (simp only [mkS_readGpr, Reg.fp, BitVec.reduceEq, ↓reduceIte]; simp [readGpr_eq, r19, r20, r21,
        r22, r23, r24, r25, r26, r27, r28, r29, k22, k23, k24, k25, k26, k27]))
      show VRegFile.calleeSaved ⟨sf4.vregs.regs⟩ = calleeSavedVRegs s0
      rw [show VRegFile.calleeSaved ⟨sf4.vregs.regs⟩ = calleeSavedVRegs sf4 from rfl, hv4]
      rw [show VRegFile.calleeSaved ⟨sf3.vregs.regs⟩ = calleeSavedVRegs sf3 from rfl, hv3]
      rw [show VRegFile.calleeSaved ⟨sf2.vregs.regs⟩ = calleeSavedVRegs sf2 from rfl, hv2, v2eq]
      rw [show VRegFile.calleeSaved ⟨sf.vregs.regs⟩ = calleeSavedVRegs sf from rfl, hvf1]
    · simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mkS_mem, stackFrame, mkS_sp]
      rw [hval] at hF
      generalize natToLeBytes 32 (fpMul (montProjOfBytes self_bs).U (fpInv (montProjOfBytes self_bs).W)) = resb
        at hF ⊢
      rw [words_eq_bytes] at hF
      try simp only [sepConj_assoc] at hF
      -- the frame, bottom up
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 272#64 - 224#64) _)] at hF
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 1312#64) _)] at hF
      replace hF := sat_mr_merge (a := s0.sp - 1312#64) 816 _ (by norm_num) (by clear * -; bv_omega) hF
      try simp only [h19l, h3l, hrb.1, hub.1, hrjl, Nat.reduceAdd, List.length_flatMap, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, unpack64_length] at hF
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 272#64) _)] at hF
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 1312#64) _)] at hF
      replace hF := sat_mr_merge (a := s0.sp - 1312#64) 1040 _ (by norm_num) (by clear * -; bv_omega) hF
      try simp only [h19l, h3l, hrb.1, hub.1, hrjl, Nat.reduceAdd, List.length_flatMap, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, unpack64_length] at hF
      simp only [sepConj_left_comm _ ((s0.sp - 264#64) ↦ₛ _)] at hF
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 1312#64) _)] at hF
      have eA := addr_eq s0.sp 264 1312 1048 (by norm_num) (by norm_num) (by norm_num)
      replace hF := sat_mr_bytes (a := s0.sp - 1312#64) (b := s0.sp - 264#64) (bs := recip) 1048
        (by norm_num) eA hF
      rw [show 1048 + recip.length = 1088 by rw [hrb.1]] at hF
      simp only [sepConj_left_comm _ ((s0.sp - 224#64) ↦ₛ t19)] at hF
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 1312#64) _)] at hF
      have e1088 := addr_eq s0.sp 224 1312 1088 (by norm_num) (by norm_num) (by norm_num)
      replace hF := sat_mr_bytes (a := s0.sp - 1312#64) (b := s0.sp - 224#64) (bs := t19) 1088 (by norm_num) e1088 hF
      rw [show 1088 + t19.length = 1128 by rw [h19l]] at hF
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 184#64) _)] at hF
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 1312#64) _)] at hF
      have e1128 := addr_eq s0.sp 184 1312 1128 (by norm_num) (by norm_num) (by norm_num)
      replace hF := sat_mr_merge (a := s0.sp - 1312#64) (b := s0.sp - 184#64) 1128 8 (by norm_num) e1128 hF
      simp only [sepConj_left_comm _ ((s0.sp - 176#64) ↦ₛ t3)] at hF
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 1312#64) _)] at hF
      have e1136 := addr_eq s0.sp 176 1312 1136 (by norm_num) (by norm_num) (by norm_num)
      replace hF := sat_mr_bytes (a := s0.sp - 1312#64) (b := s0.sp - 176#64) (bs := t3) 1136 (by norm_num) e1136 hF
      rw [show 1136 + t3.length = 1176 by rw [h3l]] at hF
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 136#64) _)] at hF
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 1312#64) _)] at hF
      have e1176 := addr_eq s0.sp 136 1312 1176 (by norm_num) (by norm_num) (by norm_num)
      replace hF := sat_mr_merge (a := s0.sp - 1312#64) (b := s0.sp - 136#64) 1176 8 (by norm_num) e1176 hF
      simp only [sepConj_left_comm _ ((s0.sp - 128#64) ↦ₛ uaff)] at hF
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 1312#64) _)] at hF
      have e1184 := addr_eq s0.sp 128 1312 1184 (by norm_num) (by norm_num) (by norm_num)
      replace hF := sat_mr_bytes (a := s0.sp - 1312#64) (b := s0.sp - 128#64) (bs := uaff) 1184 (by norm_num) e1184 hF
      rw [show 1184 + uaff.length = 1224 by rw [hub.1]] at hF
      simp only [sepConj_left_comm _ ((s0.sp - 88#64) ↦ₛ t3)] at hF
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 1312#64) _)] at hF
      have e1224 := addr_eq s0.sp 88 1312 1224 (by norm_num) (by norm_num) (by norm_num)
      replace hF := sat_mr_bytes (a := s0.sp - 1312#64) (b := s0.sp - 88#64) (bs := t3) 1224 (by norm_num) e1224 hF
      rw [show 1224 + t3.length = 1264 by rw [h3l]] at hF
      simp only [sepConj_left_comm _ ((s0.sp - 48#64) ↦ₛ _)] at hF
      simp only [sepConj_left_comm _ (memRegion (s0.sp - 1312#64) _)] at hF
      have e1264 := addr_eq s0.sp 48 1312 1264 (by norm_num) (by norm_num) (by norm_num)
      replace hF := sat_mr_bytes (a := s0.sp - 1312#64) (b := s0.sp - 48#64)
        (bs := List.flatMap unpack64 [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 28#5, s0.regs.regs 21#5,
          s0.regs.regs 20#5, s0.regs.regs 19#5]) 1264 (by norm_num) e1264 hF
      rw [show 1264 + (List.flatMap unpack64 [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 28#5,
          s0.regs.regs 21#5, s0.regs.regs 20#5, s0.regs.regs 19#5]).length = 1312 by
        rw [flatMap_unpack64_length]; rfl] at hF
      rw [show s0.sp - 1312#64 = s0.sp - BitVec.ofNat 64 1312 from rfl] at hF
      simp only [sepConj_left_comm _ ((self + 40#64) ↦ₛ _)] at hF
      simp only [sepConj_left_comm _ (self ↦ₛ _)] at hF
      rw [← sepConj_assoc, show (40#64 : BitVec 64) = BitVec.ofNat 64 40 from rfl,
        ← pointsToBytes_split self self_bs 40 (by omega)] at hF
      exact Satisfies.of_eq (sat_sep_mono hF (Entails.refl _)) (by ac_rfl)

end X25519Dalek.LP

namespace X25519Dalek

theorem fnOk_projectivePoint_as_affine_dev :
    fnOk
      "<curve25519_dalek::montgomery::ProjectivePoint>::as_affine"
      (fun _ => montProjectiveAsAffineSpec) :=
  LP.aa_ok

end X25519Dalek

end
end

section
open X25519Dalek

theorem solution :
    fnOk
      "<curve25519_dalek::montgomery::ProjectivePoint>::as_affine"
      (fun _ => montProjectiveAsAffineSpec) := by
  apply X25519Dalek.fnOk_projectivePoint_as_affine_dev <;> assumption

end
