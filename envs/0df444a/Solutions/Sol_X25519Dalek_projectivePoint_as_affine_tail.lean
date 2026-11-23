-- Prove2me | solution 1 for X25519Dalek.projectivePoint_as_affine_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T14:52:21.861267+00:00
-- url     : https://prove2.me/submissions/19b07fea-b852-421b-928b-d0c5b34ebbff

import Definitions.Def_X25519Dalek_PlacedObj
import Definitions.Def_X25519Dalek_Rfc7748
import Definitions.Def_X25519Dalek_Spec
import Definitions.Def_Arm64_ISA_Semantics
import Theorems.Thm_X25519Dalek_fe51_to_bytes_eq_natToLeBytes
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
theorem holds_emp_iff {h : Heap} : (emp : SepProp).holds h ↔ h = Heap.empty := Iff.rfl
theorem holds_sepConj_iff {P Q : SepProp} {h : Heap} :
    (P ∗ Q).holds h ↔
      ∃ h₁ h₂ : Heap, h₁.Disjoint h₂ ∧ h = h₁.union h₂ ∧ P.holds h₁ ∧ Q.holds h₂ := Iff.rfl
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

/-! ## Byte-slice heaps carry no ghost state and nothing outside the slice -/

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

/-! ## Reaching a final state -/

def Reach (p : Program) (s : State) (Q : State → Prop) : Prop := ∃ sf, Steps p s sf ∧ Q sf

theorem Reach.done {p : Program} {s : State} {Q : State → Prop} (h : Q s) : Reach p s Q :=
  ⟨s, Steps.refl s, h⟩

theorem Reach.exec {p : Program} {s : State} {Q : State → Prop} {i : Instr}
    (hrun : s.status = .Running) (hf : p.fetchMem s.mem s.pc = some i)
    (h : Reach p (execInstWithSvc (evalSvc p.svc) i s) Q) : Reach p s Q := by
  obtain ⟨sf, hst, hq⟩ := h
  exact ⟨sf, Steps.step (Step.exec hrun hf) hst, hq⟩

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

end X25519Dalek.LP

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

end X25519Dalek.LP

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

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

/-- After a byte store into an owned slice, continue from an abstract memory. -/
theorem Reach.wr8 {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {vr : BitVec 5 → BitVec 128} {Q : State → Prop}
    {base a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp} {v : BitVec 8} (j : Nat)
    (hs : m ⊨ (base ↦ₛ bs) ∗ F) (ha : a = base + BitVec.ofNat 64 j) (hj : j < bs.length)
    (h : ∀ m', (m' ⊨ (base ↦ₛ bs.set j v) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc r sp ps m' vr) Q) :
    Reach p (mkS s0 pc r sp ps (m.write8 a v) vr) Q := by
  subst ha
  have hw := (sat_bytes_access hs j 1 (by omega)).2
  have hk := Memory.keepsFrozen_write8 (m := m) (by simpa using hw) v
  exact h _ (sat_bytes_write hs j hj v) hk

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

end X25519Dalek.LP

namespace X25519Dalek.LP

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64 Arm64.Obj

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem Reach.gen_upd {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {vr : BitVec 5 → BitVec 128} {Q : State → Prop}
    {i : BitVec 5} {E : BitVec 64}
    (h : ∀ v, v = E → Reach p (mkS s0 pc (upd r i v) sp ps m vr) Q) :
    Reach p (mkS s0 pc (upd r i E) sp ps m vr) Q := h E rfl

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP

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

theorem blk11 : blk 11 = x25519CliBlk11 := rfl

theorem len11 : x25519CliBlk11.code.length = 520 := by decide +kernel

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (j : Nat) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem c11_128 : (bprog mpl j).fetchMem m (mpl.base 11 + 128#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0f#5) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x1d#5) 0xffffffffffffffc8#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 128) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0f#5) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x1d#5) 0xffffffffffffffc8#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_132 : (bprog mpl j).fetchMem m (mpl.base 11 + 132#64) =
    some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x0d#5) 0x0013#16 0) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 132) (inst := (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x0d#5) 0x0013#16 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_136 : (bprog mpl j).fetchMem m (mpl.base 11 + 136#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0a#5) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x1d#5) 0xffffffffffffffb0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 136) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0a#5) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x1d#5) 0xffffffffffffffb0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_140 : (bprog mpl j).fetchMem m (mpl.base 11 + 140#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 51 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 140) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 51 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_144 : (bprog mpl j).fetchMem m (mpl.base 11 + 144#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 144) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_148 : (bprog mpl j).fetchMem m (mpl.base 11 + 148#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0b#5) (Reg.gpr 0x0a#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 148) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0b#5) (Reg.gpr 0x0a#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_152 : (bprog mpl j).fetchMem m (mpl.base 11 + 152#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x0f#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 152) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x0f#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_156 : (bprog mpl j).fetchMem m (mpl.base 11 + 156#64) =
    some (Instr.dataProc3 (RegWidth.W64) (DataProc3Op.UMADDL) (Reg.gpr 0x0e#5) (Reg.gpr 0x09#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x0b#5)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 156) (inst := (Instr.dataProc3 (RegWidth.W64) (DataProc3Op.UMADDL) (Reg.gpr 0x0e#5) (Reg.gpr 0x09#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x0b#5))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_160 : (bprog mpl j).fetchMem m (mpl.base 11 + 160#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x09#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffc0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 160) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x09#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffc0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_164 : (bprog mpl j).fetchMem m (mpl.base 11 + 164#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0b#5) (Reg.gpr 0x0c#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 164) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0b#5) (Reg.gpr 0x0c#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_168 : (bprog mpl j).fetchMem m (mpl.base 11 + 168#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x0a#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 168) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x0a#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_172 : (bprog mpl j).fetchMem m (mpl.base 11 + 172#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 172) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_176 : (bprog mpl j).fetchMem m (mpl.base 11 + 176#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x10#5) (Reg.gpr 0x0e#5) 0x013#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 176) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x10#5) (Reg.gpr 0x0e#5) 0x013#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_180 : (bprog mpl j).fetchMem m (mpl.base 11 + 180#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x0c#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 180) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x0c#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_184 : (bprog mpl j).fetchMem m (mpl.base 11 + 184#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0c#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x10#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 184) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0c#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x10#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_188 : (bprog mpl j).fetchMem m (mpl.base 11 + 188#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x10#5) (Reg.gpr 0x0f#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 188) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x10#5) (Reg.gpr 0x0f#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_192 : (bprog mpl j).fetchMem m (mpl.base 11 + 192#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x10#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 192) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x10#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_196 : (bprog mpl j).fetchMem m (mpl.base 11 + 196#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0c#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x0c#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 196) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0c#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x0c#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_200 : (bprog mpl j).fetchMem m (mpl.base 11 + 200#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0c#5) (Reg.gpr 0x09#5) (Reg.gpr 0x0c#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 200) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0c#5) (Reg.gpr 0x09#5) (Reg.gpr 0x0c#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_204 : (bprog mpl j).fetchMem m (mpl.base 11 + 204#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0c#5) (Reg.gpr 0x08#5) (Reg.gpr 0x0c#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 204) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0c#5) (Reg.gpr 0x08#5) (Reg.gpr 0x0c#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_208 : (bprog mpl j).fetchMem m (mpl.base 11 + 208#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) 51 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 208) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) 51 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_212 : (bprog mpl j).fetchMem m (mpl.base 11 + 212#64) =
    some (Instr.dataProc3 (RegWidth.W64) (DataProc3Op.UMADDL) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x0e#5)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 212) (inst := (Instr.dataProc3 (RegWidth.W64) (DataProc3Op.UMADDL) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x0e#5))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_216 : (bprog mpl j).fetchMem m (mpl.base 11 + 216#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0c#5) 8 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 216) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0c#5) 8 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_220 : (bprog mpl j).fetchMem m (mpl.base 11 + 220#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0e#5) (Reg.gpr 0x0c#5) 16 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 220) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0e#5) (Reg.gpr 0x0c#5) 16 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_224 : (bprog mpl j).fetchMem m (mpl.base 11 + 224#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x0c#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 224) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x0c#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_228 : (bprog mpl j).fetchMem m (mpl.base 11 + 228#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000000#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 228) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000000#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_232 : (bprog mpl j).fetchMem m (mpl.base 11 + 232#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000001#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 232) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000001#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_236 : (bprog mpl j).fetchMem m (mpl.base 11 + 236#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0c#5) 24 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 236) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0c#5) 24 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_240 : (bprog mpl j).fetchMem m (mpl.base 11 + 240#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x0b#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 240) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x0b#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_244 : (bprog mpl j).fetchMem m (mpl.base 11 + 244#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0e#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000002#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 244) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0e#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000002#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_248 : (bprog mpl j).fetchMem m (mpl.base 11 + 248#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0e#5) (Reg.gpr 0x0c#5) 32 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 248) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0e#5) (Reg.gpr 0x0c#5) 32 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_252 : (bprog mpl j).fetchMem m (mpl.base 11 + 252#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000003#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 252) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000003#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_256 : (bprog mpl j).fetchMem m (mpl.base 11 + 256#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0c#5) 48 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 256) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0c#5) 48 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_260 : (bprog mpl j).fetchMem m (mpl.base 11 + 260#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) 40 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 260) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) 40 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_264 : (bprog mpl j).fetchMem m (mpl.base 11 + 264#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0e#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000004#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 264) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0e#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000004#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_268 : (bprog mpl j).fetchMem m (mpl.base 11 + 268#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0e#5) (Reg.gpr 0x0b#5) 5 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 268) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0e#5) (Reg.gpr 0x0b#5) 5 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_272 : (bprog mpl j).fetchMem m (mpl.base 11 + 272#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) (Reg.gpr 0x0a#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 272) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) (Reg.gpr 0x0a#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_276 : (bprog mpl j).fetchMem m (mpl.base 11 + 276#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000005#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 276) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000005#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_280 : (bprog mpl j).fetchMem m (mpl.base 11 + 280#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x0b#5) 13 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 280) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x0b#5) 13 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_284 : (bprog mpl j).fetchMem m (mpl.base 11 + 284#64) =
    some (Instr.bitfield (RegWidth.W32) (BitfieldOp.BFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0b#5) 29 28) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 284) (inst := (Instr.bitfield (RegWidth.W32) (BitfieldOp.BFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0b#5) 29 28)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_288 : (bprog mpl j).fetchMem m (mpl.base 11 + 288#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0e#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000007#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 288) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0e#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000007#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_292 : (bprog mpl j).fetchMem m (mpl.base 11 + 292#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0e#5) (Reg.gpr 0x0b#5) 29 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 292) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0e#5) (Reg.gpr 0x0b#5) 29 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_296 : (bprog mpl j).fetchMem m (mpl.base 11 + 296#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 296) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_300 : (bprog mpl j).fetchMem m (mpl.base 11 + 300#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000008#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 300) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000008#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_304 : (bprog mpl j).fetchMem m (mpl.base 11 + 304#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x0b#5) 45 50) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 304) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x0b#5) 45 50)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_308 : (bprog mpl j).fetchMem m (mpl.base 11 + 308#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000006#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 308) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000006#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_312 : (bprog mpl j).fetchMem m (mpl.base 11 + 312#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0b#5) 21 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 312) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0b#5) 21 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_316 : (bprog mpl j).fetchMem m (mpl.base 11 + 316#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) 37 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 316) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) 37 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_320 : (bprog mpl j).fetchMem m (mpl.base 11 + 320#64) =
    some (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 6) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 320) (inst := (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 6)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_324 : (bprog mpl j).fetchMem m (mpl.base 11 + 324#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0e#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000000a#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 324) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0e#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000000a#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_328 : (bprog mpl j).fetchMem m (mpl.base 11 + 328#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000009#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 328) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000009#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_332 : (bprog mpl j).fetchMem m (mpl.base 11 + 332#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) 2 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 332) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) 2 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_336 : (bprog mpl j).fetchMem m (mpl.base 11 + 336#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000000b#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 336) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000000b#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_340 : (bprog mpl j).fetchMem m (mpl.base 11 + 340#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x0a#5) 10 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 340) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x0a#5) 10 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_344 : (bprog mpl j).fetchMem m (mpl.base 11 + 344#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000000c#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 344) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000000c#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_348 : (bprog mpl j).fetchMem m (mpl.base 11 + 348#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x0a#5) 18 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 348) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x0a#5) 18 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_352 : (bprog mpl j).fetchMem m (mpl.base 11 + 352#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000000d#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 352) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000000d#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_356 : (bprog mpl j).fetchMem m (mpl.base 11 + 356#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) 26 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 356) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) 26 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_360 : (bprog mpl j).fetchMem m (mpl.base 11 + 360#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000000e#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 360) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000000e#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_364 : (bprog mpl j).fetchMem m (mpl.base 11 + 364#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x0a#5) 34 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 364) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x0a#5) 34 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_368 : (bprog mpl j).fetchMem m (mpl.base 11 + 368#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000000f#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 368) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000000f#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_372 : (bprog mpl j).fetchMem m (mpl.base 11 + 372#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x0a#5) 50 50) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 372) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x0a#5) 50 50)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_376 : (bprog mpl j).fetchMem m (mpl.base 11 + 376#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) 42 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 376) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) 42 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_380 : (bprog mpl j).fetchMem m (mpl.base 11 + 380#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000011#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 380) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000011#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_384 : (bprog mpl j).fetchMem m (mpl.base 11 + 384#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) 7 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 384) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) 7 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_388 : (bprog mpl j).fetchMem m (mpl.base 11 + 388#64) =
    some (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 1) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 388) (inst := (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 1)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_392 : (bprog mpl j).fetchMem m (mpl.base 11 + 392#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000012#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 392) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000012#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_396 : (bprog mpl j).fetchMem m (mpl.base 11 + 396#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) 15 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 396) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) 15 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_400 : (bprog mpl j).fetchMem m (mpl.base 11 + 400#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000014#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 400) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000014#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_404 : (bprog mpl j).fetchMem m (mpl.base 11 + 404#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) 31 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 404) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) 31 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_408 : (bprog mpl j).fetchMem m (mpl.base 11 + 408#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000013#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 408) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000013#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_412 : (bprog mpl j).fetchMem m (mpl.base 11 + 412#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x09#5) 23 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 412) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0c#5) (Reg.gpr 0x09#5) 23 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_416 : (bprog mpl j).fetchMem m (mpl.base 11 + 416#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000015#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 416) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000015#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_420 : (bprog mpl j).fetchMem m (mpl.base 11 + 420#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) 47 50) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 420) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) 47 50)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_424 : (bprog mpl j).fetchMem m (mpl.base 11 + 424#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) 39 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 424) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) 39 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_428 : (bprog mpl j).fetchMem m (mpl.base 11 + 428#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000010#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 428) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000010#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_432 : (bprog mpl j).fetchMem m (mpl.base 11 + 432#64) =
    some (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 4) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 432) (inst := (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 4)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_436 : (bprog mpl j).fetchMem m (mpl.base 11 + 436#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000018#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 436) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000018#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_440 : (bprog mpl j).fetchMem m (mpl.base 11 + 440#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 4 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 440) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 4 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_444 : (bprog mpl j).fetchMem m (mpl.base 11 + 444#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000016#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 444) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000016#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_448 : (bprog mpl j).fetchMem m (mpl.base 11 + 448#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000019#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 448) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000019#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_452 : (bprog mpl j).fetchMem m (mpl.base 11 + 452#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) 12 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 452) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) 12 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_456 : (bprog mpl j).fetchMem m (mpl.base 11 + 456#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000001a#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 456) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000001a#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_460 : (bprog mpl j).fetchMem m (mpl.base 11 + 460#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 20 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 460) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 20 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_464 : (bprog mpl j).fetchMem m (mpl.base 11 + 464#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000001b#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 464) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000001b#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_468 : (bprog mpl j).fetchMem m (mpl.base 11 + 468#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) 28 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 468) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) 28 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_472 : (bprog mpl j).fetchMem m (mpl.base 11 + 472#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000001c#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 472) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000001c#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_476 : (bprog mpl j).fetchMem m (mpl.base 11 + 476#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 36 63) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 476) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 36 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_480 : (bprog mpl j).fetchMem m (mpl.base 11 + 480#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 44 50) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 480) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 44 50)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_484 : (bprog mpl j).fetchMem m (mpl.base 11 + 484#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000017#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 484) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000017#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_488 : (bprog mpl j).fetchMem m (mpl.base 11 + 488#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000001d#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 488) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000001d#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_492 : (bprog mpl j).fetchMem m (mpl.base 11 + 492#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000001e#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 492) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000001e#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_496 : (bprog mpl j).fetchMem m (mpl.base 11 + 496#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000001f#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 496) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x000000000000001f#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_500 : (bprog mpl j).fetchMem m (mpl.base 11 + 500#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000100#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 500) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000100#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_504 : (bprog mpl j).fetchMem m (mpl.base 11 + 504#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1c#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x00000000000000f0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 504) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1c#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x00000000000000f0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_508 : (bprog mpl j).fetchMem m (mpl.base 11 + 508#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.Offset (Reg.sp) 0x00000000000000e0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 508) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.Offset (Reg.sp) 0x00000000000000e0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_512 : (bprog mpl j).fetchMem m (mpl.base 11 + 512#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.sp) (Reg.sp) 0x110#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 512) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.sp) (Reg.sp) 0x110#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c11_516 : (bprog mpl j).fetchMem m (mpl.base 11 + 516#64) =
    some (Instr.ret (Reg.gpr 0x1e#5)) := by
  have := fetch_at' hP hCL (by decide) j blk11 len11 (off := 516) (inst := (Instr.ret (Reg.gpr 0x1e#5))) (by decide) rfl (by decide +kernel) hk
  exact this

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

/-- A 40-byte buffer as five words. -/
theorem bytes40_words (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 40) :
    (a ↦ₛ bs) = (a ↦₆₄* chunks64 bs 5) := by
  rw [words_eq_bytes, chunks64_flat 5 bs (by omega)]

/-! ## Field arithmetic -/

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP

theorem list32 {α : Type} (l : List α) (h : l.length = 32) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25
      a26 a27 a28 a29 a30 a31, l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
      a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21,
      a22, a23, a24, a25, a26, a27, a28, a29, a30, a31], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
      a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, rfl⟩

end X25519Dalek.LP

namespace X25519Dalek.LP

theorem byte6_eq (u0 u1 : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (u0 >>> 48)))) &&&
        ~~~(BitVec.ofNat 64 (Nat.shiftLeft 1 29 - 1) <<< 3) |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 u1))) &&&
        BitVec.ofNat 64 (Nat.shiftLeft 1 29 - 1)) <<< 3))))) =
    BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (u0 >>> 48)) &&& 18446744069414584327#64 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 u1) &&& 536870911#64) <<< 3) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  interval_cases i <;> simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, Nat.shiftLeft_eq]

theorem byte12_eq (u1 u2 : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.setWidth 32 (u1 >>> 45 &&& BitVec.ofNat 64 (Nat.shiftLeft 1 6 - 1))) |||
        BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 u2)) <<< 6)))))) =
    BitVec.truncate 8 (BitVec.setWidth 32 (u1 >>> 45 &&& 63#64) ||| BitVec.setWidth 32 u2 <<< 6) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  interval_cases i <;> simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, Nat.shiftLeft_eq]

theorem byte19_eq (u2 u3 : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.setWidth 32 (u2 >>> 50 &&& BitVec.ofNat 64 (Nat.shiftLeft 1 1 - 1))) |||
        BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 u3)) <<< 1)))))) =
    BitVec.truncate 8 (BitVec.setWidth 32 (u2 >>> 50 &&& 1#64) ||| BitVec.setWidth 32 u3 <<< 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  interval_cases i <;> simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, Nat.shiftLeft_eq]

theorem byte25_eq (u3 u4 : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.setWidth 32 (u3 >>> 47 &&& BitVec.ofNat 64 (Nat.shiftLeft 1 4 - 1))) |||
        BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 u4)) <<< 4)))))) =
    BitVec.truncate 8 (BitVec.setWidth 32 (u3 >>> 47 &&& 15#64) ||| BitVec.setWidth 32 u4 <<< 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  interval_cases i <;> simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, Nat.shiftLeft_eq]

end X25519Dalek.LP

end
end

section
section
/-! # `as_affine` offsets 128-516: `FieldElement51::to_bytes` of the product and the epilogue -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

set_option maxHeartbeats 4000000 in
/-- `FieldElement51::to_bytes` of the product and the epilogue of `as_affine` (offsets 128 to 516). -/
theorem aa_tail {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {sf : State} (hrun : sf.status = .Running) {m : Memory}
    (hkf : m0.KeepsFrozen m) {S out : BitVec 64} {uaff out_bs : List (BitVec 8)}
    {v29 v30 v28 v21 v20 v19 : BitVec 64} {F : SepProp} {Q : State → Prop}
    (hal : (S - 272#64 &&& 15#64) = 0#64) (h19 : sf.regs.regs 19#5 = out)
    (h29 : sf.regs.regs 29#5 = S - 48#64) (hub : fe51LimbsBounded uaff (2 ^ 52)) (hlo : out_bs.length = 32)
    (hs : m ⊨ ((S - 128#64) ↦ₛ uaff) ∗ (out ↦ₛ out_bs) ∗ ((S - 48#64) ↦₆₄* [v29, v30, v28, v21, v20, v19]) ∗ F)
    (hcont : ∀ (m' : Memory) (rf : BitVec 5 → BitVec 64) (ps : PState),
      rf 19#5 = v19 → rf 20#5 = v20 → rf 21#5 = v21 → rf 28#5 = v28 → rf 29#5 = v29 →
      rf 22#5 = sf.regs.regs 22#5 → rf 23#5 = sf.regs.regs 23#5 → rf 24#5 = sf.regs.regs 24#5 →
      rf 25#5 = sf.regs.regs 25#5 → rf 26#5 = sf.regs.regs 26#5 → rf 27#5 = sf.regs.regs 27#5 →
      (m' ⊨ ((S - 128#64) ↦ₛ uaff) ∗ (out ↦ₛ natToLeBytes 32 (fe51ValOfBytes uaff % p25519)) ∗
        ((S - 48#64) ↦₆₄* [v29, v30, v28, v21, v20, v19]) ∗ F) → m0.KeepsFrozen m' →
      Q (mkS sf v30 rf S ps m' sf.vregs.regs)) :
    Reach (bprog mpl 11) (mkS sf (mpl.base 11 + 128#64) sf.regs.regs (S - 272#64) sf.pstate m
      sf.vregs.regs) Q := by
  have hrun' := hrun
  rw [bytes40_words _ _ hub.1] at hs
  obtain ⟨q0, cq0, -⟩ := sat_words_read hs 0 (by simp [chunks64_length])
  obtain ⟨q1, cq1, -⟩ := sat_words_read hs 1 (by simp [chunks64_length])
  obtain ⟨q2, cq2, -⟩ := sat_words_read hs 2 (by simp [chunks64_length])
  obtain ⟨q3, cq3, -⟩ := sat_words_read hs 3 (by simp [chunks64_length])
  obtain ⟨q4, cq4, -⟩ := sat_words_read hs 4 (by simp [chunks64_length])
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero, chunks64_getElem] at q0 q1 q2 q3 q4 cq0 cq1 cq2 cq3 cq4
  have hl := hub
  unfold fe51LimbsBounded at hl
  obtain ⟨_, hl0, hl1, hl2, hl3, hl4⟩ := hl
  generalize hL0 : ByteSlice.readLE uaff 0 8 = l0 at q0 hl0
  generalize hL1 : ByteSlice.readLE uaff 8 8 = l1 at q1 hl1
  generalize hL2 : ByteSlice.readLE uaff 16 8 = l2 at q2 hl2
  generalize hL3 : ByteSlice.readLE uaff 24 8 = l3 at q3 hl3
  generalize hL4 : ByteSlice.readLE uaff 32 8 = l4 at q4 hl4
  rw [words_eq_bytes, chunks64_flat 5 _ (by rw [hub.1])] at hs
  rw [sepConj_left_comm] at hs
  have kf := hkf
  refine Reach.mk hrun (c11_128 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.mk hrun (c11_132 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v132 e132 => ?_)
  refine Reach.mk hrun (c11_136 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.mk hrun (c11_140 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v140 e140 => ?_)
  refine Reach.mk hrun (c11_144 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v144 e144 => ?_)
  refine Reach.mk hrun (c11_148 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v148 e148 => ?_)
  refine Reach.mk hrun (c11_152 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v152 e152 => ?_)
  refine Reach.mk hrun (c11_156 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v156 e156 => ?_)
  refine Reach.mk hrun (c11_160 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.mk hrun (c11_164 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v164 e164 => ?_)
  refine Reach.mk hrun (c11_168 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v168 e168 => ?_)
  refine Reach.mk hrun (c11_172 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v172 e172 => ?_)
  refine Reach.mk hrun (c11_176 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v176 e176 => ?_)
  refine Reach.mk hrun (c11_180 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v180 e180 => ?_)
  refine Reach.mk hrun (c11_184 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v184 e184 => ?_)
  refine Reach.mk hrun (c11_188 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v188 e188 => ?_)
  refine Reach.mk hrun (c11_192 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v192 e192 => ?_)
  refine Reach.mk hrun (c11_196 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v196 e196 => ?_)
  refine Reach.mk hrun (c11_200 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v200 e200 => ?_)
  refine Reach.mk hrun (c11_204 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v204 e204 => ?_)
  refine Reach.mk hrun (c11_208 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v208 e208 => ?_)
  refine Reach.mk hrun (c11_212 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v212 e212 => ?_)
  refine Reach.mk hrun (c11_216 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v216 e216 => ?_)
  refine Reach.mk hrun (c11_220 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v220 e220 => ?_)
  refine Reach.mk hrun (c11_224 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v224 e224 => ?_)
  have cw := (sat_bytes_access hs 0 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_228 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 0 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  have cw := (sat_bytes_access hs 1 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_232 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 1 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_236 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v236 e236 => ?_)
  refine Reach.mk hrun (c11_240 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v240 e240 => ?_)
  have cw := (sat_bytes_access hs 2 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_244 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 2 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_248 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v248 e248 => ?_)
  have cw := (sat_bytes_access hs 3 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_252 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 3 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_256 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v256 e256 => ?_)
  refine Reach.mk hrun (c11_260 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v260 e260 => ?_)
  have cw := (sat_bytes_access hs 4 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_264 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 4 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_268 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v268 e268 => ?_)
  refine Reach.mk hrun (c11_272 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v272 e272 => ?_)
  have cw := (sat_bytes_access hs 5 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_276 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 5 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_280 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v280 e280 => ?_)
  refine Reach.mk hrun (c11_284 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v284 e284 => ?_)
  have cw := (sat_bytes_access hs 7 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_288 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 7 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_292 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v292 e292 => ?_)
  refine Reach.mk hrun (c11_296 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v296 e296 => ?_)
  have cw := (sat_bytes_access hs 8 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_300 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 8 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_304 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v304 e304 => ?_)
  have cw := (sat_bytes_access hs 6 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_308 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 6 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_312 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v312 e312 => ?_)
  refine Reach.mk hrun (c11_316 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v316 e316 => ?_)
  refine Reach.mk hrun (c11_320 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v320 e320 => ?_)
  have cw := (sat_bytes_access hs 10 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_324 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 10 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  have cw := (sat_bytes_access hs 9 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_328 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 9 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_332 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v332 e332 => ?_)
  have cw := (sat_bytes_access hs 11 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_336 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 11 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_340 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v340 e340 => ?_)
  have cw := (sat_bytes_access hs 12 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_344 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 12 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_348 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v348 e348 => ?_)
  have cw := (sat_bytes_access hs 13 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_352 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 13 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_356 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v356 e356 => ?_)
  have cw := (sat_bytes_access hs 14 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_360 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 14 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_364 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v364 e364 => ?_)
  have cw := (sat_bytes_access hs 15 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_368 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 15 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_372 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v372 e372 => ?_)
  refine Reach.mk hrun (c11_376 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v376 e376 => ?_)
  have cw := (sat_bytes_access hs 17 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_380 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 17 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_384 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v384 e384 => ?_)
  refine Reach.mk hrun (c11_388 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v388 e388 => ?_)
  have cw := (sat_bytes_access hs 18 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_392 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 18 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_396 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v396 e396 => ?_)
  have cw := (sat_bytes_access hs 20 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_400 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 20 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_404 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v404 e404 => ?_)
  have cw := (sat_bytes_access hs 19 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_408 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 19 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_412 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v412 e412 => ?_)
  have cw := (sat_bytes_access hs 21 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_416 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 21 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_420 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v420 e420 => ?_)
  refine Reach.mk hrun (c11_424 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v424 e424 => ?_)
  have cw := (sat_bytes_access hs 16 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_428 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 16 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_432 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v432 e432 => ?_)
  have cw := (sat_bytes_access hs 24 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_436 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 24 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_440 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v440 e440 => ?_)
  have cw := (sat_bytes_access hs 22 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_444 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 22 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  have cw := (sat_bytes_access hs 25 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_448 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 25 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_452 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v452 e452 => ?_)
  have cw := (sat_bytes_access hs 26 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_456 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 26 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_460 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v460 e460 => ?_)
  have cw := (sat_bytes_access hs 27 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_464 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 27 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_468 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v468 e468 => ?_)
  have cw := (sat_bytes_access hs 28 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_472 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 28 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  refine Reach.mk hrun (c11_476 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v476 e476 => ?_)
  refine Reach.mk hrun (c11_480 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4]
  refine Reach.gen_upd (fun v480 e480 => ?_)
  have cw := (sat_bytes_access hs 23 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_484 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 23 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  have cw := (sat_bytes_access hs 29 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_488 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 29 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  have cw := (sat_bytes_access hs 30 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_492 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 30 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  have cw := (sat_bytes_access hs 31 1 (by simp [hlo])).2
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero] at cw
  refine Reach.mk hrun (c11_496 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, q0, q1, q2, q3, q4, cq0, cq1, cq2, cq3, cq4, cw]
  refine Reach.wr8 31 hs (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero]) (by simp [hlo]) (fun m' hs' kf' => ?_)
  clear hs cw; have hs := hs'; clear hs'
  replace kf := kf.trans kf'
  clear kf'
  -- epilogue: restore x20, x19, x28, x21, x29, x30; release the frame; return
  have hW := hs
  simp only [sepConj_left_comm _ ((S - 48#64) ↦₆₄* _)] at hW
  obtain ⟨w0, cw0, -⟩ := sat_words_read hW 0 (by simp)
  obtain ⟨w1, cw1, -⟩ := sat_words_read hW 1 (by simp)
  obtain ⟨w2, cw2, -⟩ := sat_words_read hW 2 (by simp)
  obtain ⟨w3, cw3, -⟩ := sat_words_read hW 3 (by simp)
  obtain ⟨w4, cw4, -⟩ := sat_words_read hW 4 (by simp)
  obtain ⟨w5, cw5, -⟩ := sat_words_read hW 5 (by simp)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceLT, addr_sub_add, addr_sub_sub, BitVec.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at w0 w1 w2 w3 w4 w5 cw0 cw1 cw2 cw3 cw4 cw5
  refine Reach.mk hrun (c11_500 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, hal, w4, w5, cw4, cw5]
  refine Reach.mk hrun (c11_504 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, hal, w2, w3, cw2, cw3]
  refine Reach.mk hrun (c11_508 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29, hal, w0, w1, cw0, cw1]
  refine Reach.mk hrun (c11_512 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29]
  refine Reach.mk hrun (c11_516 hP hCL 11 kf) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', addr_sub_add, addr_sub_sub, BitVec.sub_zero, BitVec.zero_or, BitVec.or_zero, BitVec.truncate_eq_setWidth, h19, h29]
  apply Reach.done
  generalize hLst : List.set _ 31 _ = Lst at hs
  have hLeq : Lst = natToLeBytes 32 (fe51ValOfBytes uaff % p25519) := by
    rw [← hLst]
    clear hs hW hcont
    subst e480 e476 e468 e460 e452 e440 e432 e424 e420 e412 e404 e396 e388 e384 e376 e372 e364 e356 e348 e340 e332 e320 e316 e312 e304 e296 e292 e284 e280 e272 e268 e260 e256 e248 e240 e236 e224 e220 e216 e212 e208 e204 e200 e196 e192 e188 e184 e180 e176 e172 e168 e164 e156 e152 e148 e144 e140 e132
    simp only [BitVec.reduceSetWidth]
    generalize hh0 : (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64 = h0
    generalize hh1 : (l1 &&& 2251799813685247#64) + l0 >>> 51 = h1
    generalize hh2 : (l2 &&& 2251799813685247#64) + l1 >>> 51 = h2
    generalize hh3 : (l3 &&& 2251799813685247#64) + l2 >>> 51 = h3
    generalize hh4 : (l4 &&& 2251799813685247#64) + l3 >>> 51 = h4
    generalize hq : (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = q
    generalize hu0 : h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64 = u0
    generalize hu1 : h1 + u0 >>> 51 = u1
    generalize hu2 : h2 + u1 >>> 51 = u2
    generalize hu3 : h3 + u2 >>> 51 = u3
    generalize hu4 : h4 + u3 >>> 51 = u4
    have hpack := X25519Dalek.fe51_to_bytes_eq_natToLeBytes l0 l1 l2 l3 l4 (by clear * - hl0; omega) (by clear * - hl1; omega) (by clear * - hl2; omega) (by clear * - hl3; omega) (by clear * - hl4; omega)
      h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4 hh0.symm hh1.symm hh2.symm hh3.symm hh4.symm hq.symm hu0.symm
      hu1.symm hu2.symm hu3.symm hu4.symm
    have hval : fe51Val l0 l1 l2 l3 l4 = fe51ValOfBytes uaff := by
      rw [fe51ValOfBytes, hL0, hL1, hL2, hL3, hL4]
    rw [← hval, ← hpack]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ :=
      list32 out_bs hlo
    simp only [List.set_cons_zero, List.set_cons_succ, List.cons.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    all_goals first | exact True.intro | rfl | skip
    · exact byte6_eq _ _
    · exact byte12_eq _ _
    · exact byte19_eq _ _
    · exact byte25_eq _ _
  rw [hLeq] at hs
  refine hcont m' _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (Satisfies.of_eq hs (by ac_rfl)) kf
  all_goals simp only [upd_apply, BitVec.reduceEq, ↓reduceIte]


end X25519Dalek.LP

namespace X25519Dalek

theorem projectivePoint_as_affine_tail_dev {mpl : Arm64.Obj.MultiPlacement}
    (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S out : BitVec 64} {uaff out_bs : List (BitVec 8)}
    {v29 v30 v28 v21 v20 v19 : BitVec 64} {F : Arm64.SepProp}
    (hrun : s.status = .Running) (hpc : s.pc = mpl.base 11 + 128#64) (hsp : s.sp = S - 272#64)
    (hal : (S - 272#64 &&& 15#64) = 0#64) (h19 : s.regs.regs 19#5 = out)
    (h29 : s.regs.regs 29#5 = S - 48#64) (hub : fe51LimbsBounded uaff (2 ^ 52)) (hlo : out_bs.length = 32)
    (hs : s.mem ⊨ ((S - 128#64) ↦ₛ uaff) ∗ (out ↦ₛ out_bs) ∗
      ((S - 48#64) ↦₆₄* [v29, v30, v28, v21, v20, v19]) ∗ F) :
    ∃ (rf : BitVec 5 → BitVec 64) (ps : Arm64.PState) (m' : Arm64.Memory),
      Arm64.Steps (x25519CliMultiLib.blockProgram mpl 11) s
        { s with pc := v30, regs := ⟨rf⟩, sp := S, pstate := ps, mem := m' } ∧
      rf 19#5 = v19 ∧ rf 20#5 = v20 ∧ rf 21#5 = v21 ∧ rf 28#5 = v28 ∧ rf 29#5 = v29 ∧
      rf 22#5 = s.regs.regs 22#5 ∧ rf 23#5 = s.regs.regs 23#5 ∧ rf 24#5 = s.regs.regs 24#5 ∧
      rf 25#5 = s.regs.regs 25#5 ∧ rf 26#5 = s.regs.regs 26#5 ∧ rf 27#5 = s.regs.regs 27#5 ∧
      m' ⊨ ((S - 128#64) ↦ₛ uaff) ∗ (out ↦ₛ natToLeBytes 32 (fe51ValOfBytes uaff % p25519)) ∗
        ((S - 48#64) ↦₆₄* [v29, v30, v28, v21, v20, v19]) ∗ F := by
  obtain ⟨sf, hst, rf, ps, m', hsf, r19, r20, r21, r28, r29, r22, r23, r24, r25, r26, r27, hF⟩ :=
    LP.aa_tail (sf := s) (Q := fun t => ∃ (rf : BitVec 5 → BitVec 64) (ps : Arm64.PState) (m' : Arm64.Memory),
      t = { s with pc := v30, regs := ⟨rf⟩, sp := S, pstate := ps, mem := m' } ∧
      rf 19#5 = v19 ∧ rf 20#5 = v20 ∧ rf 21#5 = v21 ∧ rf 28#5 = v28 ∧ rf 29#5 = v29 ∧
      rf 22#5 = s.regs.regs 22#5 ∧ rf 23#5 = s.regs.regs 23#5 ∧ rf 24#5 = s.regs.regs 24#5 ∧
      rf 25#5 = s.regs.regs 25#5 ∧ rf 26#5 = s.regs.regs 26#5 ∧ rf 27#5 = s.regs.regs 27#5 ∧
      m' ⊨ ((S - 128#64) ↦ₛ uaff) ∗ (out ↦ₛ natToLeBytes 32 (fe51ValOfBytes uaff % p25519)) ∗
        ((S - 48#64) ↦₆₄* [v29, v30, v28, v21, v20, v19]) ∗ F)
    hP hCL hrun (Arm64.Memory.KeepsFrozen.refl _) hal h19 h29 hub hlo hs
    (fun m' rf ps a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 hF _ => ⟨rf, ps, m', rfl, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hF⟩)
  subst hsf
  have e : LP.mkS s (mpl.base 11 + 128#64) s.regs.regs (S - 272#64) s.pstate s.mem s.vregs.regs = s := by
    rw [← hpc, ← hsp]; rfl
  rw [e] at hst
  exact ⟨rf, ps, m', hst, r19, r20, r21, r28, r29, r22, r23, r24, r25, r26, r27, hF⟩

end X25519Dalek

end
end

section
open X25519Dalek

theorem solution {mpl : Arm64.Obj.MultiPlacement}
    (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S out : BitVec 64} {uaff out_bs : List (BitVec 8)}
    {v29 v30 v28 v21 v20 v19 : BitVec 64} {F : Arm64.SepProp}
    (hrun : s.status = .Running) (hpc : s.pc = mpl.base 11 + 128#64) (hsp : s.sp = S - 272#64)
    (hal : (S - 272#64 &&& 15#64) = 0#64) (h19 : s.regs.regs 19#5 = out)
    (h29 : s.regs.regs 29#5 = S - 48#64) (hub : fe51LimbsBounded uaff (2 ^ 52)) (hlo : out_bs.length = 32)
    (hs : s.mem ⊨ ((S - 128#64) ↦ₛ uaff) ∗ (out ↦ₛ out_bs) ∗
      ((S - 48#64) ↦₆₄* [v29, v30, v28, v21, v20, v19]) ∗ F) :
    ∃ (rf : BitVec 5 → BitVec 64) (ps : Arm64.PState) (m' : Arm64.Memory),
      Arm64.Steps (x25519CliMultiLib.blockProgram mpl 11) s
        { s with pc := v30, regs := ⟨rf⟩, sp := S, pstate := ps, mem := m' } ∧
      rf 19#5 = v19 ∧ rf 20#5 = v20 ∧ rf 21#5 = v21 ∧ rf 28#5 = v28 ∧ rf 29#5 = v29 ∧
      rf 22#5 = s.regs.regs 22#5 ∧ rf 23#5 = s.regs.regs 23#5 ∧ rf 24#5 = s.regs.regs 24#5 ∧
      rf 25#5 = s.regs.regs 25#5 ∧ rf 26#5 = s.regs.regs 26#5 ∧ rf 27#5 = s.regs.regs 27#5 ∧
      m' ⊨ ((S - 128#64) ↦ₛ uaff) ∗ (out ↦ₛ natToLeBytes 32 (fe51ValOfBytes uaff % p25519)) ∗
        ((S - 48#64) ↦₆₄* [v29, v30, v28, v21, v20, v19]) ∗ F := by
  apply X25519Dalek.projectivePoint_as_affine_tail_dev <;> assumption

end
