-- Prove2me | solution 1 for X25519Dalek.differentialAddAndDouble_828_ret
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T20:51:29.24485+00:00
-- url     : https://prove2.me/submissions/0d956b68-0d76-4672-8d56-256bf89ebd34

import Definitions.Def_X25519Dalek_PlacedObj
import Definitions.Def_X25519Dalek_Rfc7748
import Definitions.Def_X25519Dalek_Spec
import Definitions.Def_Arm64_ISA_Semantics
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

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP

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

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

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

end X25519Dalek.LP

end
end

section
section
/-! # One lemma per instruction shape

Each lemma executes one instruction of a given shape from an abstract state `mkS s0 pc r sp ps m v`,
so a block proof applies a lemma per instruction instead of re-running the evaluator `simp` each time
(smaller proof terms). Register operands other than `xzr`/`sp` carry side conditions `≠ 31#5`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64

section
variable {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem y_ldp_sp {d1 d2 : BitVec 5} {off A A8 w1 w2 : BitVec 64} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (hA8 : A + 8#64 = A8) (c1 : m.canRead A 8 = true) (c2 : m.canRead A8 8 = true) (e1 : m.read64 A = w1) (e2 : m.read64 A8 = w2) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.Offset .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) (upd (upd r d1 w1) d2 w2) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd1, hd2, hal, hA, hA8, c1, c2, e1, e2]
  exact h

theorem y_ldr_r {d b : BitVec 5} {off A w : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5) (hA : r b + off = A) (c : m.canRead A 8 = true) (e : m.read64 A = w) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W64 .X64 false (.gpr d) (.UnscaledOffset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d w) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, hb, hA, c, e]
  exact h

theorem y_ldr_sp {d : BitVec 5} {off A w : BitVec 64} (hd : d ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (c : m.canRead A 8 = true) (e : m.read64 A = w) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W64 .X64 false (.gpr d) (.Offset .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d w) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, hal, hA, c, e]
  exact h

theorem y_str_ro {t b : BitVec 5} {off A : BitVec 64} (ht : t ≠ 31#5) (hb : b ≠ 31#5) (hA : r b + off = A) (c : m.canWrite A 8 = true) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 (.gpr t) (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps (m.write64 A (r t)) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ht, hb, hA, c]
  exact h

theorem y_addi_sp {d : BitVec 5} {k : BitVec 12} (hd : d ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD (.gpr d) .sp k false))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (sp + k.setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, BitVec.truncate_eq_setWidth]
  exact h

end

theorem pc4 (b : BitVec 64) (k l : Nat) (h : k + 4 = l) :
    b + BitVec.ofNat 64 k + 4#64 = b + BitVec.ofNat 64 l := by
  subst h; rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem w8 (a : BitVec 64) (i : Nat) :
    a + BitVec.ofNat 64 (8 * i) + 8#64 = a + BitVec.ofNat 64 (8 * (i + 1)) := by
  rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
  congr 2

/-- Word `i` of a word list at position 1, 2, 3 or 4 of a separating conjunction. -/
theorem wf1 {m : Memory} {a : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (i : Nat) (hi : i < ws.length) :
    m.read64 (a + BitVec.ofNat 64 (8 * i)) = ws.getD i 0 ∧
      m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true := by
  obtain ⟨h1, h2, -⟩ := sat_words_read hs i hi
  refine ⟨?_, h2⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

section
variable {p : Program} {s0 : State} {pc pc' : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem x_ldp_sp {d1 d2 : BitVec 5} {off a w1 w2 : BitVec 64} {i : Nat} {B : BitVec 64} (hd1 : d1 ≠ 31#5)
    (hd2 : d2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * i))
    (f1 : m.read64 (a + BitVec.ofNat 64 (8 * i)) = w1 ∧ m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true)
    (hB : a + BitVec.ofNat 64 (8 * (i + 1)) = B)
    (f2 : m.read64 B = w2 ∧ m.canRead B 8 = true)
    (h : Reach p (mkS s0 pc' (upd (upd r d1 w1) d2 w2) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; exact y_ldp_sp hd1 hd2 hal hA ((w8 a i).trans hB) f1.2 f2.2 f1.1 f2.1 hrun hf h

end

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
variable {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem y_ldrq_u {t b : BitVec 5} {off A lo hi : BitVec 64} (hb : b ≠ 31#5)
    (hA : r b + off = A) (c : m.canRead A 16 = true) (e1 : m.read64 A = lo) (e2 : m.read64 (A + 8#64) = hi)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldrSimd .Q128 t (.UnscaledOffset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps m (upd v t (hi ++ lo))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, c, e1, e2]
  exact h

theorem y_ldrq_o {t b : BitVec 5} {off A lo hi : BitVec 64} (hb : b ≠ 31#5)
    (hA : r b + off = A) (c : m.canRead A 16 = true) (e1 : m.read64 A = lo) (e2 : m.read64 (A + 8#64) = hi)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldrSimd .Q128 t (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps m (upd v t (hi ++ lo))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, c, e1, e2]
  exact h

theorem y_ldpq_o {t1 t2 b : BitVec 5} {off A A16 lo1 hi1 lo2 hi2 : BitVec 64} (hb : b ≠ 31#5)
    (hA : r b + off = A) (hA16 : A + 16#64 = A16) (c1 : m.canRead A 16 = true)
    (c2 : m.canRead A16 16 = true) (e1 : m.read64 A = lo1) (e2 : m.read64 (A + 8#64) = hi1)
    (e3 : m.read64 A16 = lo2) (e4 : m.read64 (A16 + 8#64) = hi2)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldpSimd .Q128 t1 t2 (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps m (upd (upd v t1 (hi1 ++ lo1)) t2 (hi2 ++ lo2))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, hA16, c1, c2, e1, e2, e3, e4]
  exact h

theorem y_strq_u {t b : BitVec 5} {off A A8 lo hi : BitVec 64} (hb : b ≠ 31#5)
    (hA : r b + off = A) (hA8 : A + 8#64 = A8) (c : m.canWrite A 16 = true) (ev : v t = hi ++ lo)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.UnscaledOffset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps ((m.write64 A lo).write64 A8 hi) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, hA8, c, ev]
  exact h

theorem y_stpq_o {t1 t2 b : BitVec 5} {off A A8 A16 A24 lo1 hi1 lo2 hi2 : BitVec 64} (hb : b ≠ 31#5)
    (hA : r b + off = A) (hA8 : A + 8#64 = A8) (hA16 : A + 16#64 = A16) (hA24 : A16 + 8#64 = A24)
    (c1 : m.canWrite A 16 = true) (c2 : m.canWrite A16 16 = true) (ev1 : v t1 = hi1 ++ lo1)
    (ev2 : v t2 = hi2 ++ lo2) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stpSimd .Q128 t1 t2 (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps ((((m.write64 A lo1).write64 A8 hi1).write64 A16 lo2).write64 A24 hi2) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, hA8, hA16, hA24, c1, c2, ev1, ev2]
  exact h

end

section
variable {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem y_ldp_post {d1 d2 : BitVec 5} {off w1 w2 : BitVec 64} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5)
    (hal : (sp &&& 15#64) = 0#64) (c1 : m.canRead sp 8 = true) (c2 : m.canRead (sp + 8#64) 8 = true)
    (e1 : m.read64 sp = w1) (e2 : m.read64 (sp + 8#64) = w2) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.PostIndex .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) (upd (upd r d1 w1) d2 w2) (sp + off) ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd1, hd2, hal, c1, c2, e1, e2]
  exact h

theorem y_addsp {k : BitVec 12} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD .sp .sp k false))
    (h : Reach p (mkS s0 (pc + 4#64) r (sp + k.setWidth 64) ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', BitVec.truncate_eq_setWidth]
  exact h

theorem y_ret (hrun : s0.status = .Running) (hf : p.fetchMem m pc = some (.ret (.gpr 30#5)))
    (h : Reach p (mkS s0 (r 30#5) r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel']
  exact h

end

end X25519Dalek.LP

end
end

section
section
/-! # Block 12: per-offset instruction fetch (generated by tools_ladder/gen_code.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

theorem blk12 : blk 12 = x25519CliBlk12 := rfl

theorem len12 : x25519CliBlk12.code.length = 952 := by decide +kernel

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (j : Nat) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem c12_828 : (bprog mpl j).fetchMem m (mpl.base 12 + 828#64) =
    some (Instr.ldrSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffff58#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 828) (inst := (Instr.ldrSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffff58#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_832 : (bprog mpl j).fetchMem m (mpl.base 12 + 832#64) =
    some (Instr.ldrSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffff68#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 832) (inst := (Instr.ldrSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffff68#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_836 : (bprog mpl j).fetchMem m (mpl.base 12 + 836#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.sp) 0x1c0#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 836) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.sp) 0x1c0#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_840 : (bprog mpl j).fetchMem m (mpl.base 12 + 840#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.sp) 0x1c0#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 840) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.sp) 0x1c0#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_844 : (bprog mpl j).fetchMem m (mpl.base 12 + 844#64) =
    some (Instr.ldrSimd (SimdMemSize.Q128) 0x02#5 (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffa8#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 844) (inst := (Instr.ldrSimd (SimdMemSize.Q128) 0x02#5 (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffa8#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_848 : (bprog mpl j).fetchMem m (mpl.base 12 + 848#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x14#5) 0x0000000000000000#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 848) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x14#5) 0x0000000000000000#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_852 : (bprog mpl j).fetchMem m (mpl.base 12 + 852#64) =
    some (Instr.ldrSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffb8#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 852) (inst := (Instr.ldrSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffb8#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_856 : (bprog mpl j).fetchMem m (mpl.base 12 + 856#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x02#5 (AddrMode.UnscaledOffset (Reg.gpr 0x14#5) 0x0000000000000028#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 856) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x02#5 (AddrMode.UnscaledOffset (Reg.gpr 0x14#5) 0x0000000000000028#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_860 : (bprog mpl j).fetchMem m (mpl.base 12 + 860#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x14#5) 0x0000000000000038#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 860) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x14#5) 0x0000000000000038#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_864 : (bprog mpl j).fetchMem m (mpl.base 12 + 864#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x08#5) 0x0000000000000000#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 864) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x08#5) 0x0000000000000000#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_868 : (bprog mpl j).fetchMem m (mpl.base 12 + 868#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000000#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 868) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x00#5 (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000000#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_872 : (bprog mpl j).fetchMem m (mpl.base 12 + 872#64) =
    some (Instr.ldrSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.Offset (Reg.gpr 0x08#5) 0x0000000000000100#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 872) (inst := (Instr.ldrSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.Offset (Reg.gpr 0x08#5) 0x0000000000000100#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_876 : (bprog mpl j).fetchMem m (mpl.base 12 + 876#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x08#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffff78#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 876) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x08#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffff78#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_880 : (bprog mpl j).fetchMem m (mpl.base 12 + 880#64) =
    some (Instr.ldrSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.Offset (Reg.gpr 0x09#5) 0x00000000000000f0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 880) (inst := (Instr.ldrSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.Offset (Reg.gpr 0x09#5) 0x00000000000000f0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_884 : (bprog mpl j).fetchMem m (mpl.base 12 + 884#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x09#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffc8#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 884) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x09#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffc8#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_888 : (bprog mpl j).fetchMem m (mpl.base 12 + 888#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x14#5) 0x0000000000000020#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 888) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x14#5) 0x0000000000000020#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_892 : (bprog mpl j).fetchMem m (mpl.base 12 + 892#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x00000000000001e0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 892) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x00000000000001e0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_896 : (bprog mpl j).fetchMem m (mpl.base 12 + 896#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x14#5) 0x0000000000000048#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 896) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x14#5) 0x0000000000000048#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_900 : (bprog mpl j).fetchMem m (mpl.base 12 + 900#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x09#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xfffffffffffffff0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 900) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x09#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xfffffffffffffff0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_904 : (bprog mpl j).fetchMem m (mpl.base 12 + 904#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.UnscaledOffset (Reg.gpr 0x13#5) 0x0000000000000038#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 904) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.UnscaledOffset (Reg.gpr 0x13#5) 0x0000000000000038#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_908 : (bprog mpl j).fetchMem m (mpl.base 12 + 908#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000020#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 908) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000020#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_912 : (bprog mpl j).fetchMem m (mpl.base 12 + 912#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000048#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 912) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000048#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_916 : (bprog mpl j).fetchMem m (mpl.base 12 + 916#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x13#5) 0x0000000000000028#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 916) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x13#5) 0x0000000000000028#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_920 : (bprog mpl j).fetchMem m (mpl.base 12 + 920#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.sp) (Reg.sp) 0x2e0#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 920) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.sp) (Reg.sp) 0x2e0#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_924 : (bprog mpl j).fetchMem m (mpl.base 12 + 924#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 924) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_928 : (bprog mpl j).fetchMem m (mpl.base 12 + 928#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 928) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_932 : (bprog mpl j).fetchMem m (mpl.base 12 + 932#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 932) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_936 : (bprog mpl j).fetchMem m (mpl.base 12 + 936#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 936) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_940 : (bprog mpl j).fetchMem m (mpl.base 12 + 940#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1c#5) (Reg.gpr 0x1b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000010#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 940) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1c#5) (Reg.gpr 0x1b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000010#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_944 : (bprog mpl j).fetchMem m (mpl.base 12 + 944#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.PostIndex (Reg.sp) 0x0000000000000060#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 944) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.PostIndex (Reg.sp) 0x0000000000000060#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_948 : (bprog mpl j).fetchMem m (mpl.base 12 + 948#64) =
    some (Instr.ret (Reg.gpr 0x1e#5)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 948) (inst := (Instr.ret (Reg.gpr 0x1e#5))) (by decide) rfl (by decide +kernel) hk
  exact this

end

end X25519Dalek.LP

end
end

section
section
/-! # Relocated `ADRP`/`ADD` (and their relaxed `NOP`/`ADR` form): loading a `.rodata` address

Decoding lemmas copied from the sibling batch's `Solutions/X25519DalekEdwards/Reloc.lean`, itself from
the zlib CRC-32 mission's `ZlibCrc32.Small.RelocBase`/`RelocTab`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj


section words
variable (D : BitVec 64)

end words



abbrev symA24 : String := "curve25519_dalek:.rodata..Lanon.35"

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (j : Nat) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

end

end X25519Dalek.LP

end
end

section
section
/-! # Calls to `mul` and `pow2k` with operands held as 64-bit word lists

The callee contracts speak of byte slices; a caller that keeps its field elements as five-word
lists (`a ↦₆₄* A`) calls through these lemmas, which do the conversion once. After the return the
register file is `csMerge r sf.regs.regs`: the callee-saved registers as before the call, the others
as the callee left them. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

end X25519Dalek.LP

end
end

section
section
/-! # More instruction-shape wrappers: stack-pointer arithmetic, pre/post-indexed pairs, `ret`,
128-bit loads and stores on word lists, and address normalisation `S - a + b = S - c + d` -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64

theorem aSS (S : BitVec 64) (a b c d : Nat)
    (h : BitVec.ofNat 64 b - BitVec.ofNat 64 a = BitVec.ofNat 64 d - BitVec.ofNat 64 c) :
    S - BitVec.ofNat 64 a + BitVec.ofNat 64 b = S - BitVec.ofNat 64 c + BitVec.ofNat 64 d := by
  have e1 : S - BitVec.ofNat 64 a + BitVec.ofNat 64 b = S + (BitVec.ofNat 64 b - BitVec.ofNat 64 a) := by abel
  have e2 : S - BitVec.ofNat 64 c + BitVec.ofNat 64 d = S + (BitVec.ofNat 64 d - BitVec.ofNat 64 c) := by abel
  rw [e1, e2, h]

theorem aSk (S : BitVec 64) (a c : Nat) (k : BitVec 12)
    (h : BitVec.ofNat 64 a - k.setWidth 64 = BitVec.ofNat 64 c) :
    S - BitVec.ofNat 64 a + k.setWidth 64 = S - BitVec.ofNat 64 c := by
  rw [← h]; try abel

theorem aSb (S : BitVec 64) (a b c : Nat) (h : BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 c) :
    S - BitVec.ofNat 64 a + BitVec.ofNat 64 b = S - BitVec.ofNat 64 c := by
  rw [← h]; try abel

theorem aS0 (S : BitVec 64) (a : Nat) : S - BitVec.ofNat 64 a = S - BitVec.ofNat 64 a + BitVec.ofNat 64 (8 * 0) := by
  simp

theorem aS16 (A : BitVec 64) (i : Nat) :
    A + BitVec.ofNat 64 (8 * i) + 16#64 = A + BitVec.ofNat 64 (8 * (i + 2)) := by
  rw [BitVec.add_assoc, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
  congr 2

section
variable {p : Program} {s0 : State} {pc pc' : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem x_addi_sp2 {d : BitVec 5} {k : BitVec 12} {x : BitVec 64} (hd : d ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD (.gpr d) .sp k false))
    (hpc : pc + 4#64 = pc') (hx : sp + k.setWidth 64 = x)
    (h : Reach p (mkS s0 pc' (upd r d x) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc hx; exact y_addi_sp hd hrun hf h

theorem x_addsp {k : BitVec 12} {sp' : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD .sp .sp k false))
    (hpc : pc + 4#64 = pc') (hx : sp + k.setWidth 64 = sp')
    (h : Reach p (mkS s0 pc' r sp' ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc hx; exact y_addsp hrun hf h

theorem x_ret {x : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ret (.gpr 30#5))) (ex : r 30#5 = x)
    (h : Reach p (mkS s0 x r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst ex; exact y_ret hrun hf h

/-- `ldp d1, d2, [sp], #off` from words `i`, `i + 1` (`sp` is word `i`'s address). -/
theorem x_ldp_post {d1 d2 : BitVec 5} {off a w1 w2 sp' : BitVec 64} {i : Nat} (hd1 : d1 ≠ 31#5)
    (hd2 : d2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.PostIndex .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp = a + BitVec.ofNat 64 (8 * i)) (hsp : sp + off = sp')
    (f1 : m.read64 (a + BitVec.ofNat 64 (8 * i)) = w1 ∧ m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true)
    (f2 : m.read64 (a + BitVec.ofNat 64 (8 * (i + 1))) = w2 ∧
      m.canRead (a + BitVec.ofNat 64 (8 * (i + 1))) 8 = true)
    (h : Reach p (mkS s0 pc' (upd (upd r d1 w1) d2 w2) sp' ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc hsp hA
  rw [← w8] at f2
  exact y_ldp_post hd1 hd2 hal f1.2 f2.2 f1.1 f2.1 hrun hf h

theorem x_ldr_u {d b : BitVec 5} {off x a w : BitVec 64} {i : Nat} (hd : d ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W64 .X64 false (.gpr d) (.UnscaledOffset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (f1 : m.read64 (a + BitVec.ofNat 64 (8 * i)) = w ∧ m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true)
    (h : Reach p (mkS s0 pc' (upd r d w) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_ldr_r hd hb hA f1.2 f1.1 hrun hf h

theorem x_ldr_sp {d : BitVec 5} {off a w : BitVec 64} {i : Nat} (hd : d ≠ 31#5)
    (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W64 .X64 false (.gpr d) (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * i))
    (f1 : m.read64 (a + BitVec.ofNat 64 (8 * i)) = w ∧ m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true)
    (h : Reach p (mkS s0 pc' (upd r d w) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; exact y_ldr_sp hd hal hA f1.2 f1.1 hrun hf h

theorem x_str_o {t b : BitVec 5} {off x a v1 : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    {i : Nat} (ht : t ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 (.gpr t) (.Offset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hi : i < ws.length) (e1 : r t = v1)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* ws.set i v1) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex e1
  obtain ⟨-, -, c1⟩ := sat_words_read hs i hi
  refine y_str_ro ht hb hA c1 hrun hf ?_
  exact Reach.wr64 i hs rfl hi h

theorem x_ldrq_u {t b : BitVec 5} {off x a lo hi : BitVec 64} {i : Nat} (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldrSimd .Q128 t (.UnscaledOffset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (f1 : m.read64 (a + BitVec.ofNat 64 (8 * i)) = lo ∧ m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true)
    (f2 : m.read64 (a + BitVec.ofNat 64 (8 * (i + 1))) = hi ∧
      m.canRead (a + BitVec.ofNat 64 (8 * (i + 1))) 8 = true)
    (h : Reach p (mkS s0 pc' r sp ps m (upd v t (hi ++ lo))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex
  rw [← w8] at f2
  refine y_ldrq_u hb hA (canRead16 f1.2 f2.2) f1.1 f2.1 hrun hf h

theorem x_ldrq_o {t b : BitVec 5} {off x a lo hi : BitVec 64} {i : Nat} (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldrSimd .Q128 t (.Offset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (f1 : m.read64 (a + BitVec.ofNat 64 (8 * i)) = lo ∧ m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true)
    (f2 : m.read64 (a + BitVec.ofNat 64 (8 * (i + 1))) = hi ∧
      m.canRead (a + BitVec.ofNat 64 (8 * (i + 1))) 8 = true)
    (h : Reach p (mkS s0 pc' r sp ps m (upd v t (hi ++ lo))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex
  rw [← w8] at f2
  refine y_ldrq_o hb hA (canRead16 f1.2 f2.2) f1.1 f2.1 hrun hf h

theorem x_ldpq_o {t1 t2 b : BitVec 5} {off x a lo1 hi1 lo2 hi2 : BitVec 64} {i : Nat} (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldpSimd .Q128 t1 t2 (.Offset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (f1 : m.read64 (a + BitVec.ofNat 64 (8 * i)) = lo1 ∧ m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true)
    (f2 : m.read64 (a + BitVec.ofNat 64 (8 * (i + 1))) = hi1 ∧
      m.canRead (a + BitVec.ofNat 64 (8 * (i + 1))) 8 = true)
    (f3 : m.read64 (a + BitVec.ofNat 64 (8 * (i + 2))) = lo2 ∧
      m.canRead (a + BitVec.ofNat 64 (8 * (i + 2))) 8 = true)
    (f4 : m.read64 (a + BitVec.ofNat 64 (8 * (i + 3))) = hi2 ∧
      m.canRead (a + BitVec.ofNat 64 (8 * (i + 3))) 8 = true)
    (h : Reach p (mkS s0 pc' r sp ps m (upd (upd v t1 (hi1 ++ lo1)) t2 (hi2 ++ lo2))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex
  have g2 : m.canRead (a + BitVec.ofNat 64 (8 * i) + 8#64) 8 = true := by rw [w8]; exact f2.2
  have g4 : m.canRead (a + BitVec.ofNat 64 (8 * (i + 2)) + 8#64) 8 = true := by rw [w8]; exact f4.2
  have r2 : m.read64 (a + BitVec.ofNat 64 (8 * i) + 8#64) = hi1 := by rw [w8]; exact f2.1
  have r4 : m.read64 (a + BitVec.ofNat 64 (8 * (i + 2)) + 8#64) = hi2 := by rw [w8]; exact f4.1
  exact y_ldpq_o hb hA (aS16 a i) (canRead16 f1.2 g2) (canRead16 f3.2 g4) f1.1 r2 f3.1 r4 hrun hf h

theorem x_strq_u {t b : BitVec 5} {off x a lo hi : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    {i : Nat} (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.UnscaledOffset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hl : i + 1 < ws.length) (ev : v t = hi ++ lo)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (ws.set i lo).set (i + 1) hi) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex
  obtain ⟨-, -, c1⟩ := sat_words_read hs i (by omega)
  obtain ⟨-, -, c2⟩ := sat_words_read hs (i + 1) hl
  rw [← w8] at c2
  refine y_strq_u hb hA (w8 a i) (canWrite16 c1 c2) ev hrun hf ?_
  exact Reach.wr64x2 i hs rfl rfl hl h

theorem x_stpq_o {t1 t2 b : BitVec 5} {off x a lo1 hi1 lo2 hi2 : BitVec 64} {ws : List (BitVec 64)}
    {F : SepProp} {i : Nat} (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stpSimd .Q128 t1 t2 (.Offset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hi : i + 3 < ws.length) (ev1 : v t1 = hi1 ++ lo1)
    (ev2 : v t2 = hi2 ++ lo2)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (((ws.set i lo1).set (i + 1) hi1).set (i + 2) lo2).set (i + 3) hi2) ∗ F) →
      m.KeepsFrozen m' → Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex
  obtain ⟨-, -, c1⟩ := sat_words_read hs i (by omega)
  obtain ⟨-, -, c2⟩ := sat_words_read hs (i + 1) (by omega)
  obtain ⟨-, -, c3⟩ := sat_words_read hs (i + 2) (by omega)
  obtain ⟨-, -, c4⟩ := sat_words_read hs (i + 3) hi
  have g2 : m.canWrite (a + BitVec.ofNat 64 (8 * i) + 8#64) 8 = true := by rw [w8]; exact c2
  have g4 : m.canWrite (a + BitVec.ofNat 64 (8 * (i + 2)) + 8#64) 8 = true := by rw [w8]; exact c4
  refine y_stpq_o hb hA (w8 a i) (aS16 a i) (w8 a (i + 2)) (canWrite16 c1 g2) (canWrite16 c3 g4) ev1 ev2
    hrun hf ?_
  exact Reach.wr64x4 i hs rfl rfl rfl rfl hi h


end


theorem reach_reg {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
    {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop} {i : BitVec 5} {x : BitVec 64}
    (h : r i = x) (hr : Reach p (mkS s0 pc (upd r i x) sp ps m v) Q) : Reach p (mkS s0 pc r sp ps m v) Q := by
  have e : upd r i x = r := by
    funext k; simp only [upd]; split_ifs with hk
    · subst hk; exact h.symm
    · rfl
  rwa [e] at hr


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

end X25519Dalek.LP

end
end

section
section
/-! # Reordering separating conjunctions (generated): `pickN` moves the `N`-th conjunct to the front.

Same statements as the sibling batch's `Solutions/X25519DalekField/G/P22Sep.lean`. -/

set_option autoImplicit false

namespace X25519Dalek.LP

open Arm64

theorem pick2 (A1 A2 R : SepProp) : (A1 ∗ A2 ∗ R) = (A2 ∗ A1 ∗ R) := by ac_rfl
theorem pick4 (A1 A2 A3 A4 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ R) = (A4 ∗ A1 ∗ A2 ∗ A3 ∗ R) := by ac_rfl
theorem pick6 (A1 A2 A3 A4 A5 A6 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ R) = (A6 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ R) := by ac_rfl
theorem pick7 (A1 A2 A3 A4 A5 A6 A7 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ R) = (A7 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ R) := by ac_rfl
theorem pick8 (A1 A2 A3 A4 A5 A6 A7 A8 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ R) = (A8 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ R) := by ac_rfl
theorem pick9 (A1 A2 A3 A4 A5 A6 A7 A8 A9 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ R) = (A9 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ R) := by ac_rfl
theorem pick10 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ R) = (A10 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ R) := by ac_rfl
theorem pick11 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ R) = (A11 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ R) := by ac_rfl
theorem pick12 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ R) = (A12 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ R) := by ac_rfl
theorem pick14 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ R) = (A14 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ R) := by ac_rfl
theorem pick15 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ R) = (A15 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ R) := by ac_rfl
theorem pick16 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ R) = (A16 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ R) := by ac_rfl
theorem pick17 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ R) = (A17 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ R) := by ac_rfl
theorem pick21 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ R) = (A21 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ R) := by ac_rfl
theorem pick23 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ R) = (A23 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ R) := by ac_rfl
theorem pick24 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ R) = (A24 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ R) := by ac_rfl
theorem pick25 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ R) = (A25 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ R) := by ac_rfl

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

/-! ## Field arithmetic -/

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP

end X25519Dalek.LP

namespace X25519Dalek.LP

end X25519Dalek.LP

end
end

section
section
/-! # `FieldElement51` add, subtract (with bias) and weak reduction: bounds and values mod p

Ported from google-deepmind/code-verification @ 8c8d371f (Apache-2.0),
`LibsignalBinary/Proofs/HookDischarge/CryptoX25519/Shared51/SliceBase.lean` (lines 156-432),
unchanged except for the namespace. -/

set_option autoImplicit false

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg


end X25519Dalek.LP

end
end

section
section
/-! # `FieldElement51` buffers held as five 64-bit words

`fe51LimbsBounded` and `fe51ValOfBytes` of `[w0, …, w4].flatMap unpack64` in terms of the words. -/

set_option autoImplicit false

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg

theorem pack64_unpack64 (w : BitVec 64) : pack64 (unpack64 w) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack64, unpack64, List.getD_cons_zero, List.getD_cons_succ, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

theorem chunks64_flatMap : ∀ (ws : List (BitVec 64)), chunks64 (ws.flatMap unpack64) ws.length = ws
  | [] => rfl
  | w :: ws => by
    simp only [List.flatMap_cons, List.length_cons, chunks64]
    rw [List.take_left' (unpack64_length w), List.drop_left' (unpack64_length w), pack64_unpack64,
      chunks64_flatMap ws]

theorem readLE_words (ws : List (BitVec 64)) (i : Nat) (hi : i < ws.length) :
    ByteSlice.readLE (ws.flatMap unpack64) (8 * i) 8 = ws[i] := by
  have h := chunks64_getElem ws.length (ws.flatMap unpack64) i (by rw [chunks64_length]; exact hi)
  rw [← h]
  congr 1
  · exact chunks64_flatMap ws

theorem lbw (w0 w1 w2 w3 w4 : BitVec 64) (B : Nat) :
    fe51LimbsBounded ([w0, w1, w2, w3, w4].flatMap unpack64) B ↔
      (w0.toNat < B ∧ w1.toNat < B ∧ w2.toNat < B ∧ w3.toNat < B ∧ w4.toNat < B) := by
  have e0 := readLE_words [w0, w1, w2, w3, w4] 0 (by simp)
  have e1 := readLE_words [w0, w1, w2, w3, w4] 1 (by simp)
  have e2 := readLE_words [w0, w1, w2, w3, w4] 2 (by simp)
  have e3 := readLE_words [w0, w1, w2, w3, w4] 3 (by simp)
  have e4 := readLE_words [w0, w1, w2, w3, w4] 4 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2 e3 e4
  unfold fe51LimbsBounded
  rw [e0, e1, e2, e3, e4]
  simp

theorem valw (w0 w1 w2 w3 w4 : BitVec 64) :
    fe51ValOfBytes ([w0, w1, w2, w3, w4].flatMap unpack64) = fe51Val w0 w1 w2 w3 w4 := by
  have e0 := readLE_words [w0, w1, w2, w3, w4] 0 (by simp)
  have e1 := readLE_words [w0, w1, w2, w3, w4] 1 (by simp)
  have e2 := readLE_words [w0, w1, w2, w3, w4] 2 (by simp)
  have e3 := readLE_words [w0, w1, w2, w3, w4] 3 (by simp)
  have e4 := readLE_words [w0, w1, w2, w3, w4] 4 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2 e3 e4
  unfold fe51ValOfBytes
  rw [e0, e1, e2, e3, e4]

end X25519Dalek.LP

end
end

section
section
/-! # The field additions and subtractions of `differential_add_and_double`, as word equations

`add_slot`: five limb-wise additions. `sub_reduce_slot`: the biased subtraction `a - b + 16p` followed by
`FieldElement51::reduce` (carry chain with the top carry times 19), in the exact shape the compiled code
computes it (one equation per instruction). Both give limb bounds and the value mod `p`, from DeepMind's
`fe51Add_*`, `fe51Sub_val_mod`, `fe51Reduce_*` (FeArith.lean). -/

set_option autoImplicit false

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg

end X25519Dalek.LP

end
end

section
section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

set_option maxHeartbeats 8000000 in
theorem d12_s10 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {S Pb Qb u1 : BitVec 64} {F : SepProp} {Q : State → Prop}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 uw0 uw1 uw2 uw3 uw4 : BitVec 64}
    {vo : BitVec 5 → BitVec 128} {c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 : BitVec 64}
    (hal : (S &&& 15#64 == 0#64) = true)
    (hPU : fe51LimbsBounded ([p0, p1, p2, p3, p4].flatMap unpack64) (2 ^ 53))
    (hPW : fe51LimbsBounded ([p5, p6, p7, p8, p9].flatMap unpack64) (2 ^ 53))
    (hQU : fe51LimbsBounded ([q0, q1, q2, q3, q4].flatMap unpack64) (2 ^ 53))
    (hQW : fe51LimbsBounded ([q5, q6, q7, q8, q9].flatMap unpack64) (2 ^ 53))
    (hU1 : fe51LimbsBounded ([uw0, uw1, uw2, uw3, uw4].flatMap unpack64) (2 ^ 54))
    {sb : State} {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {o166 o167 o168 o169 o170 o235 o236 o237 o238 o239 t452 t476 t488 t492 t484 t768 t772 t784 t788 t792 o220 o221 o222 o223 o224 o181 o182 o183 o184 o185 o64 o65 o66 o67 o68 o79 o80 o81 o82 o83 o196 o197 o198 o199 o200 t632 t644 t660 t676 t680 t560 t564 t584 t588 t616 o151 o152 o153 o154 o155 o118 o119 o120 o121 o122 o103 o104 o105 o106 o107 t144 t164 t172 t180 t188 t232 t228 t248 t256 t276 t76 t96 t100 t120 t68 t316 t328 t324 t336 t348 g1 : BitVec 64}
    (hrun : sb.status = .Running) (kf : m0.KeepsFrozen m) (hvs : VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩) (hr19 : r 19#5 = Qb) (hr20 : r 20#5 = Pb) (hr21 : r 21#5 = o80) (hr22 : r 22#5 = 0x007ffffffffffff0#64) (hr23 : r 23#5 = o79) (hr24 : r 24#5 = 36028797018963664#64) (hr25 : r 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64)) (hr26 : r 26#5 = o83) (hr27 : r 27#5 = o82) (hr28 : r 28#5 = o81) (hr29 : r 29#5 = (S - 96#64)) (bd_Tmp : fe51LimbsBounded ([o166, o167, o168, o169, o170].flatMap unpack64) (2 ^ 52)) (bd_W3 : fe51LimbsBounded ([o235, o236, o237, o238, o239].flatMap unpack64) (2 ^ 52)) (bd_E : fe51LimbsBounded ([t452, t476, t488, t492, t484].flatMap unpack64) (2 ^ 52)) (bd_A24EpBB : fe51LimbsBounded ([t768, t772, t784, t788, t792].flatMap unpack64) (2 ^ 53)) (bd_W2 : fe51LimbsBounded ([o220, o221, o222, o223, o224].flatMap unpack64) (2 ^ 52)) (bd_A24E : fe51LimbsBounded ([o181, o182, o183, o184, o185].flatMap unpack64) (2 ^ 52)) (bd_AA : fe51LimbsBounded ([o64, o65, o66, o67, o68].flatMap unpack64) (2 ^ 52)) (bd_BB : fe51LimbsBounded ([o79, o80, o81, o82, o83].flatMap unpack64) (2 ^ 52)) (bd_U2 : fe51LimbsBounded ([o196, o197, o198, o199, o200].flatMap unpack64) (2 ^ 52)) (bd_Diff : fe51LimbsBounded ([t632, t644, t660, t676, t680].flatMap unpack64) (2 ^ 52)) (bd_Sum : fe51LimbsBounded ([t560, t564, t584, t588, t616].flatMap unpack64) (2 ^ 53)) (bd_U3 : fe51LimbsBounded ([o151, o152, o153, o154, o155].flatMap unpack64) (2 ^ 52)) (bd_CB : fe51LimbsBounded ([o118, o119, o120, o121, o122].flatMap unpack64) (2 ^ 52)) (bd_DA : fe51LimbsBounded ([o103, o104, o105, o106, o107].flatMap unpack64) (2 ^ 52)) (bd_B : fe51LimbsBounded ([t144, t164, t172, t180, t188].flatMap unpack64) (2 ^ 52)) (bd_C : fe51LimbsBounded ([t232, t228, t248, t256, t276].flatMap unpack64) (2 ^ 54)) (bd_A : fe51LimbsBounded ([t76, t96, t100, t120, t68].flatMap unpack64) (2 ^ 54)) (bd_D : fe51LimbsBounded ([t316, t328, t324, t336, t348].flatMap unpack64) (2 ^ 52)) (hs : m ⊨ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F)
    (hcont : ∀ (sb : State) (r : BitVec 5 → BitVec 64) (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128), (sb.status = .Running) → (m0.KeepsFrozen m) → (VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩) → (r 19#5 = c19) → (r 20#5 = c20) → (r 21#5 = c21) → (r 22#5 = c22) → (r 23#5 = c23) → (r 24#5 = c24) → (r 25#5 = c25) → (r 26#5 = c26) → (r 27#5 = c27) → (r 28#5 = c28) → (r 29#5 = c29) → (r 30#5 = c30) → (fe51LimbsBounded ([o235, o236, o237, o238, o239].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o151, o152, o153, o154, o155].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o220, o221, o222, o223, o224].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o196, o197, o198, o199, o200].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o166, o167, o168, o169, o170].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([t452, t476, t488, t492, t484].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([t768, t772, t784, t788, t792].flatMap unpack64) (2 ^ 53)) → (fe51LimbsBounded ([o181, o182, o183, o184, o185].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o64, o65, o66, o67, o68].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o79, o80, o81, o82, o83].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([t632, t644, t660, t676, t680].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([t560, t564, t584, t588, t616].flatMap unpack64) (2 ^ 53)) → (fe51LimbsBounded ([o118, o119, o120, o121, o122].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o103, o104, o105, o106, o107].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([t144, t164, t172, t180, t188].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([t232, t228, t248, t256, t276].flatMap unpack64) (2 ^ 54)) → (fe51LimbsBounded ([t76, t96, t100, t120, t68].flatMap unpack64) (2 ^ 54)) → (fe51LimbsBounded ([t316, t328, t324, t336, t348].flatMap unpack64) (2 ^ 52)) → (m ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ (Qb ↦₆₄* [o151, o152, o153, o154, o155, o235, o236, o237, o238, o239]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ (Pb ↦₆₄* [o196, o197, o198, o199, o200, o220, o221, o222, o223, o224]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F) → Reach (bprog mpl 12) (mkS sb (r 30#5) r (S - 0#64) ps m v) Q) :
    Reach (bprog mpl 12) (mkS sb (mpl.base 12 + BitVec.ofNat 64 828) r (S - 832#64) ps m v) Q := by
  refine reach_reg (i := 19#5) hr19 ?_
  refine reach_reg (i := 20#5) hr20 ?_
  refine reach_reg (i := 21#5) hr21 ?_
  refine reach_reg (i := 22#5) hr22 ?_
  refine reach_reg (i := 23#5) hr23 ?_
  refine reach_reg (i := 24#5) hr24 ?_
  refine reach_reg (i := 25#5) hr25 ?_
  refine reach_reg (i := 26#5) hr26 ?_
  refine reach_reg (i := 27#5) hr27 ?_
  refine reach_reg (i := 28#5) hr28 ?_
  refine reach_reg (i := 29#5) hr29 ?_
  rw [pick12] at hs
  refine x_ldrq_u (t := 0#5) (b := 29#5) (x := (S - 96#64)) (a := (S - 264#64)) (i := 0) (by decide) hrun (c12_828 hP hCL 12 kf) (pc4 _ 828 832 rfl) rfl (aSS S 96 18446744073709551448 264 (8 * 0) (by decide)) (wf1 hs 0 (by exact (by decide : 0 < 5)) : m.read64 _ = o196 ∧ _) (wf1 hs 1 (by exact (by decide : 1 < 5)) : m.read64 _ = o197 ∧ _) ?_
  refine x_ldrq_u (t := 1#5) (b := 29#5) (x := (S - 96#64)) (a := (S - 264#64)) (i := 2) (by decide) hrun (c12_832 hP hCL 12 kf) (pc4 _ 832 836 rfl) rfl (aSS S 96 18446744073709551464 264 (8 * 2) (by decide)) (wf1 hs 2 (by exact (by decide : 2 < 5)) : m.read64 _ = o198 ∧ _) (wf1 hs 3 (by exact (by decide : 3 < 5)) : m.read64 _ = o199 ∧ _) ?_
  refine x_addi_sp2 (d := 8#5) (by decide) hrun (c12_836 hP hCL 12 kf) (pc4 _ 836 840 rfl) (aSk S 832 384 _ (by decide)) ?_
  refine x_addi_sp2 (d := 9#5) (by decide) hrun (c12_840 hP hCL 12 kf) (pc4 _ 840 844 rfl) (aSk S 832 384 _ (by decide)) ?_
  rw [pick9] at hs
  refine x_ldrq_u (t := 2#5) (b := 29#5) (x := (S - 96#64)) (a := (S - 184#64)) (i := 0) (by decide) hrun (c12_844 hP hCL 12 kf) (pc4 _ 844 848 rfl) rfl (aSS S 96 18446744073709551528 184 (8 * 0) (by decide)) (wf1 hs 0 (by exact (by decide : 0 < 5)) : m.read64 _ = o220 ∧ _) (wf1 hs 1 (by exact (by decide : 1 < 5)) : m.read64 _ = o221 ∧ _) ?_
  rw [pick24] at hs
  refine x_stpq_o (t1 := 0#5) (t2 := 1#5) (b := 20#5) (x := Pb) (lo1 := o196) (hi1 := o197) (lo2 := o198) (hi2 := o199) (i := 0) (by decide) hrun (c12_848 hP hCL 12 kf) (pc4 _ 848 852 rfl) rfl rfl hs (by exact (by decide : 3 < 10)) rfl rfl (fun m241 hs242 kf243 => ?_)
  replace hs242 : m241 ⊨ (Pb ↦₆₄* [o196, o197, o198, o199, p4, p5, p6, p7, p8, p9]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F := hs242
  replace kf243 := kf.trans kf243
  clear hs kf
  rw [pick2] at hs242
  refine x_ldrq_u (t := 0#5) (b := 29#5) (x := (S - 96#64)) (a := (S - 184#64)) (i := 2) (by decide) hrun (c12_852 hP hCL 12 kf243) (pc4 _ 852 856 rfl) rfl (aSS S 96 18446744073709551544 184 (8 * 2) (by decide)) (wf1 hs242 2 (by exact (by decide : 2 < 5)) : m241.read64 _ = o222 ∧ _) (wf1 hs242 3 (by exact (by decide : 3 < 5)) : m241.read64 _ = o223 ∧ _) ?_
  rw [pick2] at hs242
  refine x_strq_u (t := 2#5) (b := 20#5) (x := Pb) (lo := o220) (hi := o221) (i := 5) (by decide) hrun (c12_856 hP hCL 12 kf243) (pc4 _ 856 860 rfl) rfl rfl hs242 (by exact (by decide : 6 < 10)) rfl (fun m244 hs245 kf246 => ?_)
  replace hs245 : m244 ⊨ (Pb ↦₆₄* [o196, o197, o198, o199, p4, o220, o221, p7, p8, p9]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F := hs245
  replace kf246 := kf243.trans kf246
  clear hs242 kf243
  refine x_strq_u (t := 0#5) (b := 20#5) (x := Pb) (lo := o222) (hi := o223) (i := 7) (by decide) hrun (c12_860 hP hCL 12 kf246) (pc4 _ 860 864 rfl) rfl rfl hs245 (by exact (by decide : 8 < 10)) rfl (fun m247 hs248 kf249 => ?_)
  replace hs248 : m247 ⊨ (Pb ↦₆₄* [o196, o197, o198, o199, p4, o220, o221, o222, o223, p9]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F := hs248
  replace kf249 := kf246.trans kf249
  clear hs245 kf246
  rw [pick17] at hs248
  refine x_ldpq_o (t1 := 1#5) (t2 := 0#5) (b := 8#5) (x := (S - 384#64)) (a := (S - 384#64)) (i := 0) (by decide) hrun (c12_864 hP hCL 12 kf249) (pc4 _ 864 868 rfl) rfl (aSS S 384 0 384 (8 * 0) (by decide)) (wf1 hs248 0 (by exact (by decide : 0 < 5)) : m247.read64 _ = o151 ∧ _) (wf1 hs248 1 (by exact (by decide : 1 < 5)) : m247.read64 _ = o152 ∧ _) (wf1 hs248 2 (by exact (by decide : 2 < 5)) : m247.read64 _ = o153 ∧ _) (wf1 hs248 3 (by exact (by decide : 3 < 5)) : m247.read64 _ = o154 ∧ _) ?_
  rw [pick24] at hs248
  refine x_stpq_o (t1 := 1#5) (t2 := 0#5) (b := 19#5) (x := Qb) (lo1 := o151) (hi1 := o152) (lo2 := o153) (hi2 := o154) (i := 0) (by decide) hrun (c12_868 hP hCL 12 kf249) (pc4 _ 868 872 rfl) rfl rfl hs248 (by exact (by decide : 3 < 10)) rfl rfl (fun m250 hs251 kf252 => ?_)
  replace hs251 : m250 ⊨ (Qb ↦₆₄* [o151, o152, o153, o154, q4, q5, q6, q7, q8, q9]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ (Pb ↦₆₄* [o196, o197, o198, o199, p4, o220, o221, o222, o223, p9]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F := hs251
  replace kf252 := kf249.trans kf252
  clear hs248 kf249
  rw [pick8] at hs251
  refine x_ldrq_o (t := 1#5) (b := 8#5) (x := (S - 384#64)) (a := (S - 144#64)) (i := 2) (by decide) hrun (c12_872 hP hCL 12 kf252) (pc4 _ 872 876 rfl) rfl (aSS S 384 256 144 (8 * 2) (by decide)) (wf1 hs251 2 (by exact (by decide : 2 < 5)) : m250.read64 _ = o237 ∧ _) (wf1 hs251 3 (by exact (by decide : 3 < 5)) : m250.read64 _ = o238 ∧ _) ?_
  rw [pick6] at hs251
  refine x_ldr_u (d := 8#5) (b := 29#5) (x := (S - 96#64)) (a := (S - 264#64)) (i := 4) (by decide) (by decide) hrun (c12_876 hP hCL 12 kf252) (pc4 _ 876 880 rfl) rfl (aSS S 96 18446744073709551480 264 (8 * 4) (by decide)) (wf1 hs251 4 (by exact (by decide : 4 < 5)) : m250.read64 _ = o200 ∧ _) ?_
  rw [pick2] at hs251
  refine x_ldrq_o (t := 0#5) (b := 9#5) (x := (S - 384#64)) (a := (S - 144#64)) (i := 0) (by decide) hrun (c12_880 hP hCL 12 kf252) (pc4 _ 880 884 rfl) rfl (aSS S 384 240 144 (8 * 0) (by decide)) (wf1 hs251 0 (by exact (by decide : 0 < 5)) : m250.read64 _ = o235 ∧ _) (wf1 hs251 1 (by exact (by decide : 1 < 5)) : m250.read64 _ = o236 ∧ _) ?_
  rw [pick6] at hs251
  refine x_ldr_u (d := 9#5) (b := 29#5) (x := (S - 96#64)) (a := (S - 184#64)) (i := 4) (by decide) (by decide) hrun (c12_884 hP hCL 12 kf252) (pc4 _ 884 888 rfl) rfl (aSS S 96 18446744073709551560 184 (8 * 4) (by decide)) (wf1 hs251 4 (by exact (by decide : 4 < 5)) : m250.read64 _ = o224 ∧ _) ?_
  rw [pick6] at hs251
  refine x_str_o (t := 8#5) (b := 20#5) (x := Pb) (v1 := o200) (i := 4) (by decide) (by decide) hrun (c12_888 hP hCL 12 kf252) (pc4 _ 888 892 rfl) rfl rfl hs251 (by exact (by decide : 4 < 10)) rfl (fun m253 hs254 kf255 => ?_)
  replace hs254 : m253 ⊨ (Pb ↦₆₄* [o196, o197, o198, o199, o200, o220, o221, o222, o223, p9]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ (Qb ↦₆₄* [o151, o152, o153, o154, q4, q5, q6, q7, q8, q9]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F := hs254
  replace kf255 := kf252.trans kf255
  clear hs251 kf252
  rw [pick6] at hs254
  refine x_ldr_sp (d := 8#5) (a := (S - 384#64)) (i := 4) (by decide) (aligned_sub hal 832 (by decide) (by decide)) hrun (c12_892 hP hCL 12 kf255) (pc4 _ 892 896 rfl) (aSS S 832 480 384 (8 * 4) (by decide)) (wf1 hs254 4 (by exact (by decide : 4 < 5)) : m253.read64 _ = o155 ∧ _) ?_
  rw [pick2] at hs254
  refine x_str_o (t := 9#5) (b := 20#5) (x := Pb) (v1 := o224) (i := 9) (by decide) (by decide) hrun (c12_896 hP hCL 12 kf255) (pc4 _ 896 900 rfl) rfl rfl hs254 (by exact (by decide : 9 < 10)) rfl (fun m256 hs257 kf258 => ?_)
  replace hs257 : m256 ⊨ (Pb ↦₆₄* [o196, o197, o198, o199, o200, o220, o221, o222, o223, o224]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ (Qb ↦₆₄* [o151, o152, o153, o154, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F := hs257
  replace kf258 := kf255.trans kf258
  clear hs254 kf255
  rw [pick4] at hs257
  refine x_ldr_u (d := 9#5) (b := 29#5) (x := (S - 96#64)) (a := (S - 144#64)) (i := 4) (by decide) (by decide) hrun (c12_900 hP hCL 12 kf258) (pc4 _ 900 904 rfl) rfl (aSS S 96 18446744073709551600 144 (8 * 4) (by decide)) (wf1 hs257 4 (by exact (by decide : 4 < 5)) : m256.read64 _ = o239 ∧ _) ?_
  rw [pick6] at hs257
  refine x_strq_u (t := 1#5) (b := 19#5) (x := Qb) (lo := o237) (hi := o238) (i := 7) (by decide) hrun (c12_904 hP hCL 12 kf258) (pc4 _ 904 908 rfl) rfl rfl hs257 (by exact (by decide : 8 < 10)) rfl (fun m259 hs260 kf261 => ?_)
  replace hs260 : m259 ⊨ (Qb ↦₆₄* [o151, o152, o153, o154, q4, q5, q6, o237, o238, q9]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ (Pb ↦₆₄* [o196, o197, o198, o199, o200, o220, o221, o222, o223, o224]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F := hs260
  replace kf261 := kf258.trans kf261
  clear hs257 kf258
  refine x_str_o (t := 8#5) (b := 19#5) (x := Qb) (v1 := o155) (i := 4) (by decide) (by decide) hrun (c12_908 hP hCL 12 kf261) (pc4 _ 908 912 rfl) rfl rfl hs260 (by exact (by decide : 4 < 10)) rfl (fun m262 hs263 kf264 => ?_)
  replace hs263 : m262 ⊨ (Qb ↦₆₄* [o151, o152, o153, o154, o155, q5, q6, o237, o238, q9]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ (Pb ↦₆₄* [o196, o197, o198, o199, o200, o220, o221, o222, o223, o224]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F := hs263
  replace kf264 := kf261.trans kf264
  clear hs260 kf261
  refine x_str_o (t := 9#5) (b := 19#5) (x := Qb) (v1 := o239) (i := 9) (by decide) (by decide) hrun (c12_912 hP hCL 12 kf264) (pc4 _ 912 916 rfl) rfl rfl hs263 (by exact (by decide : 9 < 10)) rfl (fun m265 hs266 kf267 => ?_)
  replace hs266 : m265 ⊨ (Qb ↦₆₄* [o151, o152, o153, o154, o155, q5, q6, o237, o238, o239]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ (Pb ↦₆₄* [o196, o197, o198, o199, o200, o220, o221, o222, o223, o224]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F := hs266
  replace kf267 := kf264.trans kf267
  clear hs263 kf264
  refine x_strq_u (t := 0#5) (b := 19#5) (x := Qb) (lo := o235) (hi := o236) (i := 5) (by decide) hrun (c12_916 hP hCL 12 kf267) (pc4 _ 916 920 rfl) rfl rfl hs266 (by exact (by decide : 6 < 10)) rfl (fun m268 hs269 kf270 => ?_)
  replace hs269 : m268 ⊨ (Qb ↦₆₄* [o151, o152, o153, o154, o155, o235, o236, o237, o238, o239]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ (Pb ↦₆₄* [o196, o197, o198, o199, o200, o220, o221, o222, o223, o224]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F := hs269
  replace kf270 := kf267.trans kf270
  clear hs266 kf267
  refine x_addsp hrun (c12_920 hP hCL 12 kf270) (pc4 _ 920 924 rfl) (aSk S 832 96 _ (by decide)) ?_
  rw [pick25] at hs269
  refine x_ldp_sp (d1 := 20#5) (d2 := 19#5) (a := (S - 96#64)) (i := 10) (by decide) (by decide) (aligned_sub hal 96 (by decide) (by decide)) hrun (c12_924 hP hCL 12 kf270) (pc4 _ 924 928 rfl) (aSS S 96 80 96 (8 * 10) (by decide)) (wf1 hs269 10 (by exact (by decide : 10 < 12)) : m268.read64 _ = c20 ∧ _) rfl (wf1 hs269 11 (by exact (by decide : 11 < 12)) : m268.read64 _ = c19 ∧ _) ?_
  refine x_ldp_sp (d1 := 22#5) (d2 := 21#5) (a := (S - 96#64)) (i := 8) (by decide) (by decide) (aligned_sub hal 96 (by decide) (by decide)) hrun (c12_928 hP hCL 12 kf270) (pc4 _ 928 932 rfl) (aSS S 96 64 96 (8 * 8) (by decide)) (wf1 hs269 8 (by exact (by decide : 8 < 12)) : m268.read64 _ = c22 ∧ _) rfl (wf1 hs269 9 (by exact (by decide : 9 < 12)) : m268.read64 _ = c21 ∧ _) ?_
  refine x_ldp_sp (d1 := 24#5) (d2 := 23#5) (a := (S - 96#64)) (i := 6) (by decide) (by decide) (aligned_sub hal 96 (by decide) (by decide)) hrun (c12_932 hP hCL 12 kf270) (pc4 _ 932 936 rfl) (aSS S 96 48 96 (8 * 6) (by decide)) (wf1 hs269 6 (by exact (by decide : 6 < 12)) : m268.read64 _ = c24 ∧ _) rfl (wf1 hs269 7 (by exact (by decide : 7 < 12)) : m268.read64 _ = c23 ∧ _) ?_
  refine x_ldp_sp (d1 := 26#5) (d2 := 25#5) (a := (S - 96#64)) (i := 4) (by decide) (by decide) (aligned_sub hal 96 (by decide) (by decide)) hrun (c12_936 hP hCL 12 kf270) (pc4 _ 936 940 rfl) (aSS S 96 32 96 (8 * 4) (by decide)) (wf1 hs269 4 (by exact (by decide : 4 < 12)) : m268.read64 _ = c26 ∧ _) rfl (wf1 hs269 5 (by exact (by decide : 5 < 12)) : m268.read64 _ = c25 ∧ _) ?_
  refine x_ldp_sp (d1 := 28#5) (d2 := 27#5) (a := (S - 96#64)) (i := 2) (by decide) (by decide) (aligned_sub hal 96 (by decide) (by decide)) hrun (c12_940 hP hCL 12 kf270) (pc4 _ 940 944 rfl) (aSS S 96 16 96 (8 * 2) (by decide)) (wf1 hs269 2 (by exact (by decide : 2 < 12)) : m268.read64 _ = c28 ∧ _) rfl (wf1 hs269 3 (by exact (by decide : 3 < 12)) : m268.read64 _ = c27 ∧ _) ?_
  refine x_ldp_post (d1 := 29#5) (d2 := 30#5) (i := 0) (by decide) (by decide) (aligned_sub hal 96 (by decide) (by decide)) hrun (c12_944 hP hCL 12 kf270) (pc4 _ 944 948 rfl) (aS0 S 96) (aSb S 96 96 0 (by decide)) (wf1 hs269 0 (by exact (by decide : 0 < 12)) : m268.read64 _ = c29 ∧ _) (wf1 hs269 1 (by exact (by decide : 1 < 12)) : m268.read64 _ = c30 ∧ _) ?_
  refine x_ret hrun (c12_948 hP hCL 12 kf270) rfl ?_
  exact hcont _ _ _ _ _ hrun kf270 (cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide) hvs)))))))) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl bd_W3 bd_U3 bd_W2 bd_U2 bd_Tmp bd_E bd_A24EpBB bd_A24E bd_AA bd_BB bd_Diff bd_Sum bd_CB bd_DA bd_B bd_C bd_A bd_D hs269


end X25519Dalek.LP

end
end

section
section
/-! # `differential_add_and_double`: entry and exit conversions, and the field identity -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

theorem sat_mr_words {m : Memory} {a b : BitVec 64} {ws : List (BitVec 64)} {F : SepProp} (n k : Nat)
    (hn : n < 2 ^ 64) (hb : b = a + BitVec.ofNat 64 n) (hl : ws.length = k)
    (hs : m ⊨ memRegion a n ∗ (b ↦₆₄* ws) ∗ F) : m ⊨ memRegion a (n + 8 * k) ∗ F := by
  rw [words_eq_bytes] at hs
  have h := sat_mr_bytes n hn hb hs
  rwa [flatMap_unpack64_length, hl] at h

theorem s1056 (S : BitVec 64) : S - BitVec.ofNat 64 1056 = S - 832#64 - 224#64 := by
  rw [show (1056 : Nat) = 832 + 224 from rfl, BitVec.ofNat_add]; abel

end X25519Dalek.LP

end
end

section
section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj X25519Dalek.LP

set_option maxHeartbeats 8000000 in
theorem differentialAddAndDouble_828_ret_dev {mpl : Arm64.Obj.MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S Pb Qb u1 : BitVec 64} {F : Arm64.SepProp}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 uw0 uw1 uw2 uw3 uw4 : BitVec 64}
    {c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 : BitVec 64}
    {o166 o167 o168 o169 o170 o235 o236 o237 o238 o239 t452 t476 t488 t492 t484 t768 t772 t784 t788 t792 o220 o221 o222 o223 o224 o181 o182 o183 o184 o185 o64 o65 o66 o67 o68 o79 o80 o81 o82 o83 o196 o197 o198 o199 o200 t632 t644 t660 t676 t680 t560 t564 t584 t588 t616 o151 o152 o153 o154 o155 o118 o119 o120 o121 o122 o103 o104 o105 o106 o107 t144 t164 t172 t180 t188 t232 t228 t248 t256 t276 t76 t96 t100 t120 t68 t316 t328 t324 t336 t348 g1 : BitVec 64}
    (hal : (S &&& 15#64 == 0#64) = true)
    (hPU : p0.toNat < 9007199254740992 ∧ p1.toNat < 9007199254740992 ∧ p2.toNat < 9007199254740992 ∧ p3.toNat < 9007199254740992 ∧ p4.toNat < 9007199254740992)
    (hPW : p5.toNat < 9007199254740992 ∧ p6.toNat < 9007199254740992 ∧ p7.toNat < 9007199254740992 ∧ p8.toNat < 9007199254740992 ∧ p9.toNat < 9007199254740992)
    (hQU : q0.toNat < 9007199254740992 ∧ q1.toNat < 9007199254740992 ∧ q2.toNat < 9007199254740992 ∧ q3.toNat < 9007199254740992 ∧ q4.toNat < 9007199254740992)
    (hQW : q5.toNat < 9007199254740992 ∧ q6.toNat < 9007199254740992 ∧ q7.toNat < 9007199254740992 ∧ q8.toNat < 9007199254740992 ∧ q9.toNat < 9007199254740992)
    (hU1 : uw0.toNat < 18014398509481984 ∧ uw1.toNat < 18014398509481984 ∧ uw2.toNat < 18014398509481984 ∧ uw3.toNat < 18014398509481984 ∧ uw4.toNat < 18014398509481984)
    (hrun : s.status = Arm64.ExecStatus.Running) (hpc : s.pc = mpl.base 12 + BitVec.ofNat 64 828) (hsp : s.sp = S - 832#64)
    (hr19 : s.regs.regs 19#5 = Qb)
    (hr20 : s.regs.regs 20#5 = Pb)
    (hr21 : s.regs.regs 21#5 = o80)
    (hr22 : s.regs.regs 22#5 = 0x007ffffffffffff0#64)
    (hr23 : s.regs.regs 23#5 = o79)
    (hr24 : s.regs.regs 24#5 = 36028797018963664#64)
    (hr25 : s.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64))
    (hr26 : s.regs.regs 26#5 = o83)
    (hr27 : s.regs.regs 27#5 = o82)
    (hr28 : s.regs.regs 28#5 = o81)
    (hr29 : s.regs.regs 29#5 = (S - 96#64))
    (bd_Tmp : (o166.toNat < 4503599627370496 ∧ o167.toNat < 4503599627370496 ∧ o168.toNat < 4503599627370496 ∧ o169.toNat < 4503599627370496 ∧ o170.toNat < 4503599627370496))
    (bd_W3 : (o235.toNat < 4503599627370496 ∧ o236.toNat < 4503599627370496 ∧ o237.toNat < 4503599627370496 ∧ o238.toNat < 4503599627370496 ∧ o239.toNat < 4503599627370496))
    (bd_E : (t452.toNat < 4503599627370496 ∧ t476.toNat < 4503599627370496 ∧ t488.toNat < 4503599627370496 ∧ t492.toNat < 4503599627370496 ∧ t484.toNat < 4503599627370496))
    (bd_A24EpBB : (t768.toNat < 9007199254740992 ∧ t772.toNat < 9007199254740992 ∧ t784.toNat < 9007199254740992 ∧ t788.toNat < 9007199254740992 ∧ t792.toNat < 9007199254740992))
    (bd_W2 : (o220.toNat < 4503599627370496 ∧ o221.toNat < 4503599627370496 ∧ o222.toNat < 4503599627370496 ∧ o223.toNat < 4503599627370496 ∧ o224.toNat < 4503599627370496))
    (bd_A24E : (o181.toNat < 4503599627370496 ∧ o182.toNat < 4503599627370496 ∧ o183.toNat < 4503599627370496 ∧ o184.toNat < 4503599627370496 ∧ o185.toNat < 4503599627370496))
    (bd_AA : (o64.toNat < 4503599627370496 ∧ o65.toNat < 4503599627370496 ∧ o66.toNat < 4503599627370496 ∧ o67.toNat < 4503599627370496 ∧ o68.toNat < 4503599627370496))
    (bd_BB : (o79.toNat < 4503599627370496 ∧ o80.toNat < 4503599627370496 ∧ o81.toNat < 4503599627370496 ∧ o82.toNat < 4503599627370496 ∧ o83.toNat < 4503599627370496))
    (bd_U2 : (o196.toNat < 4503599627370496 ∧ o197.toNat < 4503599627370496 ∧ o198.toNat < 4503599627370496 ∧ o199.toNat < 4503599627370496 ∧ o200.toNat < 4503599627370496))
    (bd_Diff : (t632.toNat < 4503599627370496 ∧ t644.toNat < 4503599627370496 ∧ t660.toNat < 4503599627370496 ∧ t676.toNat < 4503599627370496 ∧ t680.toNat < 4503599627370496))
    (bd_Sum : (t560.toNat < 9007199254740992 ∧ t564.toNat < 9007199254740992 ∧ t584.toNat < 9007199254740992 ∧ t588.toNat < 9007199254740992 ∧ t616.toNat < 9007199254740992))
    (bd_U3 : (o151.toNat < 4503599627370496 ∧ o152.toNat < 4503599627370496 ∧ o153.toNat < 4503599627370496 ∧ o154.toNat < 4503599627370496 ∧ o155.toNat < 4503599627370496))
    (bd_CB : (o118.toNat < 4503599627370496 ∧ o119.toNat < 4503599627370496 ∧ o120.toNat < 4503599627370496 ∧ o121.toNat < 4503599627370496 ∧ o122.toNat < 4503599627370496))
    (bd_DA : (o103.toNat < 4503599627370496 ∧ o104.toNat < 4503599627370496 ∧ o105.toNat < 4503599627370496 ∧ o106.toNat < 4503599627370496 ∧ o107.toNat < 4503599627370496))
    (bd_B : (t144.toNat < 4503599627370496 ∧ t164.toNat < 4503599627370496 ∧ t172.toNat < 4503599627370496 ∧ t180.toNat < 4503599627370496 ∧ t188.toNat < 4503599627370496))
    (bd_C : (t232.toNat < 18014398509481984 ∧ t228.toNat < 18014398509481984 ∧ t248.toNat < 18014398509481984 ∧ t256.toNat < 18014398509481984 ∧ t276.toNat < 18014398509481984))
    (bd_A : (t76.toNat < 18014398509481984 ∧ t96.toNat < 18014398509481984 ∧ t100.toNat < 18014398509481984 ∧ t120.toNat < 18014398509481984 ∧ t68.toNat < 18014398509481984))
    (bd_D : (t316.toNat < 4503599627370496 ∧ t328.toNat < 4503599627370496 ∧ t324.toNat < 4503599627370496 ∧ t336.toNat < 4503599627370496 ∧ t348.toNat < 4503599627370496))
    (hs : s.mem ⊨ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F) :
    ∃ sf, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 12) s sf ∧
      sf.status = Arm64.ExecStatus.Running ∧
      sf.pc = c30 ∧
      sf.sp = S ∧
      Arm64.VRegFile.calleeSaved sf.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      sf.regs.regs 19#5 = c19 ∧
        sf.regs.regs 20#5 = c20 ∧
        sf.regs.regs 21#5 = c21 ∧
        sf.regs.regs 22#5 = c22 ∧
        sf.regs.regs 23#5 = c23 ∧
        sf.regs.regs 24#5 = c24 ∧
        sf.regs.regs 25#5 = c25 ∧
        sf.regs.regs 26#5 = c26 ∧
        sf.regs.regs 27#5 = c27 ∧
        sf.regs.regs 28#5 = c28 ∧
        sf.regs.regs 29#5 = c29 ∧
        sf.mem ⊨ Arm64.memRegion (S - 1056#64) 1056 ∗ (Qb ↦₆₄* [o151, o152, o153, o154, o155, o235, o236, o237, o238, o239]) ∗ (Pb ↦₆₄* [o196, o197, o198, o199, o200, o220, o221, o222, o223, o224]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F := by
  have e0 : mkS s (mpl.base 12 + BitVec.ofNat 64 828) s.regs.regs (S - 832#64) s.pstate s.mem s.vregs.regs = s := by
    rw [← hpc, ← hsp]; rfl
  rw [← e0]
  show Reach (bprog mpl 12) _ _
  refine d12_s10 (S := S) (vo := s.vregs.regs) (c19 := c19) (c20 := c20) (c21 := c21) (c22 := c22) (c23 := c23) (c24 := c24) (c25 := c25) (c26 := c26) (c27 := c27) (c28 := c28) (c29 := c29) (c30 := c30) hP hCL hal (by simpa only [lbw, valw, Nat.reducePow] using hPU) (by simpa only [lbw, valw, Nat.reducePow] using hPW) (by simpa only [lbw, valw, Nat.reducePow] using hQU) (by simpa only [lbw, valw, Nat.reducePow] using hQW) (by simpa only [lbw, valw, Nat.reducePow] using hU1) hrun (Memory.KeepsFrozen.refl _) rfl hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26 hr27 hr28 hr29 (by simpa only [lbw, valw, Nat.reducePow] using bd_Tmp) (by simpa only [lbw, valw, Nat.reducePow] using bd_W3) (by simpa only [lbw, valw, Nat.reducePow] using bd_E) (by simpa only [lbw, valw, Nat.reducePow] using bd_A24EpBB) (by simpa only [lbw, valw, Nat.reducePow] using bd_W2) (by simpa only [lbw, valw, Nat.reducePow] using bd_A24E) (by simpa only [lbw, valw, Nat.reducePow] using bd_AA) (by simpa only [lbw, valw, Nat.reducePow] using bd_BB) (by simpa only [lbw, valw, Nat.reducePow] using bd_U2) (by simpa only [lbw, valw, Nat.reducePow] using bd_Diff) (by simpa only [lbw, valw, Nat.reducePow] using bd_Sum) (by simpa only [lbw, valw, Nat.reducePow] using bd_U3) (by simpa only [lbw, valw, Nat.reducePow] using bd_CB) (by simpa only [lbw, valw, Nat.reducePow] using bd_DA) (by simpa only [lbw, valw, Nat.reducePow] using bd_B) (by simpa only [lbw, valw, Nat.reducePow] using bd_C) (by simpa only [lbw, valw, Nat.reducePow] using bd_A) (by simpa only [lbw, valw, Nat.reducePow] using bd_D) hs ?_
  intro sb r ps m v  hrun kf hvs hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26 hr27 hr28 hr29 hr30 bd_W3 bd_U3 bd_W2 bd_U2 bd_Tmp bd_E bd_A24EpBB bd_A24E bd_AA bd_BB bd_Diff bd_Sum bd_CB bd_DA bd_B bd_C bd_A bd_D hs
  apply Reach.done
  have hm := hs
  clear hs
  rw [pick10] at hm
  rw [← s1056] at hm
  rw [pick11] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 224 1 (by norm_num) (aSb _ 1056 224 832 (by decide)).symm rfl hm
  rw [pick23] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 232 5 (by norm_num) (aSb _ 1056 232 824 (by decide)).symm rfl hm
  rw [pick21] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 272 5 (by norm_num) (aSb _ 1056 272 784 (by decide)).symm rfl hm
  rw [pick21] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 312 5 (by norm_num) (aSb _ 1056 312 744 (by decide)).symm rfl hm
  rw [pick21] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 352 5 (by norm_num) (aSb _ 1056 352 704 (by decide)).symm rfl hm
  rw [pick14] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 392 5 (by norm_num) (aSb _ 1056 392 664 (by decide)).symm rfl hm
  rw [pick14] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 432 5 (by norm_num) (aSb _ 1056 432 624 (by decide)).symm rfl hm
  rw [pick11] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 472 5 (by norm_num) (aSb _ 1056 472 584 (by decide)).symm rfl hm
  rw [pick17] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 512 5 (by norm_num) (aSb _ 1056 512 544 (by decide)).symm rfl hm
  rw [pick16] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 552 5 (by norm_num) (aSb _ 1056 552 504 (by decide)).symm rfl hm
  rw [pick15] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 592 5 (by norm_num) (aSb _ 1056 592 464 (by decide)).symm rfl hm
  rw [pick14] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 632 5 (by norm_num) (aSb _ 1056 632 424 (by decide)).symm rfl hm
  rw [pick6] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 672 5 (by norm_num) (aSb _ 1056 672 384 (by decide)).symm rfl hm
  rw [pick9] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 712 5 (by norm_num) (aSb _ 1056 712 344 (by decide)).symm rfl hm
  rw [pick10] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 752 5 (by norm_num) (aSb _ 1056 752 304 (by decide)).symm rfl hm
  rw [pick7] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 792 5 (by norm_num) (aSb _ 1056 792 264 (by decide)).symm rfl hm
  rw [pick8] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 832 5 (by norm_num) (aSb _ 1056 832 224 (by decide)).symm rfl hm
  rw [pick6] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 872 5 (by norm_num) (aSb _ 1056 872 184 (by decide)).symm rfl hm
  rw [pick4] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 912 5 (by norm_num) (aSb _ 1056 912 144 (by decide)).symm rfl hm
  rw [pick7] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 952 1 (by norm_num) (aSb _ 1056 952 104 (by decide)).symm rfl hm
  rw [pick2] at hm
  rw [sepConj_left_comm] at hm
  replace hm := sat_mr_words (a := S - BitVec.ofNat 64 1056) 960 12 (by norm_num) (aSb _ 1056 960 96 (by decide)).symm rfl hm
  exact ⟨hrun, hr30, BitVec.sub_zero S, hvs, hr19, hr20, hr21, hr22, hr23, hr24, hr25, hr26, hr27, hr28, hr29, hm⟩

end X25519Dalek

end
end

section
open X25519Dalek

set_option maxHeartbeats 4000000


theorem solution {mpl : Arm64.Obj.MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S Pb Qb u1 : BitVec 64} {F : Arm64.SepProp}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 uw0 uw1 uw2 uw3 uw4 : BitVec 64}
    {c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 : BitVec 64}
    {o166 o167 o168 o169 o170 o235 o236 o237 o238 o239 t452 t476 t488 t492 t484 t768 t772 t784 t788 t792 o220 o221 o222 o223 o224 o181 o182 o183 o184 o185 o64 o65 o66 o67 o68 o79 o80 o81 o82 o83 o196 o197 o198 o199 o200 t632 t644 t660 t676 t680 t560 t564 t584 t588 t616 o151 o152 o153 o154 o155 o118 o119 o120 o121 o122 o103 o104 o105 o106 o107 t144 t164 t172 t180 t188 t232 t228 t248 t256 t276 t76 t96 t100 t120 t68 t316 t328 t324 t336 t348 g1 : BitVec 64}
    (hal : (S &&& 15#64 == 0#64) = true)
    (hPU : p0.toNat < 9007199254740992 ∧ p1.toNat < 9007199254740992 ∧ p2.toNat < 9007199254740992 ∧ p3.toNat < 9007199254740992 ∧ p4.toNat < 9007199254740992)
    (hPW : p5.toNat < 9007199254740992 ∧ p6.toNat < 9007199254740992 ∧ p7.toNat < 9007199254740992 ∧ p8.toNat < 9007199254740992 ∧ p9.toNat < 9007199254740992)
    (hQU : q0.toNat < 9007199254740992 ∧ q1.toNat < 9007199254740992 ∧ q2.toNat < 9007199254740992 ∧ q3.toNat < 9007199254740992 ∧ q4.toNat < 9007199254740992)
    (hQW : q5.toNat < 9007199254740992 ∧ q6.toNat < 9007199254740992 ∧ q7.toNat < 9007199254740992 ∧ q8.toNat < 9007199254740992 ∧ q9.toNat < 9007199254740992)
    (hU1 : uw0.toNat < 18014398509481984 ∧ uw1.toNat < 18014398509481984 ∧ uw2.toNat < 18014398509481984 ∧ uw3.toNat < 18014398509481984 ∧ uw4.toNat < 18014398509481984)
    (hrun : s.status = Arm64.ExecStatus.Running) (hpc : s.pc = mpl.base 12 + BitVec.ofNat 64 828) (hsp : s.sp = S - 832#64)
    (hr19 : s.regs.regs 19#5 = Qb)
    (hr20 : s.regs.regs 20#5 = Pb)
    (hr21 : s.regs.regs 21#5 = o80)
    (hr22 : s.regs.regs 22#5 = 0x007ffffffffffff0#64)
    (hr23 : s.regs.regs 23#5 = o79)
    (hr24 : s.regs.regs 24#5 = 36028797018963664#64)
    (hr25 : s.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64))
    (hr26 : s.regs.regs 26#5 = o83)
    (hr27 : s.regs.regs 27#5 = o82)
    (hr28 : s.regs.regs 28#5 = o81)
    (hr29 : s.regs.regs 29#5 = (S - 96#64))
    (bd_Tmp : (o166.toNat < 4503599627370496 ∧ o167.toNat < 4503599627370496 ∧ o168.toNat < 4503599627370496 ∧ o169.toNat < 4503599627370496 ∧ o170.toNat < 4503599627370496))
    (bd_W3 : (o235.toNat < 4503599627370496 ∧ o236.toNat < 4503599627370496 ∧ o237.toNat < 4503599627370496 ∧ o238.toNat < 4503599627370496 ∧ o239.toNat < 4503599627370496))
    (bd_E : (t452.toNat < 4503599627370496 ∧ t476.toNat < 4503599627370496 ∧ t488.toNat < 4503599627370496 ∧ t492.toNat < 4503599627370496 ∧ t484.toNat < 4503599627370496))
    (bd_A24EpBB : (t768.toNat < 9007199254740992 ∧ t772.toNat < 9007199254740992 ∧ t784.toNat < 9007199254740992 ∧ t788.toNat < 9007199254740992 ∧ t792.toNat < 9007199254740992))
    (bd_W2 : (o220.toNat < 4503599627370496 ∧ o221.toNat < 4503599627370496 ∧ o222.toNat < 4503599627370496 ∧ o223.toNat < 4503599627370496 ∧ o224.toNat < 4503599627370496))
    (bd_A24E : (o181.toNat < 4503599627370496 ∧ o182.toNat < 4503599627370496 ∧ o183.toNat < 4503599627370496 ∧ o184.toNat < 4503599627370496 ∧ o185.toNat < 4503599627370496))
    (bd_AA : (o64.toNat < 4503599627370496 ∧ o65.toNat < 4503599627370496 ∧ o66.toNat < 4503599627370496 ∧ o67.toNat < 4503599627370496 ∧ o68.toNat < 4503599627370496))
    (bd_BB : (o79.toNat < 4503599627370496 ∧ o80.toNat < 4503599627370496 ∧ o81.toNat < 4503599627370496 ∧ o82.toNat < 4503599627370496 ∧ o83.toNat < 4503599627370496))
    (bd_U2 : (o196.toNat < 4503599627370496 ∧ o197.toNat < 4503599627370496 ∧ o198.toNat < 4503599627370496 ∧ o199.toNat < 4503599627370496 ∧ o200.toNat < 4503599627370496))
    (bd_Diff : (t632.toNat < 4503599627370496 ∧ t644.toNat < 4503599627370496 ∧ t660.toNat < 4503599627370496 ∧ t676.toNat < 4503599627370496 ∧ t680.toNat < 4503599627370496))
    (bd_Sum : (t560.toNat < 9007199254740992 ∧ t564.toNat < 9007199254740992 ∧ t584.toNat < 9007199254740992 ∧ t588.toNat < 9007199254740992 ∧ t616.toNat < 9007199254740992))
    (bd_U3 : (o151.toNat < 4503599627370496 ∧ o152.toNat < 4503599627370496 ∧ o153.toNat < 4503599627370496 ∧ o154.toNat < 4503599627370496 ∧ o155.toNat < 4503599627370496))
    (bd_CB : (o118.toNat < 4503599627370496 ∧ o119.toNat < 4503599627370496 ∧ o120.toNat < 4503599627370496 ∧ o121.toNat < 4503599627370496 ∧ o122.toNat < 4503599627370496))
    (bd_DA : (o103.toNat < 4503599627370496 ∧ o104.toNat < 4503599627370496 ∧ o105.toNat < 4503599627370496 ∧ o106.toNat < 4503599627370496 ∧ o107.toNat < 4503599627370496))
    (bd_B : (t144.toNat < 4503599627370496 ∧ t164.toNat < 4503599627370496 ∧ t172.toNat < 4503599627370496 ∧ t180.toNat < 4503599627370496 ∧ t188.toNat < 4503599627370496))
    (bd_C : (t232.toNat < 18014398509481984 ∧ t228.toNat < 18014398509481984 ∧ t248.toNat < 18014398509481984 ∧ t256.toNat < 18014398509481984 ∧ t276.toNat < 18014398509481984))
    (bd_A : (t76.toNat < 18014398509481984 ∧ t96.toNat < 18014398509481984 ∧ t100.toNat < 18014398509481984 ∧ t120.toNat < 18014398509481984 ∧ t68.toNat < 18014398509481984))
    (bd_D : (t316.toNat < 4503599627370496 ∧ t328.toNat < 4503599627370496 ∧ t324.toNat < 4503599627370496 ∧ t336.toNat < 4503599627370496 ∧ t348.toNat < 4503599627370496))
    (hs : s.mem ⊨ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F) :
    ∃ sf, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 12) s sf ∧
      sf.status = Arm64.ExecStatus.Running ∧
      sf.pc = c30 ∧
      sf.sp = S ∧
      Arm64.VRegFile.calleeSaved sf.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      sf.regs.regs 19#5 = c19 ∧
        sf.regs.regs 20#5 = c20 ∧
        sf.regs.regs 21#5 = c21 ∧
        sf.regs.regs 22#5 = c22 ∧
        sf.regs.regs 23#5 = c23 ∧
        sf.regs.regs 24#5 = c24 ∧
        sf.regs.regs 25#5 = c25 ∧
        sf.regs.regs 26#5 = c26 ∧
        sf.regs.regs 27#5 = c27 ∧
        sf.regs.regs 28#5 = c28 ∧
        sf.regs.regs 29#5 = c29 ∧
        sf.mem ⊨ Arm64.memRegion (S - 1056#64) 1056 ∗ (Qb ↦₆₄* [o151, o152, o153, o154, o155, o235, o236, o237, o238, o239]) ∗ (Pb ↦₆₄* [o196, o197, o198, o199, o200, o220, o221, o222, o223, o224]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F := by
  exact X25519Dalek.differentialAddAndDouble_828_ret_dev hP hCL hal hPU hPW hQU hQW hU1 hrun hpc hsp hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26 hr27 hr28 hr29 bd_Tmp bd_W3 bd_E bd_A24EpBB bd_W2 bd_A24E bd_AA bd_BB bd_U2 bd_Diff bd_Sum bd_U3 bd_CB bd_DA bd_B bd_C bd_A bd_D hs

end
