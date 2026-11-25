-- Prove2me | solution 1 for Poly1305Debian.internalOk_poly1305_finish_of_blocks_whole
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-25T20:59:30.388801+00:00
-- url     : https://prove2.me/submissions/a016b757-ce7e-46e7-b79f-24792c18aeef

import Definitions.Def_Poly1305Debian_PlacedObj
import Definitions.Def_Poly1305Debian_Spec
import Mathlib.Tactic.IntervalCases
import Definitions.Def_Link_LinkOk
import Theorems.Thm_Arm64Facts_steps_codeLoaded_v2
import Mathlib.Tactic.ClearExcept
import Mathlib.Tactic.Ring

section
section
/-! # Separation-logic heap algebra

Ported from google-deepmind/code-verification @ 8c8d371f (Apache-2.0),
`arm64-semantics/ProofLib/CoreLemmas.lean` and `ProofLib/SepLogic/Model.lean`: the plain lemmas
about `Heap.Disjoint`, `Heap.union`, `Heap.Matches` and `sepConj`, with ProofLib's custom simp
attributes removed. -/

set_option autoImplicit false

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

instance instAssociativeSepConj : Std.Associative SepProp.sepConj where
  assoc := sepConj_assoc

instance instCommutativeSepConj : Std.Commutative SepProp.sepConj where
  comm := sepConj_comm

theorem Entails.of_eq {P Q : SepProp} (heq : P = Q := by ac_rfl) : P ⊢ Q :=
  heq ▸ Entails.refl P

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
/-! # Abstract machine states

Every state inside a block proof is `mkS s0 pc r sp ps m v`: the state `s0` with the program
counter, the general registers, the stack pointer, the flags, the memory and the vector registers
replaced. The instruction evaluators map such states to such states, and these lemmas let `simp`
compute the result without unfolding `State`. -/

set_option autoImplicit false

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

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

theorem mkS_self (s : State) : mkS s s.pc s.regs.regs s.sp s.pstate s.mem s.vregs.regs = s := rfl

/-- Register reads of the entry state, as `mkS` sees them. -/
theorem readGpr_eq (s : State) (i : BitVec 5) (h : i ≠ 31#5) :
    s.readReg64 (.gpr i) = s.regs.regs i := by
  simp [State.readReg64, RegFile.read, h]

end Poly1305Debian.FD

end
end

section
section
/-! # Execution by backward chaining, and instruction fetch in the placed libsodium library

`P pl ex` is the placed program with hook table `ex`. No hook has its entry point inside the text
block (`hook_none_in`), so inside the block `Step` is fetch-and-execute. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj

abbrev P (pl : Placement) (ex : String → Option (State → State)) : Program :=
  libsodiumDebianOnetimeauthLib.program pl ex

/-! ## Reaching a final state -/

theorem Steps.trans' {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Steps p b c) :
    Steps p a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

/-! ## Code loaded, fetch -/

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

theorem take4_drop_patched {blk : CodeBlock} {pl : Placement} {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ blk.code.length) :
    ((blk.patched pl).drop off).take 4 = bytesOfWordLE (blk.patchedWord pl off) := by
  have hj : off / 4 < (List.range (blk.code.length / 4)).length := by
    simp only [List.length_range]; omega
  have h := drop_take_flatMap_bytesOfWordLE (fun j => blk.patchedWord pl (4 * j))
    (List.range (blk.code.length / 4)) (off / 4) hj
  rw [List.getElem_range, show 4 * (off / 4) = off by omega] at h
  exact h

theorem codeLoaded_cell {p : Program} {m : Memory} (h : p.CodeLoaded m) (i : Nat)
    (hi : i < p.code.length) :
    m.read8 (p.base + BitVec.ofNat 64 i) = p.code[i] ∧
    m.perm (p.base + BitVec.ofNat 64 i) = some Perm.rx := by
  unfold Program.CodeLoaded at h
  exact ⟨(h.2.2 i hi).1, (h.2.2 i hi).2.1⟩

set_option maxRecDepth 100000 in
theorem code_length : libsodiumDebianOnetimeauthPlacedCode.length = 1800 := by rfl

theorem patched_length (pl : Placement) : (libsodiumDebianOnetimeauthText.patched pl).length = 1800 := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE]
  show (List.map (fun _ => 4) (List.range (libsodiumDebianOnetimeauthPlacedCode.length / 4))).sum = 1800
  rw [code_length]; rfl

theorem stub_far {pl : Placement} (hP : libsodiumDebianOnetimeauthLib.Placeable pl) (e : String)
    (he : e ∈ libsodiumDebianOnetimeauthLib.text.externs) : 1800 ≤ (pl.ρ e - pl.base).toNat := by
  have := (hP.text.externs_ok e he).2
  rwa [show libsodiumDebianOnetimeauthLib.text.code.length = 1800 from code_length] at this

/-- No hook has its entry point inside the text block. -/
theorem hook_none_in {pl : Placement} (hP : libsodiumDebianOnetimeauthLib.Placeable pl)
    (ex : String → Option (State → State)) {off : Nat} (hoff : off < 1800) :
    (P pl ex).externAt? (pl.base + BitVec.ofNat 64 off) = none := by
  have e : (pl.base + BitVec.ofNat 64 off - pl.base).toNat = off := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  simp only [Program.externAt?, Program.hookAtOff?, P, PlacedLib.program, e]
  have h1 : (libsodiumDebianOnetimeauthLib.text.externs.map fun e => (e, (pl.ρ e - pl.base).toNat)).findSome?
      (fun (n, o) => if o == off then ex n else none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro x hx
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
    have := stub_far hP e' he'
    have hne : ((pl.ρ e' - pl.base).toNat == off) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp only [hne, Bool.false_eq_true, ite_false]
  have h2 : libsodiumDebianOnetimeauthLib.text.symbols.findSome?
      (fun (n, o) => if o == off then (fun _ => (none : Option (State → State))) n else none) = none := by
    rw [List.findSome?_eq_none_iff]; intro x _; simp
  rw [h1]; simpa using h2

/-- The stub lookup returns the hook of `e` when hooks agree at equal addresses. -/
theorem findSome_stub {pl : Placement} {ex : String → Option (State → State)} {fns : List String}
    (hag : Link.HooksAgree fns pl.ρ ex) (e : String) (he : e ∈ fns) :
    ∀ L : List String, (∀ x ∈ L, x ∈ fns) →
      (L.map fun e' => (e', (pl.ρ e' - pl.base).toNat)).findSome?
        (fun (n, o) => if o == (pl.ρ e - pl.base).toNat then ex n else none) =
      if L.any (fun e' => (pl.ρ e' - pl.base).toNat == (pl.ρ e - pl.base).toNat) then ex e else none
  | [], _ => by simp
  | a :: L, hL => by
    have ih := findSome_stub hag e he L (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.findSome?_cons, List.any_cons]
    by_cases hc : (pl.ρ a - pl.base).toNat = (pl.ρ e - pl.base).toNat
    · have hρ : pl.ρ a = pl.ρ e := by
        have := BitVec.eq_of_toNat_eq hc
        simpa using this
      have hx : ex a = ex e := hag a (hL a (by simp)) e he hρ
      simp only [hc, beq_self_eq_true, if_true, Bool.true_or, hx]
      cases h : ex e with
      | none => simp only [ih]; split <;> simp [h]
      | some f => rfl
    · have hc' : ((pl.ρ a - pl.base).toNat == (pl.ρ e - pl.base).toNat) = false := by
        simpa using hc
      simp only [hc', Bool.false_eq_true, if_false, Bool.false_or, ih]

/-- Under `LinkOk`, the hook found at an external function's address is its own. -/
theorem hookAt_of_linkOk {pl : Placement} {ex : String → Option (State → State)}
    (hL : Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthLib pl ex) (e : String)
    (he : e ∈ Link.PlacedLib.externFns libsodiumDebianOnetimeauthLib) :
    (P pl ex).externAt? (pl.ρ e) = ex e := by
  have hfns : Link.PlacedLib.externFns libsodiumDebianOnetimeauthLib =
      libsodiumDebianOnetimeauthLib.text.externs := by decide
  have h := findSome_stub hL.1 e he libsodiumDebianOnetimeauthLib.text.externs
    (fun x hx => by rw [hfns]; exact hx)
  have hany : libsodiumDebianOnetimeauthLib.text.externs.any
      (fun e' => (pl.ρ e' - pl.base).toNat == (pl.ρ e - pl.base).toNat) = true := by
    rw [List.any_eq_true]; exact ⟨e, by rw [← hfns]; exact he, by simp⟩
  rw [hany, if_pos rfl] at h
  have hdef : (P pl ex).externAt? (pl.ρ e) =
      ((libsodiumDebianOnetimeauthLib.text.externs.map fun e' => (e', (pl.ρ e' - pl.base).toNat)).findSome?
        (fun (n, o) => if o == (pl.ρ e - pl.base).toNat then ex n else none)).or
      (libsodiumDebianOnetimeauthLib.text.symbols.findSome?
        (fun (n, o) => if o == (pl.ρ e - pl.base).toNat then (none : Option (State → State)) else none)) :=
    rfl
  rw [hdef, h]
  cases ex e with
  | some f => rfl
  | none =>
    rw [Option.none_or, List.findSome?_eq_none_iff]; intro x _; simp

/-- Byte `k < 4` of the word at aligned offset `off` of the placed code. -/
theorem read8_code {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
    (hCL : (P pl ex).CodeLoaded m) {off k : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 1800) (hk : k < 4) :
    m.read8 (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      (libsodiumDebianOnetimeauthText.patchedWord pl off).extractLsb' (8 * k) 8 ∧
    m.perm (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (P pl ex).code.length = 1800 := patched_length pl
  have h := codeLoaded_cell hCL (off + k) (by omega)
  have ha : pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
      (P pl ex).base + BitVec.ofNat 64 (off + k) := by
    show _ = pl.base + _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  refine ⟨?_, h.2⟩
  rw [h.1]
  have ht := take4_drop_patched (blk := libsodiumDebianOnetimeauthText) (pl := pl) hal
    (by rw [show libsodiumDebianOnetimeauthText.code = libsodiumDebianOnetimeauthPlacedCode from rfl, code_length]; exact hlen)
  have e1 : (P pl ex).code[off + k]'(by omega) =
      (((libsodiumDebianOnetimeauthText.patched pl).drop off).take 4)[k]'(by
        simp [List.length_take, List.length_drop, patched_length]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + i < 32 := by omega
  simp [hi, this]; omega

theorem fetch_word {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
    (hP : libsodiumDebianOnetimeauthLib.Placeable pl)
    (hCL : (P pl ex).CodeLoaded m) {off : Nat} (hal : off % 4 = 0) (hlen : off + 4 ≤ 1800) :
    (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (libsodiumDebianOnetimeauthText.patchedWord pl off) := by
  have hb4 : pl.base.toNat % 4 = 0 := by
    have := hP.text.base_aligned
    simp [libsodiumDebianOnetimeauthLib, libsodiumDebianOnetimeauthText] at this; omega
  have hnw : pl.base.toNat + 1800 ≤ 2 ^ 64 := by
    have := hP.text.no_wrap
    have hl : libsodiumDebianOnetimeauthText.code.length = 1800 := code_length
    rw [show libsodiumDebianOnetimeauthLib.text = libsodiumDebianOnetimeauthText from rfl, hl] at this
    exact this
  have hpc : (pl.base + BitVec.ofNat 64 off).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
    have h2 : (pl.base.toNat + off) % 2 ^ 64 = pl.base.toNat + off := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]; omega
  have r0 := read8_code hCL hal hlen (k := 0) (by omega)
  have r1 := read8_code hCL hal hlen (k := 1) (by omega)
  have r2 := read8_code hCL hal hlen (k := 2) (by omega)
  have r3 := read8_code hCL hal hlen (k := 3) (by omega)
  simp only [Program.fetchMem, hook_none_in hP ex (show off < 1800 by omega), Option.isSome_none,
    Bool.false_eq_true, if_false, hpc, ne_eq, not_true_eq_false]
  generalize ha : pl.base + BitVec.ofNat 64 off = a at *
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at r0 r1 r2 r3
  have hx : m.canExec a 4 = true := by
    simp only [Memory.canExec, Memory.allPerm, BitVec.add_assoc, BitVec.reduceAdd]
    simp only [BitVec.add_zero] at r0
    simp [r0.2, r1.2, r2.2, r3.2, Perm.rx]
  simp only [hx, Bool.not_true, Bool.false_eq_true, if_false]
  congr 1
  simp only [Memory.read32]
  rw [r0.1, r1.1, r2.1, r3.1]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

theorem patchedWord_plain (pl : Placement) {off : Nat}
    (h : libsodiumDebianOnetimeauthText.relocAt? off = none) :
    libsodiumDebianOnetimeauthText.patchedWord pl off = libsodiumDebianOnetimeauthText.wordAt off := by
  simp [CodeBlock.patchedWord, h]

end Poly1305Debian.FD

end
end

section
section
/-! # One lemma per instruction shape of `poly1305_finish`, on abstract states `mkS`

Some lemmas are copied from the x25519 `G` tree (`Solutions/X25519DalekField/G/Steps.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj

theorem awc_false_fst (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]
  omega

theorem awc_sub (x y : BitVec 64) : (AddWithCarry64 x (~~~y) true).1 = x - y := by
  simp only [AddWithCarry64, if_true]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have hx := x.isLt; have hy := y.isLt
  omega

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_stp64_pre_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw1 : m.canWrite (sp + off) 8 = true)
    (hw2 : m.canWrite (sp + off + 8#64) 8 = true) :
    execInstWithSvc svc (.stp .W64 (.gpr a) (.gpr b) (.PreIndex .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r (sp + off) ps
        ((m.write64 (sp + off) (r a)).write64 (sp + off + 8#64) (r b)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hw1, hw2, ha, hb,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_stp64_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw1 : m.canWrite (sp + off) 8 = true)
    (hw2 : m.canWrite (sp + off + 8#64) 8 = true) :
    execInstWithSvc svc (.stp .W64 (.gpr a) (.gpr b) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps ((m.write64 (sp + off) (r a)).write64 (sp + off + 8#64) (r b)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hw1, hw2, ha, hb,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_stp64_gpr (a b n : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hn : n ≠ 31#5)
    (off : BitVec 64) (hw1 : m.canWrite (r n + off) 8 = true)
    (hw2 : m.canWrite (r n + off + 8#64) 8 = true) :
    execInstWithSvc svc (.stp .W64 (.gpr a) (.gpr b) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps
        ((m.write64 (r n + off) (r a)).write64 (r n + off + 8#64) (r b)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw1, hw2, ha, hb, hn,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_ldp64_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr1 : m.canRead (sp + off) 8 = true)
    (hr2 : m.canRead (sp + off + 8#64) 8 = true) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a (m.read64 (sp + off))) b (m.read64 (sp + off + 8#64)))
        sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hr1, hr2, ha, hb,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_ldp64_post_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr1 : m.canRead sp 8 = true)
    (hr2 : m.canRead (sp + 8#64) 8 = true) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.PostIndex .sp off))
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a (m.read64 sp)) b (m.read64 (sp + 8#64)))
        (sp + off) ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hr1, hr2, ha, hb,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_ldp64_gpr (a b n : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hn : n ≠ 31#5)
    (off : BitVec 64) (hr1 : m.canRead (r n + off) 8 = true)
    (hr2 : m.canRead (r n + off + 8#64) 8 = true) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.Offset (.gpr n) off))
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a (m.read64 (r n + off))) b (m.read64 (r n + off + 8#64)))
        sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hr1, hr2, ha, hb, hn,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_ldr64_gpr (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hr : m.canRead (r n + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a (m.read64 (r n + off))) sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hr, ha, hn,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_strb_off (t n : BitVec 5) (ht : t ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hw : m.canWrite (r n + off) 1 = true) :
    execInstWithSvc svc (.str .B8 (.gpr t) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write8 (r n + off) ((r t).truncate 8)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw, ht, hn,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_mov (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr n) .LSL 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n)) sp ps m v := by
  simp [execInstWithSvc, execLogicalShift, evalLogical, State.readReg, State.writeReg, shiftVal,
    shift64, hd, hn]

theorem ex_add_gpr_sp (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD (.gpr d) .sp imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (sp + imm.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_false_fst, hd]

theorem ex_add_imm (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD (.gpr d) (.gpr n) imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n + imm.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_false_fst, hd, hn]

theorem ex_cmp_imm (n : BitVec 5) (hn : n ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .SUBS .xzr (.gpr n) imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp (AddWithCarry64 (r n) (~~~(imm.zeroExtend 64)) true).2 m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, hn]

theorem ex_movz32 (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 16) :
    execInstWithSvc svc (.moveWide .W32 .MOVZ (.gpr d) imm 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d ((imm.zeroExtend 64).truncate 32 |>.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, State.writeReg, hd]

theorem ex_and_imm (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm .W64 .AND (.gpr d) (.gpr n) mask) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n &&& mask)) sp ps m v := by
  simp [execInstWithSvc, evalLogical, State.readReg, State.writeReg, hd, hn]

theorem ex_add_shift (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (sh : ShiftType) (amt : Nat) :
    execInstWithSvc svc (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) sh amt)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n + shift64 (r k) sh amt)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, shiftVal, awc_false_fst, hd, hn,
    hk]

theorem ex_orr_shift (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (sh : ShiftType) (amt : Nat) :
    execInstWithSvc svc (.logicalShift .W64 .ORR (.gpr d) (.gpr n) (.gpr k) sh amt)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n ||| shift64 (r k) sh amt)) sp ps m v := by
  simp [execInstWithSvc, evalLogical, State.readReg, State.writeReg, shiftVal, hd, hn, hk]

theorem ex_and_shift (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (sh : ShiftType) (amt : Nat) :
    execInstWithSvc svc (.logicalShift .W64 .AND (.gpr d) (.gpr n) (.gpr k) sh amt)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n &&& shift64 (r k) sh amt)) sp ps m v := by
  simp [execInstWithSvc, evalLogical, State.readReg, State.writeReg, shiftVal, hd, hn, hk]

theorem ex_bitfield (op : BitfieldOp) (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5)
    (immr imms : Nat) :
    execInstWithSvc svc (.bitfield .W64 op (.gpr d) (.gpr n) immr imms) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (evalBitfield .W64 op (r d) (r n) immr imms)) sp ps m v := by
  simp [execInstWithSvc, State.readReg, State.writeReg, hd, hn]

theorem ex_extr (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) (lsb : Nat) :
    execInstWithSvc svc (.extr .W64 (.gpr d) (.gpr n) (.gpr k) lsb) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (((r n ++ r k) >>> (lsb % 64)).truncate 64)) sp ps m v := by
  simp [execInstWithSvc, State.writeReg, hd, hn, hk]

theorem ex_cbz (t : BitVec 5) (ht : t ≠ 31#5) (off : BitVec 64) :
    execInstWithSvc svc (.cbz .W64 false (.gpr t) off) (mkS s0 pc r sp ps m v) =
      mkS s0 (if r t = 0#64 then pc + off else pc + 4#64) r sp ps m v := by
  by_cases h : r t = 0#64 <;> simp [execInstWithSvc, State.readReg, ht, h]

theorem ex_bcond (c : CondCode) (off : BitVec 64) :
    execInstWithSvc svc (.bCond c off) (mkS s0 pc r sp ps m v) =
      mkS s0 (if ConditionHolds c ps then pc + off else pc + 4#64) r sp ps m v := by
  by_cases h : ConditionHolds c ps <;> simp [execInstWithSvc, h]

theorem ex_bl (off : BitVec 64) :
    execInstWithSvc svc (.bl off) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + off) (upd r 30#5 (pc + 4#64)) sp ps m v := by
  simp [execInstWithSvc]

theorem ex_b (off : BitVec 64) :
    execInstWithSvc svc (.b off) (mkS s0 pc r sp ps m v) = mkS s0 (pc + off) r sp ps m v := by
  simp [execInstWithSvc]

end exec

/-! ## Flags of `cmp` -/

theorem res_eq (x y : BitVec 64) : ((AddWithCarry64 x (~~~y) true).2.z) = decide (x = y) := by
  simp only [AddWithCarry64, if_true]
  have hx := x.isLt; have hy := y.isLt
  by_cases h : x = y
  · subst h; simp; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_not]; omega
  · simp only [h, decide_false, beq_eq_false_iff_ne]
    intro e; apply h; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e
    simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_not] at this
    omega
theorem c_eq (x y : BitVec 64) : ((AddWithCarry64 x (~~~y) true).2.c) = decide (y.toNat ≤ x.toNat) := by
  simp only [AddWithCarry64, if_true]
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.msb_eq_decide]
  simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_not]
  omega
theorem hi_cmp (x y : BitVec 64) :
    ConditionHolds .HI (AddWithCarry64 x (~~~y) true).2 = decide (y.toNat < x.toNat) := by
  simp only [ConditionHolds, c_eq, res_eq]
  by_cases h : x = y
  · subst h; simp
  · have : x.toNat ≠ y.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp [h]; omega

end Poly1305Debian.FD

end
end

section
section
/-! # The instruction at each address of Debian's `poly1305_finish` (text offsets 0x420..0x560)

Generated from `decode (wordAt off)`; the two relocated branches (`bl memset` at +0x4c,
`b sodium_memzero` at +0x140) are in `Reloc.lean`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj

section
variable {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
  (hP : libsodiumDebianOnetimeauthLib.Placeable pl) (hCL : (P pl ex).CodeLoaded m)
include hP hCL

theorem f_0 : (P pl ex).fetchMem m (pl.base + 1056#64) = Arm64.Instr.hint 0x19#7 := by
  rw [show pl.base + 1056#64 = pl.base + BitVec.ofNat 64 1056 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_4 : (P pl ex).fetchMem m (pl.base + 1060#64) = Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xffffffffffffffe0#64) := by
  rw [show pl.base + 1060#64 = pl.base + BitVec.ofNat 64 1060 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_8 : (P pl ex).fetchMem m (pl.base + 1064#64) = Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.sp) 0x000#12 false := by
  rw [show pl.base + 1064#64 = pl.base + BitVec.ofNat 64 1064 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c : (P pl ex).fetchMem m (pl.base + 1068#64) = Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x14#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64) := by
  rw [show pl.base + 1068#64 = pl.base + BitVec.ofNat 64 1068 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_10 : (P pl ex).fetchMem m (pl.base + 1072#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1072#64 = pl.base + BitVec.ofNat 64 1072 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_14 : (P pl ex).fetchMem m (pl.base + 1076#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1076#64 = pl.base + BitVec.ofNat 64 1076 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_18 : (P pl ex).fetchMem m (pl.base + 1080#64) = Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000040#64) := by
  rw [show pl.base + 1080#64 = pl.base + BitVec.ofNat 64 1080 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1c : (P pl ex).fetchMem m (pl.base + 1084#64) = Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x01#5) 0x000000000000004c#64 := by
  rw [show pl.base + 1084#64 = pl.base + BitVec.ofNat 64 1084 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_20 : (P pl ex).fetchMem m (pl.base + 1088#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1088#64 = pl.base + BitVec.ofNat 64 1088 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_24 : (P pl ex).fetchMem m (pl.base + 1092#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x02#5) 0x0001#16 0 := by
  rw [show pl.base + 1092#64 = pl.base + BitVec.ofNat 64 1092 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_28 : (P pl ex).fetchMem m (pl.base + 1096#64) = Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x02#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000048#64) := by
  rw [show pl.base + 1096#64 = pl.base + BitVec.ofNat 64 1096 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_2c : (P pl ex).fetchMem m (pl.base + 1100#64) = Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x01#5) 0x001#12 false := by
  rw [show pl.base + 1100#64 = pl.base + BitVec.ofNat 64 1100 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_30 : (P pl ex).fetchMem m (pl.base + 1104#64) = Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) 0x00f#12 false := by
  rw [show pl.base + 1104#64 = pl.base + BitVec.ofNat 64 1104 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_34 : (P pl ex).fetchMem m (pl.base + 1108#64) = Arm64.Instr.bCond (Arm64.CondCode.HI) 0x000000000000001c#64 := by
  rw [show pl.base + 1108#64 = pl.base + BitVec.ofNat 64 1108 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_38 : (P pl ex).fetchMem m (pl.base + 1112#64) = Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x01#5) 0x049#12 false := by
  rw [show pl.base + 1112#64 = pl.base + BitVec.ofNat 64 1112 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_3c : (P pl ex).fetchMem m (pl.base + 1116#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x02#5) 0x000f#16 0 := by
  rw [show pl.base + 1116#64 = pl.base + BitVec.ofNat 64 1116 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_40 : (P pl ex).fetchMem m (pl.base + 1120#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1120#64 = pl.base + BitVec.ofNat 64 1120 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_44 : (P pl ex).fetchMem m (pl.base + 1124#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1124#64 = pl.base + BitVec.ofNat 64 1124 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_48 : (P pl ex).fetchMem m (pl.base + 1128#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0000#16 0 := by
  rw [show pl.base + 1128#64 = pl.base + BitVec.ofNat 64 1128 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_50 : (P pl ex).fetchMem m (pl.base + 1136#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x00#5) 0x0001#16 0 := by
  rw [show pl.base + 1136#64 = pl.base + BitVec.ofNat 64 1136 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_54 : (P pl ex).fetchMem m (pl.base + 1140#64) = Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000058#64) := by
  rw [show pl.base + 1140#64 = pl.base + BitVec.ofNat 64 1140 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_58 : (P pl ex).fetchMem m (pl.base + 1144#64) = Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x13#5) 0x048#12 false := by
  rw [show pl.base + 1144#64 = pl.base + BitVec.ofNat 64 1144 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_5c : (P pl ex).fetchMem m (pl.base + 1148#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x13#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1148#64 = pl.base + BitVec.ofNat 64 1148 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_60 : (P pl ex).fetchMem m (pl.base + 1152#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x02#5) 0x0010#16 0 := by
  rw [show pl.base + 1152#64 = pl.base + BitVec.ofNat 64 1152 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_64 : (P pl ex).fetchMem m (pl.base + 1156#64) = Arm64.Instr.bl 0xfffffffffffffd1c#64 := by
  rw [show pl.base + 1156#64 = pl.base + BitVec.ofNat 64 1156 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_68 : (P pl ex).fetchMem m (pl.base + 1160#64) = Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x02#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000018#64) := by
  rw [show pl.base + 1160#64 = pl.base + BitVec.ofNat 64 1160 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_6c : (P pl ex).fetchMem m (pl.base + 1164#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x03#5) 0x0005#16 0 := by
  rw [show pl.base + 1164#64 = pl.base + BitVec.ofNat 64 1164 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_70 : (P pl ex).fetchMem m (pl.base + 1168#64) = Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000028#64) := by
  rw [show pl.base + 1168#64 = pl.base + BitVec.ofNat 64 1168 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_74 : (P pl ex).fetchMem m (pl.base + 1172#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x02#5) 0x00000fffffffffff#64 := by
  rw [show pl.base + 1172#64 = pl.base + BitVec.ofNat 64 1172 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_78 : (P pl ex).fetchMem m (pl.base + 1176#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSR) 44 := by
  rw [show pl.base + 1176#64 = pl.base + BitVec.ofNat 64 1176 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_7c : (P pl ex).fetchMem m (pl.base + 1180#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) 0x000003ffffffffff#64 := by
  rw [show pl.base + 1180#64 = pl.base + BitVec.ofNat 64 1180 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_80 : (P pl ex).fetchMem m (pl.base + 1184#64) = Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) 42 63 := by
  rw [show pl.base + 1184#64 = pl.base + BitVec.ofNat 64 1184 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_84 : (P pl ex).fetchMem m (pl.base + 1188#64) = Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x05#5) := by
  rw [show pl.base + 1188#64 = pl.base + BitVec.ofNat 64 1188 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_88 : (P pl ex).fetchMem m (pl.base + 1192#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x02#5) 0x00000fffffffffff#64 := by
  rw [show pl.base + 1192#64 = pl.base + BitVec.ofNat 64 1192 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_8c : (P pl ex).fetchMem m (pl.base + 1196#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSR) 44 := by
  rw [show pl.base + 1196#64 = pl.base + BitVec.ofNat 64 1196 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_90 : (P pl ex).fetchMem m (pl.base + 1200#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x02#5) 0x00000fffffffffff#64 := by
  rw [show pl.base + 1200#64 = pl.base + BitVec.ofNat 64 1200 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_94 : (P pl ex).fetchMem m (pl.base + 1204#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSR) 44 := by
  rw [show pl.base + 1204#64 = pl.base + BitVec.ofNat 64 1204 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_98 : (P pl ex).fetchMem m (pl.base + 1208#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x02#5) 0x000003ffffffffff#64 := by
  rw [show pl.base + 1208#64 = pl.base + BitVec.ofNat 64 1208 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_9c : (P pl ex).fetchMem m (pl.base + 1212#64) = Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) 42 63 := by
  rw [show pl.base + 1212#64 = pl.base + BitVec.ofNat 64 1212 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a0 : (P pl ex).fetchMem m (pl.base + 1216#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) 0xfffffc0000000000#64 := by
  rw [show pl.base + 1216#64 = pl.base + BitVec.ofNat 64 1216 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a4 : (P pl ex).fetchMem m (pl.base + 1220#64) = Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x05#5) := by
  rw [show pl.base + 1220#64 = pl.base + BitVec.ofNat 64 1220 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a8 : (P pl ex).fetchMem m (pl.base + 1224#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x05#5) 0x0000#16 0 := by
  rw [show pl.base + 1224#64 = pl.base + BitVec.ofNat 64 1224 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ac : (P pl ex).fetchMem m (pl.base + 1228#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x00#5) 0x00000fffffffffff#64 := by
  rw [show pl.base + 1228#64 = pl.base + BitVec.ofNat 64 1228 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b0 : (P pl ex).fetchMem m (pl.base + 1232#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSR) 44 := by
  rw [show pl.base + 1232#64 = pl.base + BitVec.ofNat 64 1232 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b4 : (P pl ex).fetchMem m (pl.base + 1236#64) = Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x07#5) 0x005#12 false := by
  rw [show pl.base + 1236#64 = pl.base + BitVec.ofNat 64 1236 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b8 : (P pl ex).fetchMem m (pl.base + 1240#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x04#5) (Arm64.ShiftType.LSR) 44 := by
  rw [show pl.base + 1240#64 = pl.base + BitVec.ofNat 64 1240 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_bc : (P pl ex).fetchMem m (pl.base + 1244#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSR) 44 := by
  rw [show pl.base + 1244#64 = pl.base + BitVec.ofNat 64 1244 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c0 : (P pl ex).fetchMem m (pl.base + 1248#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x05#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1248#64 = pl.base + BitVec.ofNat 64 1248 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c4 : (P pl ex).fetchMem m (pl.base + 1252#64) = Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINV) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.CondCode.LT) := by
  rw [show pl.base + 1252#64 = pl.base + BitVec.ofNat 64 1252 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c8 : (P pl ex).fetchMem m (pl.base + 1256#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.ASR) 63 := by
  rw [show pl.base + 1256#64 = pl.base + BitVec.ofNat 64 1256 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_cc : (P pl ex).fetchMem m (pl.base + 1260#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1260#64 = pl.base + BitVec.ofNat 64 1260 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d0 : (P pl ex).fetchMem m (pl.base + 1264#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1264#64 = pl.base + BitVec.ofNat 64 1264 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d4 : (P pl ex).fetchMem m (pl.base + 1268#64) = Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000038#64) := by
  rw [show pl.base + 1268#64 = pl.base + BitVec.ofNat 64 1268 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d8 : (P pl ex).fetchMem m (pl.base + 1272#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) 0x00000fffffffffff#64 := by
  rw [show pl.base + 1272#64 = pl.base + BitVec.ofNat 64 1272 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_dc : (P pl ex).fetchMem m (pl.base + 1276#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x07#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1276#64 = pl.base + BitVec.ofNat 64 1276 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e0 : (P pl ex).fetchMem m (pl.base + 1280#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.ASR) 63 := by
  rw [show pl.base + 1280#64 = pl.base + BitVec.ofNat 64 1280 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e4 : (P pl ex).fetchMem m (pl.base + 1284#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) 0x00000fffffffffff#64 := by
  rw [show pl.base + 1284#64 = pl.base + BitVec.ofNat 64 1284 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e8 : (P pl ex).fetchMem m (pl.base + 1288#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x01#5) 0x00000fffffffffff#64 := by
  rw [show pl.base + 1288#64 = pl.base + BitVec.ofNat 64 1288 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ec : (P pl ex).fetchMem m (pl.base + 1292#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x06#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1292#64 = pl.base + BitVec.ofNat 64 1292 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f0 : (P pl ex).fetchMem m (pl.base + 1296#64) = Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x01#5) 44 := by
  rw [show pl.base + 1296#64 = pl.base + BitVec.ofNat 64 1296 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f4 : (P pl ex).fetchMem m (pl.base + 1300#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1300#64 = pl.base + BitVec.ofNat 64 1300 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f8 : (P pl ex).fetchMem m (pl.base + 1304#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x01#5) 0x00000fffffffffff#64 := by
  rw [show pl.base + 1304#64 = pl.base + BitVec.ofNat 64 1304 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_fc : (P pl ex).fetchMem m (pl.base + 1308#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.ASR) 63 := by
  rw [show pl.base + 1308#64 = pl.base + BitVec.ofNat 64 1308 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_100 : (P pl ex).fetchMem m (pl.base + 1312#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1312#64 = pl.base + BitVec.ofNat 64 1312 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_104 : (P pl ex).fetchMem m (pl.base + 1316#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1316#64 = pl.base + BitVec.ofNat 64 1316 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_108 : (P pl ex).fetchMem m (pl.base + 1320#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x00#5) 0x00000fffffffffff#64 := by
  rw [show pl.base + 1320#64 = pl.base + BitVec.ofNat 64 1320 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_10c : (P pl ex).fetchMem m (pl.base + 1324#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x07#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1324#64 = pl.base + BitVec.ofNat 64 1324 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_110 : (P pl ex).fetchMem m (pl.base + 1328#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSR) 44 := by
  rw [show pl.base + 1328#64 = pl.base + BitVec.ofNat 64 1328 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_114 : (P pl ex).fetchMem m (pl.base + 1332#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) (Arm64.ShiftType.LSR) 24 := by
  rw [show pl.base + 1332#64 = pl.base + BitVec.ofNat 64 1332 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_118 : (P pl ex).fetchMem m (pl.base + 1336#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSR) 44 := by
  rw [show pl.base + 1336#64 = pl.base + BitVec.ofNat 64 1336 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_11c : (P pl ex).fetchMem m (pl.base + 1340#64) = Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x00#5) 20 43 := by
  rw [show pl.base + 1340#64 = pl.base + BitVec.ofNat 64 1340 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_120 : (P pl ex).fetchMem m (pl.base + 1344#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 44 := by
  rw [show pl.base + 1344#64 = pl.base + BitVec.ofNat 64 1344 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_124 : (P pl ex).fetchMem m (pl.base + 1348#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x04#5) (Arm64.ShiftType.LSL) 24 := by
  rw [show pl.base + 1348#64 = pl.base + BitVec.ofNat 64 1348 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_128 : (P pl ex).fetchMem m (pl.base + 1352#64) = Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x14#5) 0x0000000000000000#64) := by
  rw [show pl.base + 1352#64 = pl.base + BitVec.ofNat 64 1352 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_12c : (P pl ex).fetchMem m (pl.base + 1356#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x13#5) (Arm64.ShiftType.LSL) 0 := by
  rw [show pl.base + 1356#64 = pl.base + BitVec.ofNat 64 1356 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_130 : (P pl ex).fetchMem m (pl.base + 1360#64) = Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x14#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64) := by
  rw [show pl.base + 1360#64 = pl.base + BitVec.ofNat 64 1360 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_134 : (P pl ex).fetchMem m (pl.base + 1364#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0060#16 0 := by
  rw [show pl.base + 1364#64 = pl.base + BitVec.ofNat 64 1364 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_138 : (P pl ex).fetchMem m (pl.base + 1368#64) = Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000020#64) := by
  rw [show pl.base + 1368#64 = pl.base + BitVec.ofNat 64 1368 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_13c : (P pl ex).fetchMem m (pl.base + 1372#64) = Arm64.Instr.hint 0x1d#7 := by
  rw [show pl.base + 1372#64 = pl.base + BitVec.ofNat 64 1372 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

end

end Poly1305Debian.FD

end
end

section
section
/-! # The relocated branches of `poly1305_finish`

Decoding lemmas copied from `Solutions/X25519DalekField/G/Reloc.lean` (which follows the zlib
CRC-32 mission's `RelocBase`), plus the `B` case. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj

theorem beq_false_of_mask {w K A M C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A &&& M) :
    (w &&& M == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, ← hK, BitVec.and_assoc, BitVec.and_comm M K, ← BitVec.and_assoc]

theorem beq_false_of_mask' {w K A C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A) :
    (w == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, hK]

theorem decode_b_class (w : BitVec 32) (hK : w &&& 0x7c000000#32 = 0x14000000#32) :
    decode w = some (if w.getLsbD 31 then .bl (((w.extractLsb' 0 26).signExtend 64) <<< 2)
      else .b (((w.extractLsb' 0 26).signExtend 64) <<< 2)) := by
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
    beq_false_of_mask hK (C := 0x13800000#32) (M := 0x7f800000#32) (by decide), hK]
  cases h : w.getLsbD 31 <;> simp [h]

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

/-- A relocated `BL` (template `0x94000000`) calls its target. -/
theorem decode_branchWord_bl {P T : BitVec 64} (hr : BranchInRange P T) :
    decode (branchWord 0x94000000#32 P T) = some (.bl (T - P)) := by
  have hm : ((0x94000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32))
      &&& 0x7c000000#32 = 0x14000000#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
    interval_cases i <;> simp
  have h31 : ((0x94000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32)).getLsbD 31
      = true := by simp
  have hoff : ((((0x94000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32)).extractLsb' 0 26).signExtend 64)
      <<< 2 = T - P := by
    have hlo := lo_bits2 _ hr.1
    have hhi := hi_bits27 _ hr.2.1 hr.2.2
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
      BitVec.msb_eq_getLsbD_last]
    interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
      first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
        exact (hhi _ (by omega) (by omega)).symm | rfl
  rw [branchWord, decode_b_class _ hm, h31, if_pos rfl, hoff]

/-- A relocated `B` (template `0x14000000`) branches to its target. -/
theorem decode_branchWord_b {P T : BitVec 64} (hr : BranchInRange P T) :
    decode (branchWord 0x14000000#32 P T) = some (.b (T - P)) := by
  have hm : ((0x14000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32))
      &&& 0x7c000000#32 = 0x14000000#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
    interval_cases i <;> simp
  have h31 : ((0x14000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32)).getLsbD 31
      = false := by simp
  have hoff : ((((0x14000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32)).extractLsb' 0 26).signExtend 64)
      <<< 2 = T - P := by
    have hlo := lo_bits2 _ hr.1
    have hhi := hi_bits27 _ hr.2.1 hr.2.2
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
      BitVec.msb_eq_getLsbD_last]
    interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
      first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
        exact (hhi _ (by omega) (by omega)).symm | rfl
  rw [branchWord, decode_b_class _ hm, h31]; simp only [Bool.false_eq_true, if_false, hoff]

abbrev rBl : RelocEntry := { off := 1132, kind := .call26, sym := "memset" }
abbrev rB : RelocEntry := { off := 1376, kind := .jump26, sym := "sodium_memzero" }

theorem rBl_mem : rBl ∈ libsodiumDebianOnetimeauthLib.text.relocs := by decide
theorem rB_mem : rB ∈ libsodiumDebianOnetimeauthLib.text.relocs := by decide

theorem relocTarget_bl (pl : Placement) :
    libsodiumDebianOnetimeauthText.relocTarget pl 1132 rBl = pl.ρ "memset" := by
  have hb : libsodiumDebianOnetimeauthText.b2bNext? rBl = none := by decide
  have hl : lookup "memset" libsodiumDebianOnetimeauthText.symbols = none := by decide
  simp only [CodeBlock.relocTarget, hb, ite_self, CodeBlock.target, CodeBlock.resolve, hl]
  simp [addSignedAddr]

theorem relocTarget_b (pl : Placement) :
    libsodiumDebianOnetimeauthText.relocTarget pl 1376 rB = pl.ρ "sodium_memzero" := by
  have hb : libsodiumDebianOnetimeauthText.b2bNext? rB = none := by decide
  have hl : lookup "sodium_memzero" libsodiumDebianOnetimeauthText.symbols = none := by decide
  simp only [CodeBlock.relocTarget, hb, ite_self, CodeBlock.target, CodeBlock.resolve, hl]
  simp [addSignedAddr]

section
variable {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
  (hP : libsodiumDebianOnetimeauthLib.Placeable pl) (hCL : (P pl ex).CodeLoaded m)
include hP hCL

theorem f_4c : (P pl ex).fetchMem m (pl.base + 1132#64) =
    some (.bl (pl.ρ "memset" - (pl.base + 1132#64))) := by
  have hrange : BranchInRange (pl.base + BitVec.ofNat 64 1132) (pl.ρ "memset") := by
    have h := (hP.text.relocs_ok _ rBl_mem).2.2
    rw [show libsodiumDebianOnetimeauthLib.text = libsodiumDebianOnetimeauthText from rfl, relocTarget_bl] at h
    exact h
  have hpw : libsodiumDebianOnetimeauthText.patchedWord pl 1132 =
      branchWord 0x94000000#32 (pl.base + BitVec.ofNat 64 1132) (pl.ρ "memset") := by
    have hr : libsodiumDebianOnetimeauthText.relocAt? 1132 = some rBl := by decide
    have hw : libsodiumDebianOnetimeauthText.wordAt 1132 = 0x94000000#32 := by decide +kernel
    have hx1 : libsodiumDebianOnetimeauthText.relaxableAt 1132 = false := by decide
    have hx2 : libsodiumDebianOnetimeauthText.relaxableAt (1132 - 4) = false := by decide
    have hr1 : libsodiumDebianOnetimeauthText.relaxedAt pl 1132 = false := by simp [CodeBlock.relaxedAt, hx1]
    have hr2 : libsodiumDebianOnetimeauthText.relaxedAt pl (1132 - 4) = false := by
      simp [CodeBlock.relaxedAt, hx2]
    have hu : libsodiumDebianOnetimeauthText.undefWeakBranch pl rBl = false := by
      simp [CodeBlock.undefWeakBranch, libsodiumDebianOnetimeauthText]
    rw [CodeBlock.patchedWord]
    simp only [hr, hr1, hr2, hw, hu, Bool.false_eq_true, if_false, Bool.and_false,
      relocTarget_bl]
    simp [RelocKind.isGotOrTlsIe, patchRelocWord]
  rw [show pl.base + 1132#64 = pl.base + BitVec.ofNat 64 1132 from rfl,
    fetch_word hP hCL (by decide) (by decide), hpw, decode_branchWord_bl hrange]

theorem f_140 : (P pl ex).fetchMem m (pl.base + 1376#64) =
    some (.b (pl.ρ "sodium_memzero" - (pl.base + 1376#64))) := by
  have hrange : BranchInRange (pl.base + BitVec.ofNat 64 1376) (pl.ρ "sodium_memzero") := by
    have h := (hP.text.relocs_ok _ rB_mem).2.2
    rw [show libsodiumDebianOnetimeauthLib.text = libsodiumDebianOnetimeauthText from rfl, relocTarget_b] at h
    exact h
  have hpw : libsodiumDebianOnetimeauthText.patchedWord pl 1376 =
      branchWord 0x14000000#32 (pl.base + BitVec.ofNat 64 1376) (pl.ρ "sodium_memzero") := by
    have hr : libsodiumDebianOnetimeauthText.relocAt? 1376 = some rB := by decide
    have hw : libsodiumDebianOnetimeauthText.wordAt 1376 = 0x14000000#32 := by decide +kernel
    have hx1 : libsodiumDebianOnetimeauthText.relaxableAt 1376 = false := by decide
    have hx2 : libsodiumDebianOnetimeauthText.relaxableAt (1376 - 4) = false := by decide
    have hr1 : libsodiumDebianOnetimeauthText.relaxedAt pl 1376 = false := by simp [CodeBlock.relaxedAt, hx1]
    have hr2 : libsodiumDebianOnetimeauthText.relaxedAt pl (1376 - 4) = false := by
      simp [CodeBlock.relaxedAt, hx2]
    have hu : libsodiumDebianOnetimeauthText.undefWeakBranch pl rB = false := by
      simp [CodeBlock.undefWeakBranch, libsodiumDebianOnetimeauthText]
    rw [CodeBlock.patchedWord]
    simp only [hr, hr1, hr2, hw, hu, Bool.false_eq_true, if_false, Bool.and_false,
      relocTarget_b]
    simp [RelocKind.isGotOrTlsIe, patchRelocWord]
  rw [show pl.base + 1376#64 = pl.base + BitVec.ofNat 64 1376 from rfl,
    fetch_word hP hCL (by decide) (by decide), hpw, decode_branchWord_b hrange]

end

end Poly1305Debian.FD

end
end

section
section
/-! # 64-bit reads and writes inside owned byte lists; stack regions

`memRegion_split`, `memRegion_merge`, `pack64` and `unpack64_pack64` are copied from the x25519
`G` tree (`Solutions/X25519DalekField/G/Mem.lean`, `Solutions/X25519DalekEdwards/Dbl/Frame.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj Poly1305Boringssl

theorem memRegion_split (a : BitVec 64) (n k : Nat) (hnk : n + k < 2 ^ 64) :
    memRegion a (n + k) ⊢ memRegion a n ∗ memRegion (a + BitVec.ofNat 64 n) k := by
  intro h hh
  obtain ⟨bs, hb⟩ := memRegion_entails_bytes a (n + k) hnk h hh
  obtain ⟨hl, hb⟩ := pure_sepConj_holds.mp hb
  rw [pointsToBytes_split a bs n (by omega)] at hb
  have e1 : (bs.take n).length = n := by simp [hl]
  have e2 : (bs.drop n).length = k := by simp [hl]
  have m1 := bytes_entails_memRegion a (bs.take n)
  have m2 := bytes_entails_memRegion (a + BitVec.ofNat 64 n) (bs.drop n)
  rw [e1] at m1
  rw [e2] at m2
  exact sepConj_mono m1 m2 h hb

theorem memRegion_merge (a b : BitVec 64) (n k : Nat) (hb : b = a + BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) (hk : k < 2 ^ 64) :
    memRegion a n ∗ memRegion b k ⊢ memRegion a (n + k) := by
  subst hb
  intro h hh
  have h2 := sepConj_mono (memRegion_entails_bytes a n hn)
    (memRegion_entails_bytes (a + BitVec.ofNat 64 n) k hk) h hh
  rw [sepExists_sepConj] at h2
  obtain ⟨bs1, h2⟩ := h2
  dsimp only at h2
  rw [sepConj_comm, sepExists_sepConj] at h2
  obtain ⟨bs2, h2⟩ := h2
  dsimp only at h2
  have h3 : (⌜bs1.length = n⌝ ∗ ⌜bs2.length = k⌝ ∗ (a ↦ₛ bs1) ∗
      ((a + BitVec.ofNat 64 n) ↦ₛ bs2)).holds h := by
    have := Entails.of_eq (P := (⌜bs2.length = k⌝ ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bs2)) ∗
      (⌜bs1.length = n⌝ ∗ (a ↦ₛ bs1)))
      (Q := ⌜bs1.length = n⌝ ∗ ⌜bs2.length = k⌝ ∗ (a ↦ₛ bs1) ∗
      ((a + BitVec.ofNat 64 n) ↦ₛ bs2))
    exact this h h2
  obtain ⟨hl1, h3⟩ := pure_sepConj_holds.mp h3
  obtain ⟨hl2, h3⟩ := pure_sepConj_holds.mp h3
  have := bytes_entails_memRegion a (bs1 ++ bs2)
  rw [pointsToBytes_append, hl1, List.length_append, hl1, hl2] at this
  exact this h h3

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

theorem app_toNat {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

theorem toNat_pack64 (l : List (BitVec 8)) (h : l.length = 8) :
    (pack64 l).toNat = leBytesToNum l := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    simp only [pack64, List.getD_cons_zero, List.getD_cons_succ, leBytesToNum, List.foldr_cons,
      List.foldr_nil, app_toNat]
    omega

/-- The 8 bytes at `off` of `bs` as a 64-bit cell. -/
theorem bytes_mid (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat) (h : off + 8 ≤ bs.length) :
    (a ↦ₛ bs) = (a ↦ₛ bs.take off) ∗
      ((a + BitVec.ofNat 64 off) ↦₆₄ pack64 ((bs.drop off).take 8)) ∗
      ((a + BitVec.ofNat 64 (off + 8)) ↦ₛ bs.drop (off + 8)) := by
  rw [pointsToBytes_split a bs off (by omega), pointsTo64_eq_bytes,
    unpack64_pack64 _ (by simp; omega)]
  congr 1
  rw [pointsToBytes_split _ (bs.drop off) 8 (by simp; omega), List.drop_drop, BitVec.add_assoc,
    ← BitVec.ofNat_add]

theorem sat_bytes_read64 {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (off : Nat) (h : off + 8 ≤ bs.length) :
    (m.read64 (a + BitVec.ofNat 64 off)).toNat = u64At bs off ∧
      m.canRead (a + BitVec.ofNat 64 off) 8 = true := by
  rw [bytes_mid a bs off h] at hs
  have hs' : m ⊨ ((a + BitVec.ofNat 64 off) ↦₆₄ pack64 ((bs.drop off).take 8)) ∗
      ((a ↦ₛ bs.take off) ∗ ((a + BitVec.ofNat 64 (off + 8)) ↦ₛ bs.drop (off + 8)) ∗ F) :=
    Satisfies.of_eq hs (by ac_rfl)
  obtain ⟨h1, h2, _⟩ := sat64_read hs'
  refine ⟨?_, h2⟩
  rw [h1, toNat_pack64 _ (by simp; omega)]; rfl

theorem sat_bytes_write64 {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (off : Nat) (h : off + 8 ≤ bs.length) (w : BitVec 64) :
    m.canWrite (a + BitVec.ofNat 64 off) 8 = true ∧
    m.write64 (a + BitVec.ofNat 64 off) w ⊨
      (a ↦ₛ (bs.take off ++ unpack64 w ++ bs.drop (off + 8))) ∗ F := by
  rw [bytes_mid a bs off h] at hs
  have hs' : m ⊨ ((a + BitVec.ofNat 64 off) ↦₆₄ pack64 ((bs.drop off).take 8)) ∗
      ((a ↦ₛ bs.take off) ∗ ((a + BitVec.ofNat 64 (off + 8)) ↦ₛ bs.drop (off + 8)) ∗ F) :=
    Satisfies.of_eq hs (by ac_rfl)
  refine ⟨(sat64_read hs').2.2, ?_⟩
  have hw := sat64_write hs' w
  have e : (bs.take off ++ unpack64 w ++ bs.drop (off + 8)) =
      bs.take off ++ (unpack64 w ++ bs.drop (off + 8)) := by simp
  rw [e, pointsToBytes_append, pointsToBytes_append, ← pointsTo64_eq_bytes]
  have l1 : (bs.take off).length = off := by simp; omega
  rw [l1, BitVec.add_assoc, ← BitVec.ofNat_add, show off + (unpack64 w).length = off + 8 by simp]
  exact Satisfies.of_eq hw (by ac_rfl)

end Poly1305Debian.FD

end
end

section
section
/-! # Forward execution from the entry state

A run is kept as `Steps (P pl ex) S0 s`; the code stays loaded along it
(`Arm64Facts.steps_codeLoaded_v2`), so every fetch lemma applies. An arithmetic step names its
result (`stepN`), so the register file stays a chain of `upd`s of variables. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj

theorem Steps.snoc {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Step p b c) :
    Steps p a c := Steps.trans' h1 (Steps.step h2 (Steps.refl _))

theorem cl {pl : Placement} {ex : String → Option (State → State)} {S0 s : State}
    (hCL0 : (P pl ex).CodeLoaded S0.mem) (h : Steps (P pl ex) S0 s) : (P pl ex).CodeLoaded s.mem :=
  Arm64Facts.steps_codeLoaded_v2 h hCL0

section
variable {pl : Placement} {ex : String → Option (State → State)} {S0 s0 : State}
  {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory}
  {v : BitVec 5 → BitVec 128} {i : Instr}

theorem stepS (hpath : Steps (P pl ex) S0 (mkS s0 pc r sp ps m v)) (hrun : s0.status = .Running)
    (hf : (P pl ex).fetchMem m pc = some i) {s' : State}
    (hex : execInstWithSvc (evalSvc (P pl ex).svc) i (mkS s0 pc r sp ps m v) = s') :
    Steps (P pl ex) S0 s' := by
  have := Step.exec (prog := P pl ex) (s := mkS s0 pc r sp ps m v) hrun hf
  rw [Program.evalInst, hex] at this
  exact Steps.snoc hpath this

theorem stepS' {pc' sp' : BitVec 64} {r' : BitVec 5 → BitVec 64} {ps' : PState} {m' : Memory}
    {v' : BitVec 5 → BitVec 128}
    (hpath : Steps (P pl ex) S0 (mkS s0 pc r sp ps m v)) (hrun : s0.status = .Running)
    (hf : (P pl ex).fetchMem m pc = some i)
    (hex : execInstWithSvc (evalSvc (P pl ex).svc) i (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r' sp' ps' m' v') (hpc : pc + 4#64 = pc') :
    Steps (P pl ex) S0 (mkS s0 pc' r' sp' ps' m' v') := by
  subst hpc; exact stepS hpath hrun hf hex

theorem stepN {pc' : BitVec 64} {d : BitVec 5} {val : BitVec 64}
    (hpath : Steps (P pl ex) S0 (mkS s0 pc r sp ps m v)) (hrun : s0.status = .Running)
    (hf : (P pl ex).fetchMem m pc = some i)
    (hex : execInstWithSvc (evalSvc (P pl ex).svc) i (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d val) sp ps m v) (hpc : pc + 4#64 = pc') :
    ∃ x, x = val ∧ Steps (P pl ex) S0 (mkS s0 pc' (upd r d x) sp ps m v) := by
  subst hpc; exact ⟨val, rfl, stepS hpath hrun hf hex⟩

end

end Poly1305Debian.FD

end
end

section
section
/-! # `toNat` of the operations used by `poly1305_finish`'s reduction -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64

theorem n_add (a b : BitVec 64) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := BitVec.toNat_add a b

theorem n_lsr (x : BitVec 64) (k : Nat) (hk : k < 64) :
    (shift64 x .LSR k).toNat = x.toNat / 2 ^ k := by
  simp [shift64, Nat.mod_eq_of_lt hk, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem n_lsl0 (x : BitVec 64) : shift64 x .LSL 0 = x := by simp [shift64]

theorem n_and44 (x : BitVec 64) : (x &&& 17592186044415#64).toNat = x.toNat % 2 ^ 44 := by
  rw [BitVec.toNat_and, show (17592186044415#64 : BitVec 64).toNat = 2 ^ 44 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem n_and42 (x : BitVec 64) : (x &&& 4398046511103#64).toNat = x.toNat % 2 ^ 42 := by
  rw [BitVec.toNat_and, show (4398046511103#64 : BitVec 64).toNat = 2 ^ 42 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem bf_uu : (BitfieldOp.UBFM == BitfieldOp.UBFM) = true := rfl

theorem n_ubfm (d s : BitVec 64) (k : Nat) (hk : k < 64) :
    (evalBitfield .W64 .UBFM d s k 63).toNat = s.toNat / 2 ^ k := by
  simp [evalBitfield, bf_uu, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]

theorem n_extr (a b : BitVec 64) :
    (BitVec.truncate 64 ((a ++ b) >>> (44 % 64))).toNat = (a.toNat * 2 ^ 64 + b.toNat) / 2 ^ 44 % 2 ^ 64 := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_append, Nat.reduceMod]
  rw [← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

theorem or_disj (x y : BitVec 64) (k z : Nat) (hx : x.toNat < 2 ^ k) (hy : y.toNat = z * 2 ^ k) :
    (x ||| y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_or, hy, ← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx,
    Nat.add_comm]

end Poly1305Debian.FD

end
end

section
section
/-! # The reduction of `poly1305_finish` (offsets 0x70..0x11c) computes `(h mod p + pad) mod 2^128`

The hypotheses `e1`..`e44` are the values the straight-line code computes, as the symbolic run
names them; `H0 H1 H2` are the accumulator limbs, `T0 T1` the two words of `pad`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Poly1305Boringssl

theorem sshr63 (x : BitVec 64) :
    (x.sshiftRight 63).toNat = if 2 ^ 63 ≤ x.toNat then 2 ^ 64 - 1 else 0 := by
  have e : x.sshiftRight 63 = if x.msb then BitVec.allOnes 64 else 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
    cases h : x.getLsbD 63 <;> (interval_cases i <;> simp [h] <;> simpa using h)
  rw [e]
  by_cases h : 2 ^ 63 ≤ x.toNat
  · have hm : x.msb = true := by rw [BitVec.msb_eq_decide]; simpa using h
    rw [if_pos hm, if_pos h]; rfl
  · have hm : x.msb = false := by rw [BitVec.msb_eq_decide]; simpa using h
    rw [if_neg (by simp [hm]), if_neg h]; rfl

theorem and_full (x y : BitVec 64) (hy : y.toNat = 2 ^ 64 - 1) : (y &&& x).toNat = x.toNat := by
  rw [BitVec.toNat_and, hy, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt x.isLt]

theorem and_zero' (x y : BitVec 64) (hy : y.toNat = 0) : (y &&& x).toNat = 0 := by
  rw [BitVec.toNat_and, hy, Nat.zero_and]

theorem or_zero_r (x y : BitVec 64) (hy : y.toNat = 0) : (x ||| y).toNat = x.toNat := by
  rw [BitVec.toNat_or, hy, Nat.or_zero]

theorem or_zero_l (x y : BitVec 64) (hx : x.toNat = 0) : (x ||| y).toNat = y.toNat := by
  rw [BitVec.toNat_or, hx, Nat.zero_or]

theorem mid_nat (T0 T1 : Nat) (ht0 : T0 < 2 ^ 64) :
    (T1 * 2 ^ 64 + T0) / 2 ^ 44 % 2 ^ 64 % 2 ^ 44 = T0 / 2 ^ 44 + 2 ^ 20 * (T1 % 2 ^ 24) := by
  have e : (T1 * 2 ^ 64 + T0) / 2 ^ 44 = T1 * 2 ^ 20 + T0 / 2 ^ 44 := by omega
  rw [e]; omega

theorem pack_nat (s0 s1 s2 T0 T1 : Nat) (h0 : s0 < 2 ^ 45) (h1 : s1 < 2 ^ 45)
    (ht0 : T0 < 2 ^ 64) (ht1 : T1 < 2 ^ 64) :
    (s0 + T0 % 2 ^ 44) % 2 ^ 44 +
      (s1 + (T1 * 2 ^ 64 + T0) / 2 ^ 44 % 2 ^ 64 % 2 ^ 44 + (s0 + T0 % 2 ^ 44) / 2 ^ 44) % 2 ^ 20 * 2 ^ 44 +
      2 ^ 64 * ((s1 + (T1 * 2 ^ 64 + T0) / 2 ^ 44 % 2 ^ 64 % 2 ^ 44 + (s0 + T0 % 2 ^ 44) / 2 ^ 44) / 2 ^ 20 % 2 ^ 24 +
        (s2 + T1 / 2 ^ 24 + (s1 + (T1 * 2 ^ 64 + T0) / 2 ^ 44 % 2 ^ 64 % 2 ^ 44 + (s0 + T0 % 2 ^ 44) / 2 ^ 44) / 2 ^ 44) % 2 ^ 40 * 2 ^ 24) =
    (s0 + 2 ^ 44 * s1 + 2 ^ 88 * s2 + (T0 + 2 ^ 64 * T1)) % 2 ^ 128 := by
  rw [mid_nat T0 T1 ht0]
  generalize hr0 : (s0 + T0 % 2 ^ 44) % 2 ^ 44 = r0
  generalize hc0 : (s0 + T0 % 2 ^ 44) / 2 ^ 44 = c0
  have e0 : s0 + T0 % 2 ^ 44 = r0 + 2 ^ 44 * c0 := by omega
  have hr0' : r0 < 2 ^ 44 := by omega
  generalize hB : s1 + (T0 / 2 ^ 44 + 2 ^ 20 * (T1 % 2 ^ 24)) + c0 = B
  generalize hC : s2 + T1 / 2 ^ 24 + B / 2 ^ 44 = C
  have eT0 : T0 = T0 % 2 ^ 44 + 2 ^ 44 * (T0 / 2 ^ 44) := by omega
  have eT1 : T1 = T1 % 2 ^ 24 + 2 ^ 24 * (T1 / 2 ^ 24) := by omega
  have eB : B = B % 2 ^ 20 + 2 ^ 20 * (B / 2 ^ 20 % 2 ^ 24) + 2 ^ 44 * (B / 2 ^ 44) := by omega
  have eC : C = C % 2 ^ 40 + 2 ^ 40 * (C / 2 ^ 40) := by omega
  have hY : s0 + 2 ^ 44 * s1 + 2 ^ 88 * s2 + (T0 + 2 ^ 64 * T1) =
      r0 + 2 ^ 44 * (B % 2 ^ 20) + 2 ^ 64 * (B / 2 ^ 20 % 2 ^ 24) + 2 ^ 88 * (C % 2 ^ 40) +
        2 ^ 128 * (C / 2 ^ 40) := by
    omega
  rw [hY]
  have hlow : r0 + 2 ^ 44 * (B % 2 ^ 20) + 2 ^ 64 * (B / 2 ^ 20 % 2 ^ 24) + 2 ^ 88 * (C % 2 ^ 40) < 2 ^ 128 := by
    omega
  omega

theorem carry_nat (H0 H1 H2 x1 x2 x3 x4 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 : Nat)
    (b0 : H0 < 2 ^ 44) (b1 : H1 < 2 ^ 44 + 64) (b2 : H2 < 2 ^ 42)
    (n1 : x1 = H2 + H1 / 2 ^ 44) (n2 : x2 = H1 % 2 ^ 44) (n3 : x3 = x1 / 2 ^ 42)
    (n4 : x4 = x1 % 2 ^ 42) (n6 : x6 = 5 * x3 + H0) (n7 : x7 = x2 + x6 / 2 ^ 44)
    (n8 : x8 = x6 % 2 ^ 44) (n9 : x9 = x4 + x7 / 2 ^ 44) (n10 : x10 = x7 % 2 ^ 44)
    (n11 : x11 = x9 / 2 ^ 42) (n12 : x12 = x9 % 2 ^ 42) (n14 : x14 = 5 * x11 + x8)
    (n15 : x15 = x14 % 2 ^ 44) (n16 : x16 = x10 + x14 / 2 ^ 44) :
    H0 + 2 ^ 44 * H1 + 2 ^ 88 * H2 = x15 + 2 ^ 44 * x16 + 2 ^ 88 * x12 + (2 ^ 130 - 5) * (x3 + x11) ∧
      x15 < 2 ^ 44 ∧ x16 ≤ 2 ^ 44 ∧ x12 < 2 ^ 42 ∧ x9 = x12 + 2 ^ 42 * x11 ∧ x11 ≤ 1 := by
  have c1 : H1 = x2 + 2 ^ 44 * (H1 / 2 ^ 44) := by omega
  have c1b : H1 / 2 ^ 44 ≤ 1 := by omega
  have c3 : x1 = x4 + 2 ^ 42 * x3 := by omega
  have c3b : x3 ≤ 1 := by omega
  have c6 : x6 = x8 + 2 ^ 44 * (x6 / 2 ^ 44) := by omega
  have c6b : x6 / 2 ^ 44 ≤ 1 := by omega
  have c7 : x7 = x10 + 2 ^ 44 * (x7 / 2 ^ 44) := by omega
  have c7b : x7 / 2 ^ 44 ≤ 1 := by omega
  have c9 : x9 = x12 + 2 ^ 42 * x11 := by omega
  have c9b : x11 ≤ 1 := by omega
  have c14 : x14 = x15 + 2 ^ 44 * (x14 / 2 ^ 44) := by omega
  have c14b : x14 / 2 ^ 44 ≤ 1 := by omega
  refine ⟨?_, by omega, by omega, by omega, c9, c9b⟩
  generalize H1 / 2 ^ 44 = q1 at *
  generalize x6 / 2 ^ 44 = q6 at *
  generalize x7 / 2 ^ 44 = q7 at *
  generalize x14 / 2 ^ 44 = q14 at *
  subst n1 n6 n9 n14 n16
  omega

theorem pack_nat2 (s0 s1 s2 T0 T1 y31 y34 y35 y37 y38 y39 y40 y41 : Nat)
    (h0 : s0 < 2 ^ 45) (h1 : s1 < 2 ^ 45) (ht0 : T0 < 2 ^ 64) (ht1 : T1 < 2 ^ 64)
    (n31 : y31 = (T1 * 2 ^ 64 + T0) / 2 ^ 44 % 2 ^ 64) (n34 : y34 = T0 % 2 ^ 44)
    (n35 : y35 = y31 % 2 ^ 44) (n37 : y37 = s0 + y34) (n38 : y38 = s1 + y35)
    (n39 : y39 = s2 + T1 / 2 ^ 24) (n40 : y40 = y38 + y37 / 2 ^ 44) (n41 : y41 = y39 + y40 / 2 ^ 44) :
    y37 % 2 ^ 44 + y40 % 2 ^ 20 * 2 ^ 44 + 2 ^ 64 * (y40 / 2 ^ 20 % 2 ^ 24 + y41 % 2 ^ 40 * 2 ^ 24) =
      (s0 + 2 ^ 44 * s1 + 2 ^ 88 * s2 + (T0 + 2 ^ 64 * T1)) % 2 ^ 128 := by
  subst n41 n40 n39 n38 n37 n35 n34 n31
  exact pack_nat s0 s1 s2 T0 T1 h0 h1 ht0 ht1

end Poly1305Debian.FD

end
end

section
section
/-! # Step lemmas for the instruction shapes GCC adds in Debian's `poly1305_finish` -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Arm64 Arm64.Obj

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_hint (imm : BitVec 7) :
    execInstWithSvc svc (.hint imm) (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) r sp ps m v := by
  simp [execInstWithSvc]

theorem ex_movz64 (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 16) :
    execInstWithSvc svc (.moveWide .W64 .MOVZ (.gpr d) imm 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (imm.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, State.writeReg, hd]

theorem ex_sub_shift (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .SUB (.gpr d) (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n - r k)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, shiftVal, shift64, awc_sub, hd,
    hn, hk]

theorem ex_cmp_reg (n k : BitVec 5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .SUBS .xzr (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp (AddWithCarry64 (r n) (~~~(r k)) true).2 m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, shiftVal, shift64, hn, hk]

theorem ex_orr_imm (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm .W64 .ORR (.gpr d) (.gpr n) mask) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n ||| mask)) sp ps m v := by
  simp [execInstWithSvc, evalLogical, State.readReg, State.writeReg, hd, hn]

theorem ex_umaddl (d n k a : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (ha : a ≠ 31#5) :
    execInstWithSvc svc (.dataProc3 .W64 .UMADDL (.gpr d) (.gpr n) (.gpr k) (.gpr a))
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64)
        (upd r d (r a + ((r n).truncate 32).zeroExtend 64 * ((r k).truncate 32).zeroExtend 64))
        sp ps m v := by
  simp [execInstWithSvc, State.readReg, State.readReg32, State.writeReg, hd, hn, hk, ha]

theorem ex_csetm (d : BitVec 5) (hd : d ≠ 31#5) (c : CondCode) :
    execInstWithSvc svc (.condSelect .W64 .CSINV (.gpr d) .xzr .xzr c) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (if ConditionHolds c ps then 0#64 else ~~~0#64)) sp ps m v := by
  by_cases h : ConditionHolds c ps <;> simp [execInstWithSvc, State.readReg, State.writeReg, hd, h]

end exec

theorem lt_cmp_zero (x : BitVec 64) :
    ConditionHolds .LT (AddWithCarry64 x (~~~0#64) true).2 = x.msb := by
  simp only [ConditionHolds, AddWithCarry64]
  have e1 : BitVec.setWidth 64 (1#65 + (BitVec.setWidth 65 (~~~0#64) + BitVec.setWidth 65 x)) = x := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_setWidth]
    have := x.isLt; omega
  have e2 : 1#65 + (BitVec.signExtend 65 (~~~0#64) + BitVec.signExtend 65 x) = BitVec.signExtend 65 x := by
    have : BitVec.signExtend 65 (~~~0#64) = BitVec.allOnes 65 := by decide
    rw [this, ← BitVec.add_assoc, show 1#65 + BitVec.allOnes 65 = 0#65 by decide, BitVec.zero_add]
  simp only [if_true, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, e1, e2,
    BitVec.msb_signExtend]
  cases x.msb <;> simp

end Poly1305Debian.FD

end
end

section
section
/-! # The reduction of Debian's `poly1305_finish` (+0x74..+0x124) computes `(h mod p + pad) mod 2^128`

The hypotheses `e1`..`e43` are the values GCC's straight-line code computes, as the symbolic run in
`Join.lean` names them; `H0 H1 H2` are the accumulator limbs, `T0 T1` the two words of `pad`. The
code is the same C as the clang build, so the carry, select and pack lemmas of `Arith.lean` apply. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Poly1305Boringssl

theorem n_ze32 (x : BitVec 64) (hx : x.toNat < 2 ^ 32) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 x)).toNat = x.toNat := by
  simp [BitVec.toNat_setWidth]; omega

theorem n_umaddl5 (a x F : BitVec 64) (hF : F.toNat = 5) (hx : x.toNat < 2 ^ 32)
    (ha : a.toNat + 5 * x.toNat < 2 ^ 64) :
    (a + BitVec.zeroExtend 64 (BitVec.truncate 32 x) * BitVec.zeroExtend 64 (BitVec.truncate 32 F)).toNat =
      a.toNat + 5 * x.toNat := by
  rw [n_add, BitVec.toNat_mul, n_ze32 x hx, n_ze32 F (by omega), hF]
  have : x.toNat * 5 % 2 ^ 64 = x.toNat * 5 := Nat.mod_eq_of_lt (by omega)
  rw [this]; omega

theorem or_K (x : BitVec 64) :
    (x ||| 18446739675663040512#64).toNat = x.toNat % 2 ^ 42 + (2 ^ 64 - 2 ^ 42) := by
  have e : x ||| 18446739675663040512#64 = (x &&& 4398046511103#64) ||| 18446739675663040512#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
    interval_cases i <;> simp
  rw [e, or_disj _ _ 42 (2 ^ 22 - 1) (by rw [n_and42]; omega) (by rfl), n_and42]; rfl

theorem asr63 (x : BitVec 64) :
    (shift64 x .ASR 63).toNat = if 2 ^ 63 ≤ x.toNat then 2 ^ 64 - 1 else 0 := by
  rw [← sshr63]; simp [shift64]

theorem msb_iff (x : BitVec 64) : x.msb = decide (2 ^ 63 ≤ x.toNat) := by
  rw [BitVec.msb_eq_decide]

theorem and_full_r (x y : BitVec 64) (hy : y.toNat = 2 ^ 64 - 1) : (x &&& y).toNat = x.toNat := by
  rw [BitVec.and_comm]; exact and_full _ _ hy

theorem and_zero_r (x y : BitVec 64) (hy : y.toNat = 0) : (x &&& y).toNat = 0 := by
  rw [BitVec.and_comm]; exact and_zero' _ _ hy

theorem n_shl44 (x : BitVec 64) : (shift64 x .LSL 44).toNat = x.toNat % 2 ^ 20 * 2 ^ 44 := by
  simp only [shift64, Nat.reduceMod, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := x.isLt; omega

theorem n_shl24 (x : BitVec 64) : (shift64 x .LSL 24).toNat = x.toNat % 2 ^ 40 * 2 ^ 24 := by
  simp only [shift64, Nat.reduceMod, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := x.isLt; omega

theorem n_ubfx20 (d s : BitVec 64) :
    (evalBitfield .W64 .UBFM d s 20 43).toNat = s.toNat / 2 ^ 20 % 2 ^ 24 := by
  have e : evalBitfield .W64 .UBFM d s 20 43 = (s >>> 20) &&& 16777215#64 := by
    simp [evalBitfield, bf_uu]
  rw [e, BitVec.toNat_and, show (16777215#64 : BitVec 64).toNat = 2 ^ 24 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem sel_nat_d (a V x15 x16 x12 k x17 x18 x19 : Nat)
    (ha : a = V + (2 ^ 130 - 5) * k) (hV : V = x15 + 2 ^ 44 * x16 + 2 ^ 88 * x12)
    (b15 : x15 < 2 ^ 44) (b16 : x16 ≤ 2 ^ 44) (b12 : x12 < 2 ^ 42)
    (n17 : x17 = x15 + 5) (n18 : x18 = x16 + x17 / 2 ^ 44) (n19 : x19 = x12 + x18 / 2 ^ 44) :
    (x19 < 2 ^ 42 → a % (2 ^ 130 - 5) = x15 + 2 ^ 44 * x16 + 2 ^ 88 * x12) ∧
    (¬ x19 < 2 ^ 42 →
      a % (2 ^ 130 - 5) = x17 % 2 ^ 44 + 2 ^ 44 * (x18 % 2 ^ 44) + 2 ^ 88 * (x19 - 2 ^ 42)) := by
  have hg : x17 % 2 ^ 44 + 2 ^ 44 * (x18 % 2 ^ 44) + 2 ^ 88 * x19 = V + 5 := by omega
  constructor
  · intro hs
    have hVp : V < 2 ^ 130 - 5 := by omega
    rw [ha, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hVp, hV]
  · intro hs
    have hVp : 2 ^ 130 - 5 ≤ V := by omega
    have hV2 : V - (2 ^ 130 - 5) < 2 ^ 130 - 5 := by omega
    rw [show a = (V - (2 ^ 130 - 5)) + (2 ^ 130 - 5) * (k + 1) by rw [ha]; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hV2]
    omega

theorem fin_arith_d (H0 H1 H2 T0 T1 F5 : BitVec 64)
    (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25
      w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 : BitVec 64)
    (eF5 : F5 = BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 5#16)))
    (b0 : H0.toNat < 2 ^ 44) (b1 : H1.toNat < 2 ^ 44 + 64) (b2 : H2.toNat < 2 ^ 42)
    (e1 : w1 = H1 &&& 17592186044415#64)
    (e2 : w2 = H2 + shift64 H1 .LSR 44)
    (e3 : w3 = w2 &&& 4398046511103#64)
    (e4 : w4 = evalBitfield .W64 .UBFM w2 w2 42 63)
    (e5 : w5 = H0 + BitVec.zeroExtend 64 (BitVec.truncate 32 w4) * BitVec.zeroExtend 64 (BitVec.truncate 32 F5))
    (e6 : w6 = w5 &&& 17592186044415#64)
    (e7 : w7 = w1 + shift64 w5 .LSR 44)
    (e8 : w8 = w7 &&& 17592186044415#64)
    (e9 : w9 = w3 + shift64 w7 .LSR 44)
    (e10 : w10 = w9 &&& 4398046511103#64)
    (e11 : w11 = evalBitfield .W64 .UBFM w3 w9 42 63)
    (e12 : w12 = w9 ||| 18446739675663040512#64)
    (e13 : w13 = w6 + BitVec.zeroExtend 64 (BitVec.truncate 32 w11) * BitVec.zeroExtend 64 (BitVec.truncate 32 F5))
    (e14 : w14 = BitVec.zeroExtend 64 0#16)
    (e15 : w15 = w13 &&& 17592186044415#64)
    (e16 : w16 = w8 + shift64 w13 .LSR 44)
    (e17 : w17 = w15 + BitVec.zeroExtend 64 5#12)
    (e18 : w18 = w16 + shift64 w17 .LSR 44)
    (e19 : w19 = w12 + shift64 w18 .LSR 44)
    (e20 : w20 = if ConditionHolds .LT (AddWithCarry64 w19 (~~~w14) true).2 = true then 0#64 else ~~~0#64)
    (e21 : w21 = w15 &&& shift64 w19 .ASR 63)
    (e22 : w22 = w17 &&& shift64 w20 .LSL 0)
    (e23 : w23 = w18 &&& shift64 w20 .LSL 0)
    (e24 : w24 = w22 &&& 17592186044415#64)
    (e25 : w25 = w24 ||| shift64 w21 .LSL 0)
    (e26 : w26 = w16 &&& shift64 w19 .ASR 63)
    (e27 : w27 = w23 &&& 17592186044415#64)
    (e28 : w28 = T0 &&& 17592186044415#64)
    (e29 : w29 = w28 + shift64 w25 .LSL 0)
    (e30 : w30 = BitVec.truncate 64 ((T1 ++ T0) >>> (44 % 64)))
    (e31 : w31 = w27 ||| shift64 w26 .LSL 0)
    (e32 : w32 = w30 &&& 17592186044415#64)
    (e33 : w33 = w10 &&& shift64 w19 .ASR 63)
    (e34 : w34 = w32 + shift64 w31 .LSL 0)
    (e35 : w35 = w19 &&& shift64 w20 .LSL 0)
    (e36 : w36 = w29 &&& 17592186044415#64)
    (e37 : w37 = w35 ||| shift64 w33 .LSL 0)
    (e38 : w38 = w34 + shift64 w29 .LSR 44)
    (e39 : w39 = w37 + shift64 T1 .LSR 24)
    (e40 : w40 = w39 + shift64 w38 .LSR 44)
    (e41 : w41 = evalBitfield .W64 .UBFM w34 w38 20 43)
    (e42 : w42 = w36 ||| shift64 w38 .LSL 44)
    (e43 : w43 = w41 ||| shift64 w40 .LSL 24) :
    w42.toNat + 2 ^ 64 * w43.toNat =
      ((H0.toNat + 2 ^ 44 * H1.toNat + 2 ^ 88 * H2.toNat) % p1305 + (T0.toNat + 2 ^ 64 * T1.toNat))
        % 2 ^ 128 := by
  simp only [n_lsl0] at *
  have hF : F5.toNat = 5 := by rw [eF5]; rfl
  have h0 := H0.isLt; have h1 := H1.isLt; have h2 := H2.isLt; have t0 := T0.isLt; have t1 := T1.isLt
  have i5 := w5.isLt; have i7 := w7.isLt; have i13 := w13.isLt; have i17 := w17.isLt
  have i18 := w18.isLt; have i19 := w19.isLt; have i29 := w29.isLt; have i38 := w38.isLt
  -- first carry pass
  have n1 : w1.toNat = H1.toNat % 2 ^ 44 := by rw [e1, n_and44]
  have n2 : w2.toNat = H2.toNat + H1.toNat / 2 ^ 44 := by
    rw [e2, n_add, n_lsr _ _ (by decide)]; clear * - b2 h1; omega
  have n3 : w3.toNat = w2.toNat % 2 ^ 42 := by rw [e3, n_and42]
  have n4 : w4.toNat = w2.toNat / 2 ^ 42 := by rw [e4, n_ubfm _ _ _ (by decide)]
  have n5 : w5.toNat = H0.toNat + 5 * w4.toNat := by
    rw [e5, n_umaddl5 _ _ _ hF (by clear * - n4 n2 b2 h1; omega) (by clear * - n4 n2 b2 h1 b0; omega)]
  have n6 : w6.toNat = w5.toNat % 2 ^ 44 := by rw [e6, n_and44]
  have n7 : w7.toNat = w1.toNat + w5.toNat / 2 ^ 44 := by
    rw [e7, n_add, n_lsr _ _ (by decide)]; clear * - n1 i5; omega
  have n8 : w8.toNat = w7.toNat % 2 ^ 44 := by rw [e8, n_and44]
  have n9 : w9.toNat = w3.toNat + w7.toNat / 2 ^ 44 := by
    rw [e9, n_add, n_lsr _ _ (by decide)]; clear * - n3 i7; omega
  have n10 : w10.toNat = w9.toNat % 2 ^ 42 := by rw [e10, n_and42]
  -- second carry pass
  have n11 : w11.toNat = w9.toNat / 2 ^ 42 := by rw [e11, n_ubfm _ _ _ (by decide)]
  have n12 : w12.toNat = w10.toNat + (2 ^ 64 - 2 ^ 42) := by rw [e12, or_K, n10]
  have n13 : w13.toNat = w6.toNat + 5 * w11.toNat := by
    rw [e13, n_umaddl5 _ _ _ hF (by clear * - n11 n9 n3 i7; omega) (by clear * - n11 n9 n3 i7 n6; omega)]
  have n15 : w15.toNat = w13.toNat % 2 ^ 44 := by rw [e15, n_and44]
  have n16 : w16.toNat = w8.toNat + w13.toNat / 2 ^ 44 := by
    rw [e16, n_add, n_lsr _ _ (by decide)]; clear * - n8 i13; omega
  -- g = h + 5 - 2^130
  have n17 : w17.toNat = w15.toNat + 5 := by rw [e17, n_add]; simp; clear * - n15; omega
  have n18 : w18.toNat = w16.toNat + w17.toNat / 2 ^ 44 := by
    rw [e18, n_add, n_lsr _ _ (by decide)]; clear * - n16 n8 i13 i17; omega
  obtain ⟨hc, b15, b16, b12, h9, b11⟩ := carry_nat H0.toNat H1.toNat H2.toNat w2.toNat w1.toNat
    w4.toNat w3.toNat w5.toNat w7.toNat w6.toNat w9.toNat w8.toNat w11.toNat w10.toNat w13.toNat
    w15.toNat w16.toNat b0 b1 b2 n2 n1 n4 n3 (by clear * - n5; omega) n7 n6 n9 n8 n11 n10
    (by clear * - n13; omega) n15 n16
  generalize hy : w10.toNat + w18.toNat / 2 ^ 44 = y19
  have n19 : w19.toNat = (y19 + (2 ^ 64 - 2 ^ 42)) % 2 ^ 64 := by
    rw [e19, n_add, n_lsr _ _ (by decide), n12]; clear * - hy; omega
  have hy19 : y19 ≤ 2 ^ 42 := by clear * - hy b12 n18 b16 n17 b15; omega
  have hsel := sel_nat_d _ _ w15.toNat w16.toNat w10.toNat _ w17.toNat w18.toNat y19 hc rfl b15 b16
    b12 n17 n18 hy.symm
  have h14 : w14 = 0#64 := by rw [e14]; rfl
  rw [h14, lt_cmp_zero, msb_iff] at e20
  -- pad
  have n28 : w28.toNat = T0.toNat % 2 ^ 44 := by rw [e28, n_and44]
  have n30 : w30.toNat = (T1.toNat * 2 ^ 64 + T0.toNat) / 2 ^ 44 % 2 ^ 64 := by rw [e30, n_extr]
  have n32 : w32.toNat = w30.toNat % 2 ^ 44 := by rw [e32, n_and44]
  have n36 : w36.toNat = w29.toNat % 2 ^ 44 := by rw [e36, n_and44]
  have n42 : w42.toNat = w29.toNat % 2 ^ 44 + w38.toNat % 2 ^ 20 * 2 ^ 44 := by
    rw [e42, or_disj _ _ 44 (w38.toNat % 2 ^ 20) (by rw [n36]; omega) (n_shl44 _), n36, n_shl44]
  have n41 : w41.toNat = w38.toNat / 2 ^ 20 % 2 ^ 24 := by rw [e41, n_ubfx20]
  have n43 : w43.toNat = w38.toNat / 2 ^ 20 % 2 ^ 24 + w40.toNat % 2 ^ 40 * 2 ^ 24 := by
    rw [e43, or_disj _ _ 24 (w40.toNat % 2 ^ 40) (by rw [n41]; omega) (n_shl24 _), n41, n_shl24]
  have hp : p1305 = 2 ^ 130 - 5 := rfl
  rw [hp, n42, n43]
  generalize (H0.toNat + 2 ^ 44 * H1.toNat + 2 ^ 88 * H2.toNat) % (2 ^ 130 - 5) = ap at hsel ⊢
  by_cases hs : y19 < 2 ^ 42
  · -- h < p: keep h
    have hap := hsel.1 hs
    have mneg : 2 ^ 63 ≤ w19.toNat := by rw [n19]; clear * - hs; omega
    have m19 : (shift64 w19 .ASR 63).toNat = 2 ^ 64 - 1 := by rw [asr63, if_pos mneg]
    have m20 : w20.toNat = 0 := by
      rw [e20]; simp only [decide_eq_true_eq]; rw [if_pos mneg]; rfl
    have n22 : w22.toNat = 0 := by rw [e22, and_zero_r _ _ m20]
    have n23 : w23.toNat = 0 := by rw [e23, and_zero_r _ _ m20]
    have n24 : w24.toNat = 0 := by rw [e24, and_zero' _ _ n22]
    have n27 : w27.toNat = 0 := by rw [e27, and_zero' _ _ n23]
    have n21 : w21.toNat = w15.toNat := by rw [e21, and_full_r _ _ m19]
    have n26 : w26.toNat = w16.toNat := by rw [e26, and_full_r _ _ m19]
    have n33 : w33.toNat = w10.toNat := by rw [e33, and_full_r _ _ m19]
    have n35 : w35.toNat = 0 := by rw [e35, and_zero_r _ _ m20]
    have n25 : w25.toNat = w15.toNat := by rw [e25, or_zero_l _ _ n24, n21]
    have n31 : w31.toNat = w16.toNat := by rw [e31, or_zero_l _ _ n27, n26]
    have n37 : w37.toNat = w10.toNat := by rw [e37, or_zero_l _ _ n35, n33]
    have n29 : w29.toNat = w15.toNat + w28.toNat := by rw [e29, n_add]; clear * - n25 n28 b15; omega
    have n34 : w34.toNat = w16.toNat + w32.toNat := by rw [e34, n_add]; clear * - n31 n32 b16; omega
    have n38 : w38.toNat = w34.toNat + w29.toNat / 2 ^ 44 := by
      rw [e38, n_add, n_lsr _ _ (by decide)]; clear * - n34 n32 b16 i29; omega
    have n39 : w39.toNat = w10.toNat + T1.toNat / 2 ^ 24 := by
      rw [e39, n_add, n_lsr _ _ (by decide), n37]; clear * - b12 t1; omega
    have n40 : w40.toNat = w39.toNat + w38.toNat / 2 ^ 44 := by
      rw [e40, n_add, n_lsr _ _ (by decide)]; clear * - n39 b12 t1 i38; omega
    have P := pack_nat2 w15.toNat w16.toNat w10.toNat T0.toNat T1.toNat w30.toNat w28.toNat
      w32.toNat w29.toNat w34.toNat w39.toNat w38.toNat w40.toNat (by clear * - b15; omega)
      (by clear * - b16; omega) t0 t1 n30 n28 n32 (by clear * - n29; omega)
      (by clear * - n34; omega) n39 n38 n40
    have hP : w29.toNat % 2 ^ 44 + w38.toNat % 2 ^ 20 * 2 ^ 44 +
        2 ^ 64 * (w38.toNat / 2 ^ 20 % 2 ^ 24 + w40.toNat % 2 ^ 40 * 2 ^ 24) =
        (ap + (T0.toNat + 2 ^ 64 * T1.toNat)) % 2 ^ 128 := by rw [P, hap]
    clear * - hP; omega
  · -- h ≥ p: take g
    have hap := hsel.2 hs
    have mpos : ¬ 2 ^ 63 ≤ w19.toNat := by rw [n19]; clear * - hs hy19; omega
    have v19 : w19.toNat = y19 - 2 ^ 42 := by rw [n19]; clear * - hs hy19; omega
    have m19 : (shift64 w19 .ASR 63).toNat = 0 := by rw [asr63, if_neg mpos]
    have m20 : w20.toNat = 2 ^ 64 - 1 := by
      rw [e20]; simp only [decide_eq_true_eq]; rw [if_neg mpos]; rfl
    have n22 : w22.toNat = w17.toNat := by rw [e22, and_full_r _ _ m20]
    have n23 : w23.toNat = w18.toNat := by rw [e23, and_full_r _ _ m20]
    have n24 : w24.toNat = w17.toNat % 2 ^ 44 := by rw [e24, n_and44, n22]
    have n27 : w27.toNat = w18.toNat % 2 ^ 44 := by rw [e27, n_and44, n23]
    have n21 : w21.toNat = 0 := by rw [e21, and_zero_r _ _ m19]
    have n26 : w26.toNat = 0 := by rw [e26, and_zero_r _ _ m19]
    have n33 : w33.toNat = 0 := by rw [e33, and_zero_r _ _ m19]
    have n35 : w35.toNat = w19.toNat := by rw [e35, and_full_r _ _ m20]
    have n25 : w25.toNat = w17.toNat % 2 ^ 44 := by rw [e25, or_zero_r _ _ n21, n24]
    have n31 : w31.toNat = w18.toNat % 2 ^ 44 := by rw [e31, or_zero_r _ _ n26, n27]
    have n37 : w37.toNat = w19.toNat := by rw [e37, or_zero_r _ _ n33, n35]
    have n29 : w29.toNat = w17.toNat % 2 ^ 44 + w28.toNat := by
      rw [e29, n_add]; clear * - n25 n28; omega
    have n34 : w34.toNat = w18.toNat % 2 ^ 44 + w32.toNat := by
      rw [e34, n_add]; clear * - n31 n32; omega
    have n38 : w38.toNat = w34.toNat + w29.toNat / 2 ^ 44 := by
      rw [e38, n_add, n_lsr _ _ (by decide)]; clear * - n34 n32 i29; omega
    have n39 : w39.toNat = w19.toNat + T1.toNat / 2 ^ 24 := by
      rw [e39, n_add, n_lsr _ _ (by decide), n37]; clear * - v19 hy19 t1; omega
    have n40 : w40.toNat = w39.toNat + w38.toNat / 2 ^ 44 := by
      rw [e40, n_add, n_lsr _ _ (by decide)]; clear * - n39 v19 hy19 t1 i38; omega
    have P := pack_nat2 (w17.toNat % 2 ^ 44) (w18.toNat % 2 ^ 44) w19.toNat T0.toNat T1.toNat
      w30.toNat w28.toNat w32.toNat w29.toNat w34.toNat w39.toNat w38.toNat w40.toNat (by omega)
      (by omega) t0 t1 n30 n28 n32 (by clear * - n29; omega) (by clear * - n34; omega) n39 n38 n40
    have hP : w29.toNat % 2 ^ 44 + w38.toNat % 2 ^ 20 * 2 ^ 44 +
        2 ^ 64 * (w38.toNat / 2 ^ 20 % 2 ^ 24 + w40.toNat % 2 ^ 40 * 2 ^ 24) =
        (ap + (T0.toNat + 2 ^ 64 * T1.toNat)) % 2 ^ 128 := by rw [P, hap, v19]
    clear * - hP; omega

end Poly1305Debian.FD

end
end

section
section
/-! # The 16 tag bytes -/

set_option autoImplicit false

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Poly1305Boringssl

theorem numTo16_mod (n : Nat) : numTo16LeBytes (n % 2 ^ 128) = numTo16LeBytes n := by
  unfold numTo16LeBytes
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  interval_cases i <;> omega

theorem extract_toNat (x : BitVec 64) (k : Nat) : (x.extractLsb' k 8).toNat = x.toNat / 2 ^ k % 2 ^ 8 := by
  simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

theorem unpack_tag (a b : BitVec 64) :
    unpack64 a ++ unpack64 b = numTo16LeBytes (a.toNat + 2 ^ 64 * b.toNat) := by
  have ha := a.isLt; have hb := b.isLt
  apply List.ext_getElem (by simp [numTo16LeBytes])
  intro i h1 h2
  have hi : i < 16 := by simpa using h1
  simp only [numTo16LeBytes, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  interval_cases i <;> simp [unpack64, extract_toNat] <;> omega

end Poly1305Debian.FD

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Poly1305Boringssl

theorem leBytes_append (a b : List (BitVec 8)) :
    leBytesToNum (a ++ b) = leBytesToNum a + 256 ^ a.length * leBytesToNum b := by
  induction a with
  | nil => simp [leBytesToNum]
  | cons x xs ih =>
    simp only [List.cons_append, leBytesToNum, List.foldr_cons, List.length_cons] at ih ⊢
    rw [ih, Nat.pow_succ]; ring

theorem leBytes_take16 (l : List (BitVec 8)) (h : 16 ≤ l.length) :
    leBytesToNum (l.take 16) = u64At l 0 + 2 ^ 64 * u64At l 8 := by
  rw [show 16 = 8 + 8 from rfl, List.take_add, leBytes_append]
  simp only [u64At, List.drop_zero, List.length_take]
  rw [show min 8 l.length = 8 by omega]; rfl

theorem stk_u64 (a b c d : BitVec 64) :
    u64At (unpack64 a ++ unpack64 b ++ unpack64 c ++ unpack64 d) 0 = a.toNat ∧
    u64At (unpack64 a ++ unpack64 b ++ unpack64 c ++ unpack64 d) 8 = b.toNat ∧
    u64At (unpack64 a ++ unpack64 b ++ unpack64 c ++ unpack64 d) 16 = c.toNat ∧
    u64At (unpack64 a ++ unpack64 b ++ unpack64 c ++ unpack64 d) 24 = d.toNat := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [u64At, unpack64, leBytesToNum, extract_toNat] <;> omega

end Poly1305Debian.FD

end
end

section
section
/-! # The tail call: `sodium_memzero`'s hook zeroes the state and returns to the caller -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj Poly1305Boringssl

theorem not_sat_false' {m : Memory} {R : SepProp} : ¬ (m ⊨ (⌜False⌝ : SepProp) ∗ R) := by
  rw [sat_pure_sep]; exact fun h => h.1

theorem tail_hook {pl : Placement} {ex : String → Option (State → State)} {S0 s0 : State}
    {rf : BitVec 5 → BitVec 64} {ps : PState} {m2 : Memory} {v : BitVec 5 → BitVec 128}
    {A M SP : BitVec 64} {R : SepProp} {rh mid rest stk st mac : List (BitVec 8)}
    {f : State → State}
    (hrun : s0.status = .Running)
    (g : Steps (P pl ex) S0 (mkS s0 (pl.ρ "sodium_memzero") rf SP ps m2 v))
    (h0 : rf 0#5 = A) (h1 : (rf 1#5).toNat = 96)
    (h19 : rf 19#5 = S0.readReg64 (.gpr 19#5)) (h20 : rf 20#5 = S0.readReg64 (.gpr 20#5))
    (h29 : rf 29#5 = S0.readReg64 (.gpr 29#5)) (h30 : rf 30#5 = S0.readReg64 (.gpr 30#5))
    (hcs : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat ≤ 28 → rf k = S0.readReg64 (.gpr k))
    (hvr : VRegFile.calleeSaved ⟨v⟩ = calleeSavedVRegs S0)
    (hA : S0.readReg64 .x0 = A) (hM : S0.readReg64 .x1 = M) (hSP : S0.sp = SP)
    (halS : SP &&& 0b1111#64 = 0#64)
    (hl : rh.length = 48 ∧ mid.length = 24 ∧ rest.length = 24 ∧ stk.length = 32)
    (hs : m2 ⊨ (A ↦ₛ rh) ∗ ((A + 48#64) ↦ₛ mid) ∗ ((A + 72#64) ↦ₛ rest) ∗ (M ↦ₛ finishTag st) ∗
      ((SP - 32#64) ↦ₛ stk) ∗ memRegion (SP - 4128#64) 4096 ∗ R)
    (hf : HookOk f Libc.explicitBzeroSpec)
    (hat : (P pl ex).externAt? (pl.ρ "sodium_memzero") = some f) :
    ∃ sf, Steps (P pl ex) S0 sf ∧ SubroutineOutcome finishSpec (st, mac) R S0 sf := by
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hl
  have hs0 : m2 ⊨ memRegion (SP - 4128#64) (32 + 4064) ∗ ((A ↦ₛ rh) ∗ ((A + 48#64) ↦ₛ mid) ∗
      ((A + 72#64) ↦ₛ rest) ∗ (M ↦ₛ finishTag st) ∗ ((SP - 32#64) ↦ₛ stk) ∗ R) :=
    Satisfies.of_eq hs (by ac_rfl)
  have hs00 := sat_sep_mono hs0 (memRegion_split (SP - 4128#64) 32 4064 (by decide))
  rw [show SP - 4128#64 + BitVec.ofNat 64 32 = SP - 4096#64 by bv_omega] at hs00
  have hs : m2 ⊨ (A ↦ₛ rh) ∗ ((A + 48#64) ↦ₛ mid) ∗ ((A + 72#64) ↦ₛ rest) ∗
      (M ↦ₛ finishTag st) ∗ ((SP - 32#64) ↦ₛ stk) ∗ memRegion (SP - 4096#64) 4064 ∗
      (memRegion (SP - 4128#64) 32 ∗ R) := Satisfies.of_eq hs00 (by ac_rfl)
  generalize hsh : mkS s0 (pl.ρ "sodium_memzero") rf SP ps m2 v = sh at g
  have hshp : sh.pc = pl.ρ "sodium_memzero" := by rw [← hsh]; rfl
  have hshs : sh.status = .Running := by rw [← hsh]; exact hrun
  have hshsp : sh.sp = SP := by rw [← hsh]; rfl
  have hshm : sh.mem = m2 := by rw [← hsh]; rfl
  have rd : ∀ k : BitVec 5, k ≠ 31#5 → sh.readReg64 (.gpr k) = rf k := by
    intro k hk; rw [← hsh]; simp [hk]
  have hvv : calleeSavedVRegs sh = calleeSavedVRegs S0 := by rw [← hsh]; exact hvr
  -- the hook's precondition
  have eA : (A ↦ₛ (rh ++ mid ++ rest)) = (A ↦ₛ rh) ∗ ((A + 48#64) ↦ₛ mid) ∗ ((A + 72#64) ↦ₛ rest) := by
    rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append, hl1, hl2, BitVec.add_assoc]
    rfl
  have hs1 : m2 ⊨ (A ↦ₛ (rh ++ mid ++ rest)) ∗ (((SP - 32#64) ↦ₛ stk) ∗
      memRegion (SP - 4096#64) 4064 ∗ (M ↦ₛ finishTag st) ∗ (memRegion (SP - 4128#64) 32 ∗ R)) := by
    rw [eA]; exact Satisfies.of_eq hs (by ac_rfl)
  have hs2 := sat_sep_mono hs1 (bytes_entails_memRegion A _)
  have hl96 : (rh ++ mid ++ rest).length = 96 := by simp [hl1, hl2, hl3]
  rw [hl96] at hs2
  have hs3 : m2 ⊨ (memRegion (SP - 4096#64) 4064 ∗ ((SP - 32#64) ↦ₛ stk)) ∗
      (memRegion A 96 ∗ (M ↦ₛ finishTag st) ∗ (memRegion (SP - 4128#64) 32 ∗ R)) :=
    Satisfies.of_eq hs2 (by ac_rfl)
  have hs4 := sat_sep_mono hs3 (sepConj_mono (Entails.refl _) (bytes_entails_memRegion _ stk))
  rw [hl4] at hs4
  have hs5 := sat_sep_mono hs4 (memRegion_merge (SP - 4096#64) (SP - 32#64) 4064 32
    (by bv_omega) (by decide) (by decide))
  have hpre : sh.mem ⊨ Libc.explicitBzeroSpec.pre (A, 96) sh ∗
      ((M ↦ₛ finishTag st) ∗ (memRegion (SP - 4128#64) 32 ∗ R)) := by
    simp only [Libc.explicitBzeroSpec, VerifiedLibraries.Musl.cExtern, ProofLib.stackAt,
      VerifiedLibraries.Musl.externStack]
    rw [sepConj_assoc, sat_pure_sep]
    refine ⟨⟨by rw [Reg.x0, rd 0#5 (by decide), h0], by rw [Reg.x1, rd 1#5 (by decide), h1]⟩, ?_⟩
    rw [hshsp, hshm]
    exact Satisfies.of_eq hs5 (by ac_rfl)
  have hal' : sh.spAligned = true := by rw [← hsh]; simp [halS]
  obtain ⟨hkeep, hsym, hout⟩ := hf (A, 96) _ sh hshs hpre hal'
  have gF : Steps (P pl ex) S0 (f sh) :=
    Poly1305Debian.FD.Steps.snoc g (Step.externHook hshs (by rw [hshp]; exact hat) hkeep hsym)
  refine ⟨f sh, gF, ?_⟩
  rcases hout with ⟨⟨hpc, hsp, hst⟩, ⟨_, hcsf⟩, hpost⟩ | ⟨_, hp⟩ | ⟨c, _, hp⟩ | ⟨_, hp⟩
  · refine Or.inl ⟨⟨?_, ?_, hst⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [hpc, Reg.lr, rd 30#5 (by decide), h30]
    · rw [hsp, hshsp, hSP]
    · rw [hsp, hshsp, hSP]
    · obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, cfp, cv⟩ := hcsf
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [c19, rd _ (by decide), h19]
      · rw [c20, rd _ (by decide), h20]
      · rw [c21, rd _ (by decide), hcs _ (by decide) (by decide)]
      · rw [c22, rd _ (by decide), hcs _ (by decide) (by decide)]
      · rw [c23, rd _ (by decide), hcs _ (by decide) (by decide)]
      · rw [c24, rd _ (by decide), hcs _ (by decide) (by decide)]
      · rw [c25, rd _ (by decide), hcs _ (by decide) (by decide)]
      · rw [c26, rd _ (by decide), hcs _ (by decide) (by decide)]
      · rw [c27, rd _ (by decide), hcs _ (by decide) (by decide)]
      · rw [c28, rd _ (by decide), hcs _ (by decide) (by decide)]
      · rw [cfp, Reg.fp, rd _ (by decide), h29]
      · rw [cv, hvv]
    · simp only [Libc.explicitBzeroSpec, VerifiedLibraries.Musl.cExtern, ProofLib.stackAt,
        VerifiedLibraries.Musl.externStack] at hpost
      show (f sh).mem ⊨ ((S0.readReg64 .x0 ↦ₛ List.replicate 96 0#8) ∗
        (S0.readReg64 .x1 ↦ₛ finishTag st) ∗ stackFrame S0 4128) ∗ R
      rw [hA, hM, stackFrame, hSP]
      rw [hshsp] at hpost
      have hq : (f sh).mem ⊨ (memRegion (SP - 4128#64) 32 ∗ memRegion (SP - BitVec.ofNat 64 4096) 4096) ∗
          ((A ↦ₛ List.replicate 96 0#8) ∗ (M ↦ₛ finishTag st) ∗ R) := Satisfies.of_eq hpost (by ac_rfl)
      have hq2 := sat_sep_mono hq (memRegion_merge (SP - 4128#64) (SP - BitVec.ofNat 64 4096) 32 4096
        (by bv_omega) (by decide) (by decide))
      exact Satisfies.of_eq hq2 (by ac_rfl)
  · exact absurd hp not_sat_false'
  · exact absurd hp not_sat_false'
  · exact absurd hp not_sat_false'

end Poly1305Debian.FD

end
end

section
section
/-! # From offset +0x68 of Debian's `poly1305_finish` to its return through `sodium_memzero`

`join` takes the state after the optional final block (both paths meet at +0x68) and proves the
subroutine outcome: the reduction writes `finishTag st` to `mac`, the saved registers are restored,
and the tail call enters the `sodium_memzero` hook, which zeroes the state and returns. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj Poly1305Boringssl

theorem ad0 (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

set_option maxHeartbeats 4000000 in
theorem join {pl : Placement} {ex : String → Option (State → State)} {S0 s0 : State}
    {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {A M SP : BitVec 64} {R : SepProp} {rh mid rest mac0 st mac : List (BitVec 8)}
    {f : State → State}
    (hP : libsodiumDebianOnetimeauthLib.Placeable pl) (hCL0 : (P pl ex).CodeLoaded S0.mem)
    (hrun : s0.status = .Running)
    (hpath : Steps (P pl ex) S0 (mkS s0 (pl.base + 1160#64) r (SP - 32#64) ps m v))
    (hr19 : r 19#5 = A) (hr20 : r 20#5 = M)
    (hA : S0.readReg64 .x0 = A) (hM : S0.readReg64 .x1 = M) (hSP : S0.sp = SP)
    (hal : (SP - 32#64) &&& 0b1111#64 = 0#64) (halS : SP &&& 0b1111#64 = 0#64)
    (hcs : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat ≤ 28 → r k = S0.readReg64 (.gpr k))
    (hvr : VRegFile.calleeSaved ⟨v⟩ = calleeSavedVRegs S0)
    (hl : rh.length = 48 ∧ mid.length = 24 ∧ rest.length = 24 ∧ mac0.length = 16)
    (hok : StateOk rh)
    (htag : numTo16LeBytes (limbVal (hLimb rh) % p1305 + leBytesToNum (mid.take 16)) = finishTag st)
    (hs : m ⊨ (A ↦ₛ rh) ∗ ((A + 48#64) ↦ₛ mid) ∗ ((A + 72#64) ↦ₛ rest) ∗ (M ↦ₛ mac0) ∗
      ((SP - 32#64) ↦ₛ (unpack64 (S0.readReg64 (.gpr 29#5)) ++ unpack64 (S0.readReg64 (.gpr 30#5)) ++
        unpack64 (S0.readReg64 (.gpr 19#5)) ++ unpack64 (S0.readReg64 (.gpr 20#5)))) ∗
      memRegion (SP - 4128#64) 4096 ∗ R)
    (hf : HookOk f Libc.explicitBzeroSpec)
    (hat : (P pl ex).externAt? (pl.ρ "sodium_memzero") = some f) :
    ∃ sf, Steps (P pl ex) S0 sf ∧ SubroutineOutcome finishSpec (st, mac) R S0 sf := by
  generalize hstk : (unpack64 (S0.readReg64 (.gpr 29#5)) ++ unpack64 (S0.readReg64 (.gpr 30#5)) ++
        unpack64 (S0.readReg64 (.gpr 19#5)) ++ unpack64 (S0.readReg64 (.gpr 20#5))) = stk at hs
  have hsM : m ⊨ ((A + 48#64) ↦ₛ mid) ∗ ((A ↦ₛ rh) ∗ ((A + 72#64) ↦ₛ rest) ∗ (M ↦ₛ mac0) ∗
      ((SP - 32#64) ↦ₛ stk) ∗ memRegion (SP - 4128#64) 4096 ∗ R) := Satisfies.of_eq hs (by ac_rfl)
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hl
  have rd24 := sat_bytes_read64 hs 24 (by omega)
  have rd32 := sat_bytes_read64 hs 32 (by omega)
  have rd40 := sat_bytes_read64 hs 40 (by omega)
  have rp0 := sat_bytes_read64 hsM 0 (by omega)
  have rp8 := sat_bytes_read64 hsM 8 (by omega)
  have rd32' : (m.read64 (A + 0x18#64 + 8#64)).toNat = u64At rh 32 ∧
      m.canRead (A + 0x18#64 + 8#64) 8 = true := by
    have := rd32; rwa [BitVec.add_assoc]
  have rp0' : (m.read64 (A + 0x28#64 + 8#64)).toNat = u64At mid 0 ∧
      m.canRead (A + 0x28#64 + 8#64) 8 = true := by
    have := rp0; rw [ad0] at this; rwa [BitVec.add_assoc]
  have rp8' : (m.read64 (A + 0x38#64)).toNat = u64At mid 8 ∧ m.canRead (A + 0x38#64) 8 = true := by
    simpa [BitVec.add_assoc] using rp8
  -- +0x68: ldp x5, x2, [x19, #0x18]
  have g1 := stepS' hpath hrun (f_68 hP (cl hCL0 hpath))
    (ex_ldp64_gpr 5#5 2#5 19#5 (by decide) (by decide) (by decide) 0x18#64
      (by rw [hr19]; exact rd24.2) (by rw [hr19]; exact rd32'.2))
    (pc' := pl.base + 1164#64) (by simp [BitVec.add_assoc])
  simp only [upd_apply, BitVec.reduceEq, ite_false, reduceIte, hr19] at g1
  generalize hH0 : m.read64 (A + 0x18#64) = H0 at g1
  generalize hH1 : m.read64 (A + 0x18#64 + 8#64) = H1 at g1
  -- +0x6c: mov w3, #5
  obtain ⟨F5, eF5, g2⟩ := stepN g1 hrun (f_6c hP (cl hCL0 g1)) (ex_movz32 3#5 (by decide) _)
    (pc' := pl.base + 1168#64) (by simp [BitVec.add_assoc])
  -- +0x70: ldp x0, x1, [x19, #0x28]
  have g3 := stepS' g2 hrun (f_70 hP (cl hCL0 g2))
    (ex_ldp64_gpr 0#5 1#5 19#5 (by decide) (by decide) (by decide) 0x28#64
      (by simp only [upd_apply, BitVec.reduceEq, ite_false, reduceIte]; rw [hr19]; exact rd40.2)
      (by simp only [upd_apply, BitVec.reduceEq, ite_false, reduceIte]; rw [hr19]; exact rp0'.2))
    (pc' := pl.base + 1172#64) (by simp [BitVec.add_assoc])
  simp only [upd_apply, BitVec.reduceEq, ite_false, reduceIte, hr19] at g3
  generalize hH2 : m.read64 (A + 0x28#64) = H2 at g3
  generalize hT0 : m.read64 (A + 0x28#64 + 8#64) = T0 at g3
  obtain ⟨w1, e1, h1⟩ := stepN g3 hrun (f_74 hP (cl hCL0 g3)) (ex_and_imm 4#5 2#5 (by decide) (by decide) _) (pc' := pl.base + 1176#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e1
  obtain ⟨w2, e2, h2⟩ := stepN h1 hrun (f_78 hP (cl hCL0 h1)) (ex_add_shift 2#5 0#5 2#5 (by decide) (by decide) (by decide) .LSR 44) (pc' := pl.base + 1180#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e2
  obtain ⟨w3, e3, h3⟩ := stepN h2 hrun (f_7c hP (cl hCL0 h2)) (ex_and_imm 0#5 2#5 (by decide) (by decide) _) (pc' := pl.base + 1184#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e3
  obtain ⟨w4, e4, h4⟩ := stepN h3 hrun (f_80 hP (cl hCL0 h3)) (ex_bitfield .UBFM 2#5 2#5 (by decide) (by decide) 42 63) (pc' := pl.base + 1188#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e4
  obtain ⟨w5, e5, h5⟩ := stepN h4 hrun (f_84 hP (cl hCL0 h4)) (ex_umaddl 2#5 2#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide)) (pc' := pl.base + 1192#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e5
  obtain ⟨w6, e6, h6⟩ := stepN h5 hrun (f_88 hP (cl hCL0 h5)) (ex_and_imm 5#5 2#5 (by decide) (by decide) _) (pc' := pl.base + 1196#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e6
  obtain ⟨w7, e7, h7⟩ := stepN h6 hrun (f_8c hP (cl hCL0 h6)) (ex_add_shift 2#5 4#5 2#5 (by decide) (by decide) (by decide) .LSR 44) (pc' := pl.base + 1200#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e7
  obtain ⟨w8, e8, h8⟩ := stepN h7 hrun (f_90 hP (cl hCL0 h7)) (ex_and_imm 4#5 2#5 (by decide) (by decide) _) (pc' := pl.base + 1204#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e8
  obtain ⟨w9, e9, h9⟩ := stepN h8 hrun (f_94 hP (cl hCL0 h8)) (ex_add_shift 2#5 0#5 2#5 (by decide) (by decide) (by decide) .LSR 44) (pc' := pl.base + 1208#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e9
  obtain ⟨w10, e10, h10⟩ := stepN h9 hrun (f_98 hP (cl hCL0 h9)) (ex_and_imm 8#5 2#5 (by decide) (by decide) _) (pc' := pl.base + 1212#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e10
  obtain ⟨w11, e11, h11⟩ := stepN h10 hrun (f_9c hP (cl hCL0 h10)) (ex_bitfield .UBFM 0#5 2#5 (by decide) (by decide) 42 63) (pc' := pl.base + 1216#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e11
  obtain ⟨w12, e12, h12⟩ := stepN h11 hrun (f_a0 hP (cl hCL0 h11)) (ex_orr_imm 2#5 2#5 (by decide) (by decide) _) (pc' := pl.base + 1220#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e12
  obtain ⟨w13, e13, h13⟩ := stepN h12 hrun (f_a4 hP (cl hCL0 h12)) (ex_umaddl 0#5 0#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide)) (pc' := pl.base + 1224#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e13
  obtain ⟨w14, e14, h14⟩ := stepN h13 hrun (f_a8 hP (cl hCL0 h13)) (ex_movz64 5#5 (by decide) _) (pc' := pl.base + 1228#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e14
  obtain ⟨w15, e15, h15⟩ := stepN h14 hrun (f_ac hP (cl hCL0 h14)) (ex_and_imm 7#5 0#5 (by decide) (by decide) _) (pc' := pl.base + 1232#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e15
  obtain ⟨w16, e16, h16⟩ := stepN h15 hrun (f_b0 hP (cl hCL0 h15)) (ex_add_shift 0#5 4#5 0#5 (by decide) (by decide) (by decide) .LSR 44) (pc' := pl.base + 1236#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e16
  obtain ⟨w17, e17, h17⟩ := stepN h16 hrun (f_b4 hP (cl hCL0 h16)) (ex_add_imm 4#5 7#5 (by decide) (by decide) _) (pc' := pl.base + 1240#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e17
  obtain ⟨w18, e18, h18⟩ := stepN h17 hrun (f_b8 hP (cl hCL0 h17)) (ex_add_shift 3#5 0#5 4#5 (by decide) (by decide) (by decide) .LSR 44) (pc' := pl.base + 1244#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e18
  obtain ⟨w19, e19, h19⟩ := stepN h18 hrun (f_bc hP (cl hCL0 h18)) (ex_add_shift 2#5 2#5 3#5 (by decide) (by decide) (by decide) .LSR 44) (pc' := pl.base + 1248#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e19
  have hc := stepS' h19 hrun (f_c0 hP (cl hCL0 h19)) (ex_cmp_reg 2#5 5#5 (by decide) (by decide)) (pc' := pl.base + 1252#64) (by simp [BitVec.add_assoc])
  simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at hc
  obtain ⟨w20, e20, h20⟩ := stepN hc hrun (f_c4 hP (cl hCL0 hc)) (ex_csetm 9#5 (by decide) .LT) (pc' := pl.base + 1256#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e20
  obtain ⟨w21, e21, h21⟩ := stepN h20 hrun (f_c8 hP (cl hCL0 h20)) (ex_and_shift 7#5 7#5 2#5 (by decide) (by decide) (by decide) .ASR 63) (pc' := pl.base + 1260#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e21
  obtain ⟨w22, e22, h22⟩ := stepN h21 hrun (f_cc hP (cl hCL0 h21)) (ex_and_shift 6#5 4#5 9#5 (by decide) (by decide) (by decide) .LSL 0) (pc' := pl.base + 1264#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e22
  obtain ⟨w23, e23, h23⟩ := stepN h22 hrun (f_d0 hP (cl hCL0 h22)) (ex_and_shift 5#5 3#5 9#5 (by decide) (by decide) (by decide) .LSL 0) (pc' := pl.base + 1268#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e23
  have hT := stepS' h23 hrun (f_d4 hP (cl hCL0 h23))
    (ex_ldr64_gpr 4#5 19#5 (by decide) (by decide) 0x38#64
      (by simp only [upd_apply, BitVec.reduceEq, ite_false, reduceIte]; rw [hr19]; exact rp8'.2))
    (pc' := pl.base + 1272#64) (by simp [BitVec.add_assoc])
  simp only [upd_apply, BitVec.reduceEq, ite_false, reduceIte, hr19] at hT
  generalize hT1 : m.read64 (A + 0x38#64) = T1 at hT
  obtain ⟨w24, e24, h24⟩ := stepN hT hrun (f_d8 hP (cl hCL0 hT)) (ex_and_imm 6#5 6#5 (by decide) (by decide) _) (pc' := pl.base + 1276#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e24
  obtain ⟨w25, e25, h25⟩ := stepN h24 hrun (f_dc hP (cl hCL0 h24)) (ex_orr_shift 6#5 6#5 7#5 (by decide) (by decide) (by decide) .LSL 0) (pc' := pl.base + 1280#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e25
  obtain ⟨w26, e26, h26⟩ := stepN h25 hrun (f_e0 hP (cl hCL0 h25)) (ex_and_shift 3#5 0#5 2#5 (by decide) (by decide) (by decide) .ASR 63) (pc' := pl.base + 1284#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e26
  obtain ⟨w27, e27, h27⟩ := stepN h26 hrun (f_e4 hP (cl hCL0 h26)) (ex_and_imm 5#5 5#5 (by decide) (by decide) _) (pc' := pl.base + 1288#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e27
  obtain ⟨w28, e28, h28⟩ := stepN h27 hrun (f_e8 hP (cl hCL0 h27)) (ex_and_imm 0#5 1#5 (by decide) (by decide) _) (pc' := pl.base + 1292#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e28
  obtain ⟨w29, e29, h29⟩ := stepN h28 hrun (f_ec hP (cl hCL0 h28)) (ex_add_shift 0#5 0#5 6#5 (by decide) (by decide) (by decide) .LSL 0) (pc' := pl.base + 1296#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e29
  obtain ⟨w30, e30, h30⟩ := stepN h29 hrun (f_f0 hP (cl hCL0 h29)) (ex_extr 1#5 4#5 1#5 (by decide) (by decide) (by decide) 44) (pc' := pl.base + 1300#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e30
  obtain ⟨w31, e31, h31⟩ := stepN h30 hrun (f_f4 hP (cl hCL0 h30)) (ex_orr_shift 3#5 5#5 3#5 (by decide) (by decide) (by decide) .LSL 0) (pc' := pl.base + 1304#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e31
  obtain ⟨w32, e32, h32⟩ := stepN h31 hrun (f_f8 hP (cl hCL0 h31)) (ex_and_imm 1#5 1#5 (by decide) (by decide) _) (pc' := pl.base + 1308#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e32
  obtain ⟨w33, e33, h33⟩ := stepN h32 hrun (f_fc hP (cl hCL0 h32)) (ex_and_shift 7#5 8#5 2#5 (by decide) (by decide) (by decide) .ASR 63) (pc' := pl.base + 1312#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e33
  obtain ⟨w34, e34, h34⟩ := stepN h33 hrun (f_100 hP (cl hCL0 h33)) (ex_add_shift 1#5 1#5 3#5 (by decide) (by decide) (by decide) .LSL 0) (pc' := pl.base + 1316#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e34
  obtain ⟨w35, e35, h35⟩ := stepN h34 hrun (f_104 hP (cl hCL0 h34)) (ex_and_shift 2#5 2#5 9#5 (by decide) (by decide) (by decide) .LSL 0) (pc' := pl.base + 1320#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e35
  obtain ⟨w36, e36, h36⟩ := stepN h35 hrun (f_108 hP (cl hCL0 h35)) (ex_and_imm 6#5 0#5 (by decide) (by decide) _) (pc' := pl.base + 1324#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e36
  obtain ⟨w37, e37, h37⟩ := stepN h36 hrun (f_10c hP (cl hCL0 h36)) (ex_orr_shift 2#5 2#5 7#5 (by decide) (by decide) (by decide) .LSL 0) (pc' := pl.base + 1328#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e37
  obtain ⟨w38, e38, h38⟩ := stepN h37 hrun (f_110 hP (cl hCL0 h37)) (ex_add_shift 0#5 1#5 0#5 (by decide) (by decide) (by decide) .LSR 44) (pc' := pl.base + 1332#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e38
  obtain ⟨w39, e39, h39⟩ := stepN h38 hrun (f_114 hP (cl hCL0 h38)) (ex_add_shift 4#5 2#5 4#5 (by decide) (by decide) (by decide) .LSR 24) (pc' := pl.base + 1336#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e39
  obtain ⟨w40, e40, h40⟩ := stepN h39 hrun (f_118 hP (cl hCL0 h39)) (ex_add_shift 4#5 4#5 0#5 (by decide) (by decide) (by decide) .LSR 44) (pc' := pl.base + 1340#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e40
  obtain ⟨w41, e41, h41⟩ := stepN h40 hrun (f_11c hP (cl hCL0 h40)) (ex_bitfield .UBFM 1#5 0#5 (by decide) (by decide) 20 43) (pc' := pl.base + 1344#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e41
  obtain ⟨w42, e42, h42⟩ := stepN h41 hrun (f_120 hP (cl hCL0 h41)) (ex_orr_shift 0#5 6#5 0#5 (by decide) (by decide) (by decide) .LSL 44) (pc' := pl.base + 1348#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e42
  obtain ⟨w43, e43, h43⟩ := stepN h42 hrun (f_124 hP (cl hCL0 h42)) (ex_orr_shift 4#5 1#5 4#5 (by decide) (by decide) (by decide) .LSL 24) (pc' := pl.base + 1352#64) (by simp [BitVec.add_assoc])
  try simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, reduceIte] at e43

  -- the reduction
  obtain ⟨hl48, hr0b, hr1b, hr2b, hb0, hb1, hb2⟩ := hok
  have vH0 : H0.toNat = hLimb rh 0 := by rw [← hH0]; exact rd24.1
  have vH1 : H1.toNat = hLimb rh 1 := by rw [← hH1]; exact rd32'.1
  have vH2 : H2.toNat = hLimb rh 2 := by rw [← hH2]; exact rd40.1
  have vT0 : T0.toNat = u64At mid 0 := by rw [← hT0]; exact rp0'.1
  have vT1 : T1.toNat = u64At mid 8 := by rw [← hT1]; exact rp8'.1
  have FA := fin_arith_d H0 H1 H2 T0 T1 F5 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
    w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40
    w41 w42 w43 eF5 (by rw [vH0]; exact hb0) (by rw [vH1]; exact hb1) (by rw [vH2]; exact hb2)
    e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26
    e27 e28 e29 e30 e31 e32 e33 e34 e35 e36 e37 e38 e39 e40 e41 e42 e43
  -- the tag value
  have hval : limbVal (hLimb rh) % p1305 + leBytesToNum (mid.take 16) =
      (H0.toNat + 2 ^ 44 * H1.toNat + 2 ^ 88 * H2.toNat) % p1305 + (T0.toNat + 2 ^ 64 * T1.toNat) := by
    rw [leBytes_take16 mid (by omega), ← vT0, ← vT1, limbVal, ← vH0, ← vH1, ← vH2]
  have htag' : unpack64 w42 ++ unpack64 w43 = finishTag st := by
    rw [unpack_tag, FA, numTo16_mod, ← hval, htag]
  -- +0x128: stp x0, x4, [x20]
  have hsC : m ⊨ (M ↦ₛ mac0) ∗ ((A ↦ₛ rh) ∗ ((A + 48#64) ↦ₛ mid) ∗ ((A + 72#64) ↦ₛ rest) ∗
      ((SP - 32#64) ↦ₛ stk) ∗ memRegion (SP - 4128#64) 4096 ∗ R) := Satisfies.of_eq hs (by ac_rfl)
  have wA := sat_bytes_write64 hsC 0 (by omega) w42
  have wA8 := (sat_bytes_write64 hsC 8 (by omega) w43).1
  have wB := sat_bytes_write64 wA.2 8 (by simp; omega) w43
  rw [ad0] at wA
  have g45 := stepS' h43 hrun (f_128 hP (cl hCL0 h43))
    (ex_stp64_gpr 0#5 4#5 20#5 (by decide) (by decide) (by decide) 0#64
      (by simp only [upd_apply, BitVec.reduceEq, ite_false]; rw [hr20, BitVec.add_zero]; exact wA.1)
      (by simp only [upd_apply, BitVec.reduceEq, ite_false]; rw [hr20, BitVec.add_zero]; exact wA8))
    (pc' := pl.base + 1356#64) (by simp [BitVec.add_assoc])
  simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true, hr20, BitVec.add_zero] at g45
  have hL : List.take 8 (List.take 0 mac0 ++ unpack64 w42 ++ List.drop 8 mac0) ++ unpack64 w43 ++
      List.drop (8 + 8) (List.take 0 mac0 ++ unpack64 w42 ++ List.drop 8 mac0) =
      unpack64 w42 ++ unpack64 w43 := by
    simp [List.take_append, List.drop_append]
    rw [List.take_of_length_le (l := unpack64 w42) (by simp),
      List.drop_eq_nil_of_le (as := mac0) (by rw [hl4])]; simp
  rw [hL, htag', BitVec.add_zero] at wB
  generalize hm2 : (m.write64 M w42).write64 (M + 8#64) w43 = m2 at g45 wB
  replace wB := wB.2
  -- +0x12c: mov x0, x19
  have g46 := stepS' g45 hrun (f_12c hP (cl hCL0 g45)) (ex_mov 0#5 19#5 (by decide) (by decide))
    (pc' := pl.base + 1360#64) (by simp [BitVec.add_assoc])
  -- +0x130: ldp x19, x20, [sp, #0x10]
  have hsS : m2 ⊨ ((SP - 32#64) ↦ₛ stk) ∗ ((M ↦ₛ finishTag st) ∗ (A ↦ₛ rh) ∗ ((A + 48#64) ↦ₛ mid) ∗
      ((A + 72#64) ↦ₛ rest) ∗ memRegion (SP - 4128#64) 4096 ∗ R) := Satisfies.of_eq wB (by ac_rfl)
  have hsk : stk.length = 32 := by rw [← hstk]; simp
  have rs0 := sat_bytes_read64 hsS 0 (by omega)
  have rs8 := sat_bytes_read64 hsS 8 (by omega)
  have rs16 := sat_bytes_read64 hsS 16 (by omega)
  have rs24 := sat_bytes_read64 hsS 24 (by omega)
  rw [ad0] at rs0
  have rs24' : (m2.read64 (SP - 32#64 + 0x10#64 + 8#64)).toNat = u64At stk 24 ∧
      m2.canRead (SP - 32#64 + 0x10#64 + 8#64) 8 = true := by
    have := rs24; rwa [BitVec.add_assoc]
  have g47 := stepS' g46 hrun (f_130 hP (cl hCL0 g46))
    (ex_ldp64_sp 19#5 20#5 (by decide) (by decide) 0x10#64 hal rs16.2 rs24'.2)
    (pc' := pl.base + 1364#64) (by simp [BitVec.add_assoc])
  generalize hX19 : m2.read64 (SP - 32#64 + 0x10#64) = X19 at g47
  generalize hX20 : m2.read64 (SP - 32#64 + 0x10#64 + 8#64) = X20 at g47
  -- +0x134: mov x1, #0x60
  have g48 := stepS' g47 hrun (f_134 hP (cl hCL0 g47)) (ex_movz64 1#5 (by decide) _)
    (pc' := pl.base + 1368#64) (by simp [BitVec.add_assoc])
  -- +0x138: ldp x29, x30, [sp], #0x20
  have g49 := stepS' g48 hrun (f_138 hP (cl hCL0 g48))
    (ex_ldp64_post_sp 29#5 30#5 (by decide) (by decide) 0x20#64 hal rs0.2 rs8.2)
    (pc' := pl.base + 1372#64) (by simp [BitVec.add_assoc])
  generalize hX29 : m2.read64 (SP - 32#64) = X29 at g49
  generalize hX30 : m2.read64 (SP - 32#64 + 8#64) = X30 at g49
  rw [show SP - 32#64 + 0x20#64 = SP by bv_omega] at g49
  -- +0x13c: autiasp
  have g50 := stepS' g49 hrun (f_13c hP (cl hCL0 g49)) (ex_hint _)
    (pc' := pl.base + 1376#64) (by simp [BitVec.add_assoc])
  -- +0x140: b sodium_memzero
  have g51 := stepS g50 hrun (f_140 hP (cl hCL0 g50)) (ex_b _)
  rw [show pl.base + 1376#64 + (pl.ρ "sodium_memzero" - (pl.base + 1376#64)) =
    pl.ρ "sodium_memzero" by bv_omega] at g51
  -- the saved registers
  obtain ⟨k0, k8, k16, k24⟩ := stk_u64 (S0.readReg64 (.gpr 29#5)) (S0.readReg64 (.gpr 30#5))
    (S0.readReg64 (.gpr 19#5)) (S0.readReg64 (.gpr 20#5))
  rw [hstk] at k0 k8 k16 k24
  have v29 : X29 = S0.readReg64 (.gpr 29#5) := BitVec.eq_of_toNat_eq (by rw [← hX29, rs0.1, k0])
  have v30 : X30 = S0.readReg64 (.gpr 30#5) := BitVec.eq_of_toNat_eq (by rw [← hX30, rs8.1, k8])
  have v19 : X19 = S0.readReg64 (.gpr 19#5) := BitVec.eq_of_toNat_eq (by rw [← hX19, rs16.1, k16])
  have v20 : X20 = S0.readReg64 (.gpr 20#5) := BitVec.eq_of_toNat_eq (by rw [← hX20, rs24'.1, k24])
  have hs' : m2 ⊨ (A ↦ₛ rh) ∗ ((A + 48#64) ↦ₛ mid) ∗ ((A + 72#64) ↦ₛ rest) ∗ (M ↦ₛ finishTag st) ∗
      ((SP - 32#64) ↦ₛ stk) ∗ memRegion (SP - 4128#64) 4096 ∗ R := Satisfies.of_eq wB (by ac_rfl)
  refine tail_hook (rh := rh) (mid := mid) (rest := rest) (stk := stk) hrun g51 ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hvr hA hM hSP halS ⟨hl1, hl2, hl3, hsk⟩ hs' hf hat
  · simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true, hr19]
  · simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true]; rfl
  · simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true, v19]
  · simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true, v20]
  · simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true, v29]
  · simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true, v30]
  · intro k hk1 hk2
    have e : k = BitVec.ofNat 5 k.toNat := by simp
    generalize hj : k.toNat = j at e hk1 hk2
    subst e
    interval_cases j <;> simp only [upd_apply, BitVec.reduceEq, BitVec.ofNat_eq_ofNat, ite_false] <;>
      exact hcs _ (by decide) (by decide)

end Poly1305Debian.FD

end
end

section
section
/-! # The prologue of `poly1305_finish` (+0x0..+0x14) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj Poly1305Boringssl

theorem st_split (A : BitVec 64) (st : List (BitVec 8)) (h : st.length = 96) :
    (A ↦ₛ st) = (A ↦ₛ st.take 48) ∗ ((A + 48#64) ↦ₛ (st.drop 48).take 24) ∗
      ((A + 72#64) ↦ₛ st.drop 72) := by
  conv_lhs => rw [← List.take_append_drop 48 st, ← List.take_append_drop 24 (st.drop 48)]
  rw [pointsToBytes_append, pointsToBytes_append, List.drop_drop]
  simp only [List.length_take, List.length_drop, h]
  rw [BitVec.add_assoc]; rfl

/-- The four saved registers written into the 32-byte frame. -/
theorem stk_writes (bs : List (BitVec 8)) (h : bs.length = 32) (a b c d : BitVec 64) :
    let L1 := List.take 0 bs ++ unpack64 a ++ List.drop (0 + 8) bs
    let L2 := List.take 8 L1 ++ unpack64 b ++ List.drop (8 + 8) L1
    let L3 := List.take 16 L2 ++ unpack64 c ++ List.drop (16 + 8) L2
    List.take 24 L3 ++ unpack64 d ++ List.drop (24 + 8) L3 =
      unpack64 a ++ unpack64 b ++ unpack64 c ++ unpack64 d := by
  match bs, h with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _ =>
    simp [unpack64]

theorem u64At_take (st : List (BitVec 8)) (k : Nat) (hk : k + 8 ≤ 48) :
    u64At (st.take 48) k = u64At st k := by
  unfold u64At; rw [List.drop_take, List.take_take]; congr 2; omega

theorem limbVal_take (st : List (BitVec 8)) (f : List (BitVec 8) → Nat → Nat)
    (hf : ∀ i, i ≤ 2 → f (st.take 48) i = f st i) : limbVal (f (st.take 48)) = limbVal (f st) := by
  unfold limbVal; rw [hf 0 (by omega), hf 1 (by omega), hf 2 (by omega)]

theorem hLimb_take' (st : List (BitVec 8)) (i : Nat) (hi : i ≤ 2) : hLimb (st.take 48) i = hLimb st i := by
  unfold hLimb; rw [u64At_take]; omega

theorem rLimb_take' (st : List (BitVec 8)) (i : Nat) (hi : i ≤ 2) : rLimb (st.take 48) i = rLimb st i := by
  unfold rLimb; rw [u64At_take]; omega

theorem fnAddr_finish (pl : Placement) :
    libsodiumDebianOnetimeauthLib.fnAddr pl "poly1305_finish [libsodium_la_poly1305_donna]" = pl.base + 1056#64 := rfl

theorem fnAddr_blocks (pl : Placement) :
    libsodiumDebianOnetimeauthLib.fnAddr pl "poly1305_blocks [libsodium_la_poly1305_donna]" = pl.base + 416#64 := rfl

end Poly1305Debian.FD

end
end

section
section
/-! # Byte-list facts for the padding of the last block -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj Poly1305Boringssl

theorem canWrite1_of_sat {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (j : Nat) (hj : j < bs.length) :
    m.canWrite (a + BitVec.ofNat 64 j) 1 = true :=
  canWrite_of (fun i hi => by
    have : i = 0 := by omega
    subst this; rw [BitVec.add_zero]; exact (sat_bytes_read hs j hj).2.1)

end Poly1305Debian.FD

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

theorem set_take (l : List (BitVec 8)) (n : Nat) (a : BitVec 8) (hn : n < l.length) :
    (l.set n a).take (n + 1) = l.take n ++ [a] := by
  rw [List.take_set]
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp only [List.length_set, List.length_take] at h1
  simp only [List.getElem_set, List.getElem_append, List.getElem_take, List.length_take]
  split_ifs <;> first | rfl | omega | simp

theorem set15 (l : List (BitVec 8)) (h : l.length = 24) :
    l.set 15 1#8 = l.take 15 ++ [1#8] ++ List.replicate (15 - 15) 0#8 ++ l.drop 16 := by
  rw [show 15 - 15 = 0 from rfl, List.replicate_zero, List.append_nil, ← set_take l 15 _ (by omega),
    ← List.drop_set_of_lt (l := l) (a := 1#8) (by omega : 15 < 16), List.take_append_drop]

end Poly1305Debian.FD

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Poly1305Boringssl

theorem leBytes_zeros (n : Nat) : leBytesToNum (List.replicate n 0#8) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, leBytesToNum] at ih ⊢; exact ih

theorem blocksAcc16 (r a : Nat) (buf : List (BitVec 8)) (h : buf.length = 16) :
    blocksAcc r (hibit 1#8) a buf = r * (a + leBytesToNum buf) % p1305 := by
  have hh : hibit 1#8 = 0 := by decide
  simp [blocksAcc, h, hh, List.take_of_length_le (show buf.length ≤ 16 by omega)]

end Poly1305Debian.FD

end
end

section
section
/-! # The call `bl memset` at +0x4c: the hook zeroes the padding bytes and returns -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj Poly1305Boringssl

theorem memset_call {pl : Placement} {ex : String → Option (State → State)} {S0 s0 : State}
    {rf : BitVec 5 → BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {B SP : BitVec 64} {F : SepProp} {pre mid post : List (BitVec 8)} {f : State → State}
    (hrun : s0.status = .Running)
    (g : Steps (P pl ex) S0 (mkS s0 (pl.ρ "memset") rf (SP - 32#64) ps m v))
    (h0 : rf 0#5 = B + BitVec.ofNat 64 pre.length) (h1 : rf 1#5 = 0#64)
    (h2 : (rf 2#5).toNat = mid.length)
    (hal : (SP - 32#64) &&& 0b1111#64 = 0#64)
    (hs : m ⊨ (B ↦ₛ (pre ++ mid ++ post)) ∗ memRegion (SP - 4128#64) 4096 ∗ F)
    (hf : HookOk f VerifiedLibraries.Musl.cryptoMemsetSpec)
    (hat : (P pl ex).externAt? (pl.ρ "memset") = some f) :
    ∃ sf, Steps (P pl ex) S0 sf ∧ sf.status = .Running ∧ sf.pc = rf 30#5 ∧ sf.sp = SP - 32#64 ∧
      CalleeSavedPreserved (mkS s0 (pl.ρ "memset") rf (SP - 32#64) ps m v) sf ∧
      sf.mem ⊨ (B ↦ₛ (pre ++ List.replicate mid.length 0#8 ++ post)) ∗
        memRegion (SP - 4128#64) 4096 ∗ F := by
  generalize hsh : mkS s0 (pl.ρ "memset") rf (SP - 32#64) ps m v = sh at g
  have hshp : sh.pc = pl.ρ "memset" := by rw [← hsh]; rfl
  have hshs : sh.status = .Running := by rw [← hsh]; exact hrun
  have hshsp : sh.sp = SP - 32#64 := by rw [← hsh]; rfl
  have hshm : sh.mem = m := by rw [← hsh]; rfl
  have rd : ∀ k : BitVec 5, k ≠ 31#5 → sh.readReg64 (.gpr k) = rf k := by
    intro k hk; rw [← hsh]; simp [hk]
  generalize hP : B + BitVec.ofNat 64 pre.length = p at h0
  have eB : (B ↦ₛ (pre ++ mid ++ post)) = (B ↦ₛ pre) ∗ (p ↦ₛ mid) ∗
      ((p + BitVec.ofNat 64 mid.length) ↦ₛ post) := by
    rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append, hP]
  rw [eB] at hs
  have hs1 : m ⊨ (p ↦ₛ mid) ∗ (memRegion (SP - 4128#64) 4096 ∗ ((B ↦ₛ pre) ∗
      ((p + BitVec.ofNat 64 mid.length) ↦ₛ post) ∗ F)) := Satisfies.of_eq hs (by ac_rfl)
  have hs2 := sat_sep_mono hs1 (bytes_entails_memRegion p mid)
  have hpre : sh.mem ⊨ VerifiedLibraries.Musl.cryptoMemsetSpec.pre (p, 0#8, mid.length) sh ∗
      ((B ↦ₛ pre) ∗ ((p + BitVec.ofNat 64 mid.length) ↦ₛ post) ∗ F) := by
    simp only [VerifiedLibraries.Musl.cryptoMemsetSpec, VerifiedLibraries.Musl.cExtern,
      ProofLib.stackAt, VerifiedLibraries.Musl.externStack]
    rw [sepConj_assoc, sat_pure_sep]
    refine ⟨⟨by rw [Reg.x0, rd 0#5 (by decide), h0], ?_, by rw [Reg.x2, rd 2#5 (by decide), h2]⟩, ?_⟩
    · show (sh.readReg32 (.gpr 1#5)).truncate 8 = 0#8
      simp only [State.readReg32, rd 1#5 (by decide), h1]
      rfl
    rw [hshsp, hshm, show SP - 32#64 - BitVec.ofNat 64 4096 = SP - 4128#64 by bv_omega]
    exact Satisfies.of_eq hs2 (by ac_rfl)
  have hal' : sh.spAligned = true := by rw [← hsh]; simp [hal]
  obtain ⟨hkeep, hsym, hout⟩ := hf (p, 0#8, mid.length) _ sh hshs hpre hal'
  have gF : Steps (P pl ex) S0 (f sh) :=
    Steps.snoc g (Step.externHook hshs (by rw [hshp]; exact hat) hkeep hsym)
  rcases hout with ⟨⟨hpc, hsp, hst⟩, ⟨_, hcsf⟩, hpost⟩ | ⟨_, hp⟩ | ⟨c, _, hp⟩ | ⟨_, hp⟩
  · refine ⟨f sh, gF, hst, ?_, by rw [hsp, hshsp], by rw [← hsh] at hcsf ⊢; exact hcsf, ?_⟩
    · rw [hpc, Reg.lr, rd 30#5 (by decide)]
    · simp only [VerifiedLibraries.Musl.cryptoMemsetSpec, VerifiedLibraries.Musl.cExtern,
        ProofLib.stackAt, VerifiedLibraries.Musl.externStack] at hpost
      have hq : (f sh).mem ⊨ ⌜(f sh).readReg64 Reg.x0 = p⌝ ∗ ((p ↦ₛ List.replicate mid.length 0#8) ∗
          memRegion (sh.sp - 4096#64) 4096 ∗ (B ↦ₛ pre) ∗
          ((p + BitVec.ofNat 64 mid.length) ↦ₛ post) ∗ F) := Satisfies.of_eq hpost (by ac_rfl)
      rw [sat_pure_sep] at hq
      obtain ⟨-, hpost⟩ := hq
      rw [hshsp, show SP - 32#64 - 4096#64 = SP - 4128#64 by bv_omega] at hpost
      have eB' : (B ↦ₛ (pre ++ List.replicate mid.length 0#8 ++ post)) = (B ↦ₛ pre) ∗
          (p ↦ₛ List.replicate mid.length 0#8) ∗ ((p + BitVec.ofNat 64 mid.length) ↦ₛ post) := by
        rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append, hP, List.length_replicate]
      rw [eB']
      exact Satisfies.of_eq hpost (by ac_rfl)
  · exact absurd hp not_sat_false'
  · exact absurd hp not_sat_false'
  · exact absurd hp not_sat_false'

end Poly1305Debian.FD

end
end

section
section
/-! # Debian's `poly1305_finish` meets `finishSpec`, given `poly1305_blocks`'s contract and the
`memset` and `sodium_memzero` hooks at the addresses its calls reach -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj Poly1305Boringssl

/-- `blocksSpec` with the message length also a multiple of 16; `poly1305_finish` calls
`poly1305_blocks` with 16 bytes. -/
def blocksW : Spec (Bool × List (BitVec 8) × BitVec 8 × List (BitVec 8)) :=
  { blocksSpec with
    pre := fun g s0 =>
      match g with
      | (_, _, _, m) => ⌜m.length % 16 = 0⌝ ∗ blocksSpec.pre g s0 }

set_option maxHeartbeats 4000000 in
theorem finish_main {pl : Placement} {ex : String → Option (State → State)} {f fm : State → State}
    (hP : libsodiumDebianOnetimeauthLib.Placeable pl) (hf : HookOk f Libc.explicitBzeroSpec)
    (hat : (P pl ex).externAt? (pl.ρ "sodium_memzero") = some f)
    (hfm : HookOk fm VerifiedLibraries.Musl.cryptoMemsetSpec)
    (hatm : (P pl ex).externAt? (pl.ρ "memset") = some fm)
    (hB : subroutine_ok (P pl ex) (pl.base + 416#64) blocksW)
    (st mac : List (BitVec 8)) (R : SepProp) (S0 : State) (hpc : S0.pc = pl.base + 1056#64)
    (hrun : S0.status = .Running) (hpre : S0.mem ⊨ finishSpec.pre (st, mac) S0 ∗ R)
    (hal : S0.spAligned = true) (hCL0 : (P pl ex).CodeLoaded S0.mem) :
    ∃ sf, Steps (P pl ex) S0 sf ∧ SubroutineOutcome finishSpec (st, mac) R S0 sf := by
  simp only [finishSpec, stackFrame] at hpre
  rw [sepConj_assoc, sat_pure_sep] at hpre
  obtain ⟨⟨hl96, hok, hL16, hl16⟩, hpre⟩ := hpre
  generalize hA : S0.readReg64 Reg.x0 = A at hpre
  generalize hM : S0.readReg64 Reg.x1 = M at hpre
  generalize hSP : S0.sp = SP at hpre
  have halS : SP &&& 0b1111#64 = 0#64 := by
    rw [← hSP]; simpa [State.spAligned] using hal
  have hal32 : (SP - 32#64) &&& 0b1111#64 = 0#64 := by
    have := (BitVec.toNat_eq.mp halS); apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_sub] at this ⊢
    rw [show (0b1111#64 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at this ⊢
    simp at this ⊢; omega
  -- the stack: 4096 bytes, then the 32-byte frame
  have hs1 : S0.mem ⊨ memRegion (SP - 4128#64) (4096 + 32) ∗ ((A ↦ₛ st) ∗ (M ↦ₛ mac) ∗ R) :=
    Satisfies.of_eq hpre (by ac_rfl)
  have hs2 := sat_sep_mono hs1 (memRegion_split (SP - 4128#64) 4096 32 (by decide))
  rw [show SP - 4128#64 + BitVec.ofNat 64 4096 = SP - 32#64 by bv_omega] at hs2
  have hs3 : S0.mem ⊨ memRegion (SP - 32#64) 32 ∗ (memRegion (SP - 4128#64) 4096 ∗
      (A ↦ₛ st) ∗ (M ↦ₛ mac) ∗ R) := Satisfies.of_eq hs2 (by ac_rfl)
  have hs4 := sat_sep_mono hs3 (memRegion_entails_bytes (SP - 32#64) 32 (by decide))
  rw [sepExists_sepConj, sat_sepExists] at hs4
  obtain ⟨bs, hs4⟩ := hs4
  rw [sepConj_assoc, sat_pure_sep] at hs4
  obtain ⟨hbs, hs4⟩ := hs4
  rw [st_split A st hl96] at hs4
  generalize hrh : List.take 48 st = rh at hs4
  generalize hmid : List.take 24 (List.drop 48 st) = mid at hs4
  generalize hrest : List.drop 72 st = rest at hs4
  have hl1 : rh.length = 48 := by rw [← hrh]; simp [hl96]
  have hl2 : mid.length = 24 := by rw [← hmid]; simp [hl96]
  have hl3 : rest.length = 24 := by rw [← hrest]; simp [hl96]
  have rA : S0.regs.regs 0#5 = A := by rw [← hA, Reg.x0, readGpr_eq S0 _ (by decide)]
  have rM : S0.regs.regs 1#5 = M := by rw [← hM, Reg.x1, readGpr_eq S0 _ (by decide)]
  have g0 : Steps (P pl ex) S0 (mkS S0 (pl.base + 1056#64) S0.regs.regs SP S0.pstate S0.mem
      S0.vregs.regs) := by
    rw [← hpc, ← hSP, mkS_self]; exact Steps.refl _
  -- +0x0: paciasp
  have g0' := stepS' g0 hrun (f_0 hP hCL0) (ex_hint _)
    (pc' := pl.base + 1060#64) (by simp [BitVec.add_assoc])
  -- +0x4: stp x29, x30, [sp, #-0x20]!
  have w0 := sat_bytes_write64 hs4 0 (by omega) (S0.regs.regs 29#5)
  have w8 := (sat_bytes_write64 hs4 8 (by omega) (S0.regs.regs 30#5)).1
  rw [ad0] at w0
  have w08 := sat_bytes_write64 w0.2 8 (by simp; omega) (S0.regs.regs 30#5)
  have e1 : SP + 0xffffffffffffffe0#64 = SP - 32#64 := by bv_omega
  have g1 := stepS' g0' hrun (f_4 hP hCL0)
    (ex_stp64_pre_sp 29#5 30#5 (by decide) (by decide) 0xffffffffffffffe0#64 halS
      (by rw [e1]; exact w0.1) (by rw [e1]; exact w8))
    (pc' := pl.base + 1064#64) (by simp [BitVec.add_assoc])
  rw [e1] at g1
  generalize hm1 : (S0.mem.write64 (SP - 32#64) (S0.regs.regs 29#5)).write64 (SP - 32#64 + 8#64)
    (S0.regs.regs 30#5) = m1 at g1 w08
  replace w08 := w08.2
  -- +0x8: mov x29, sp
  have g2 := stepS' g1 hrun (f_8 hP (cl hCL0 g1)) (ex_add_gpr_sp 29#5 (by decide) 0#12)
    (pc' := pl.base + 1068#64) (by simp [BitVec.add_assoc])
  -- +0xc: stp x19, x20, [sp, #0x10]
  have w16 := sat_bytes_write64 w08 16 (by simp; omega) (S0.regs.regs 19#5)
  have w24 := (sat_bytes_write64 w08 24 (by simp; omega) (S0.regs.regs 20#5)).1
  have w1624 := sat_bytes_write64 w16.2 24 (by simp; omega) (S0.regs.regs 20#5)
  have e24 : SP - 32#64 + 0x10#64 + 8#64 = SP - 32#64 + BitVec.ofNat 64 24 := by
    rw [BitVec.add_assoc]; rfl
  have g3 := stepS' g2 hrun (f_c hP (cl hCL0 g2))
    (ex_stp64_sp 19#5 20#5 (by decide) (by decide) 0x10#64 hal32 w16.1 (by rw [e24]; exact w24))
    (pc' := pl.base + 1072#64) (by simp [BitVec.add_assoc])
  simp only [upd_apply, BitVec.reduceEq, ite_false] at g3
  rw [e24] at g3
  generalize hm2 : (m1.write64 (SP - 32#64 + 0x10#64) (S0.regs.regs 19#5)).write64
    (SP - 32#64 + BitVec.ofNat 64 24) (S0.regs.regs 20#5) = m2 at g3 w1624
  replace w1624 := w1624.2
  -- +0x10: mov x20, x1
  have g4 := stepS' g3 hrun (f_10 hP (cl hCL0 g3)) (ex_mov 20#5 1#5 (by decide) (by decide))
    (pc' := pl.base + 1076#64) (by simp [BitVec.add_assoc])
  -- +0x14: mov x19, x0
  have g5 := stepS' g4 hrun (f_14 hP (cl hCL0 g4)) (ex_mov 19#5 0#5 (by decide) (by decide))
    (pc' := pl.base + 1080#64) (by simp [BitVec.add_assoc])
  simp only [upd_apply, BitVec.reduceEq, ite_false, rA, rM] at g5
  -- +0x18: ldr x1, [x0, #0x40]
  have hsMid : m2 ⊨ ((A + 48#64) ↦ₛ mid) ∗ ((A ↦ₛ rh) ∗ ((A + 72#64) ↦ₛ rest) ∗ (M ↦ₛ mac) ∗
      memRegion (SP - 4128#64) 4096 ∗ R ∗ ((SP - 32#64) ↦ₛ _)) := Satisfies.of_eq w1624 (by ac_rfl)
  have rL := sat_bytes_read64 hsMid 16 (by omega)
  rw [show A + 48#64 + BitVec.ofNat 64 16 = A + 0x40#64 by bv_omega] at rL
  have g6 := stepS' g5 hrun (f_18 hP (cl hCL0 g5))
    (ex_ldr64_gpr 1#5 0#5 (by decide) (by decide) 0x40#64
      (by simp only [upd_apply, BitVec.reduceEq, ite_false]; rw [rA]; exact rL.2))
    (pc' := pl.base + 1084#64) (by simp [BitVec.add_assoc])
  simp only [upd_apply, BitVec.reduceEq, ite_false, rA] at g6
  generalize hLv : m2.read64 (A + 0x40#64) = L at g6
  have vL : L.toNat = u64At st 64 := by
    rw [← hLv, rL.1, ← hmid]; simp [u64At, List.drop_take, List.take_take, List.drop_drop]
  -- +0x1c: cbz x1, +0x4c
  have g7 := stepS g6 hrun (f_1c hP (cl hCL0 g6)) (ex_cbz 1#5 (by decide) 0x4c#64)
  simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true] at g7
  have hstk := stk_writes bs hbs (S0.regs.regs 29#5) (S0.regs.regs 30#5) (S0.regs.regs 19#5)
    (S0.regs.regs 20#5)
  simp only at hstk
  rw [hstk, ← readGpr_eq S0 29#5 (by decide), ← readGpr_eq S0 30#5 (by decide),
    ← readGpr_eq S0 19#5 (by decide), ← readGpr_eq S0 20#5 (by decide)] at w1624
  have hok' : StateOk rh := by rw [← hrh]; exact hok
  have hs' : m2 ⊨ (A ↦ₛ rh) ∗ ((A + 48#64) ↦ₛ mid) ∗ ((A + 72#64) ↦ₛ rest) ∗ (M ↦ₛ mac) ∗
      ((SP - 32#64) ↦ₛ (unpack64 (S0.readReg64 (.gpr 29#5)) ++ unpack64 (S0.readReg64 (.gpr 30#5)) ++
        unpack64 (S0.readReg64 (.gpr 19#5)) ++ unpack64 (S0.readReg64 (.gpr 20#5)))) ∗
      memRegion (SP - 4128#64) 4096 ∗ R := Satisfies.of_eq w1624 (by ac_rfl)
  by_cases hL0 : L = 0#64
  · rw [if_pos hL0, show pl.base + 1084#64 + 0x4c#64 = pl.base + 1160#64 by rw [BitVec.add_assoc]; rfl]
      at g7
    have hu : u64At st 64 = 0 := by rw [← vL, hL0]; rfl
    refine join hP hCL0 hrun g7 (by simp [upd_apply]) (by simp [upd_apply]) hA hM hSP hal32 halS
      ?_ rfl ⟨hl1, hl2, hl3, hl16⟩ hok' ?_ hs' hf hat
    · intro k hk1 hk2
      have e : k = BitVec.ofNat 5 k.toNat := by simp
      generalize hj : k.toNat = j at e hk1 hk2
      subst e
      interval_cases j <;> simp only [upd_apply, BitVec.reduceEq, BitVec.ofNat_eq_ofNat, ite_false] <;>
        exact (readGpr_eq S0 _ (by decide)).symm
    · unfold finishTag
      simp only [hu, if_true]
      rw [← hrh, ← hmid, List.take_take, show min 16 24 = 16 from rfl,
        limbVal_take st hLimb (fun i hi => hLimb_take' st i hi)]
  · rw [if_neg hL0, show pl.base + 1084#64 + 4#64 = pl.base + 1088#64 by rw [BitVec.add_assoc]; rfl]
      at g7
    have hℓ1 : 1 ≤ L.toNat := by
      rcases Nat.eq_zero_or_pos L.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hL0
      · exact h
    have hℓ2 : L.toNat < 16 := by rw [vL]; exact hL16
    have hsR : m2 ⊨ ((A + 72#64) ↦ₛ rest) ∗ ((A ↦ₛ rh) ∗ ((A + 48#64) ↦ₛ mid) ∗ (M ↦ₛ mac) ∗
        ((SP - 32#64) ↦ₛ (unpack64 (S0.readReg64 (.gpr 29#5)) ++ unpack64 (S0.readReg64 (.gpr 30#5)) ++
          unpack64 (S0.readReg64 (.gpr 19#5)) ++ unpack64 (S0.readReg64 (.gpr 20#5)))) ∗
        memRegion (SP - 4128#64) 4096 ∗ R) := Satisfies.of_eq hs' (by ac_rfl)
    generalize hFr : ((A ↦ₛ rh) ∗ ((A + 48#64) ↦ₛ mid) ∗ (M ↦ₛ mac) ∗
        ((SP - 32#64) ↦ₛ (unpack64 (S0.readReg64 (.gpr 29#5)) ++ unpack64 (S0.readReg64 (.gpr 30#5)) ++
          unpack64 (S0.readReg64 (.gpr 19#5)) ++ unpack64 (S0.readReg64 (.gpr 20#5)))) ∗ R) = Fr
    have hsR' : m2 ⊨ ((A + 72#64) ↦ₛ rest) ∗ memRegion (SP - 4128#64) 4096 ∗ Fr := by
      rw [← hFr]; exact Satisfies.of_eq hsR (by ac_rfl)
    have eL : BitVec.ofNat 64 L.toNat = L := by simp
    -- +0x20: add x0, x0, x1
    have p1 := stepS' g7 hrun (f_20 hP (cl hCL0 g7))
      (ex_add_shift 0#5 0#5 1#5 (by decide) (by decide) (by decide) .LSL 0)
      (pc' := pl.base + 1092#64) (by simp [BitVec.add_assoc])
    -- +0x24: mov w2, #1
    have p2 := stepS' p1 hrun (f_24 hP (cl hCL0 p1)) (ex_movz32 2#5 (by decide) _)
      (pc' := pl.base + 1096#64) (by simp [BitVec.add_assoc])
    simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true, rA, n_lsl0] at p2
    -- +0x28: strb w2, [x0, #0x48]
    have ea : A + L + 0x48#64 = A + 72#64 + BitVec.ofNat 64 L.toNat := by rw [eL]; bv_omega
    have p3 := stepS' p2 hrun (f_28 hP (cl hCL0 p2))
      (ex_strb_off 2#5 0#5 (by decide) (by decide) 0x48#64
        (by simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true]; rw [ea];
            exact canWrite1_of_sat hsR' L.toNat (by omega)))
      (pc' := pl.base + 1100#64) (by simp [BitVec.add_assoc])
    simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true] at p3
    rw [ea] at p3
    have hw1 := sat_bytes_write hsR' L.toNat (by omega) 1#8
    have eb : BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 1#16)))
      = 1#8 := by decide
    rw [eb] at p3
    -- +0x2c: add x0, x1, #1
    have p4 := stepS' p3 hrun (f_2c hP (cl hCL0 p3)) (ex_add_imm 0#5 1#5 (by decide) (by decide) _)
      (pc' := pl.base + 1104#64) (by simp [BitVec.add_assoc])
    -- +0x30: cmp x0, #15
    have p5 := stepS' p4 hrun (f_30 hP (cl hCL0 p4)) (ex_cmp_imm 0#5 (by decide) _)
      (pc' := pl.base + 1108#64) (by simp [BitVec.add_assoc])
    simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true] at p5
    -- +0x34: b.hi +0x1c
    have p6 := stepS p5 hrun (f_34 hP (cl hCL0 p5)) (ex_bcond .HI _)
    rw [hi_cmp] at p6
    have eL1 : (L + BitVec.zeroExtend 64 1#12).toNat = L.toNat + 1 := by
      rw [BitVec.toNat_add]; simp; omega
    generalize hr5 : upd (upd (upd (upd (upd (upd (upd S0.regs.regs (29#5)
      (SP - 32#64 + BitVec.zeroExtend 64 0#12)) (20#5) M) (19#5) A) (1#5) L) (0#5) (A + L)) (2#5)
      (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 1#16)))) (0#5)
      (L + BitVec.zeroExtend 64 1#12) = r5 at p6
    have r5_19 : r5 19#5 = A := by rw [← hr5]; simp [upd_apply]
    have r5_20 : r5 20#5 = M := by rw [← hr5]; simp [upd_apply]
    have r5_1 : r5 1#5 = L := by rw [← hr5]; simp [upd_apply]
    have r5_cs : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat ≤ 28 → r5 k = S0.readReg64 (.gpr k) := by
      intro k hk1 hk2
      have e : k = BitVec.ofNat 5 k.toNat := by simp
      generalize hj : k.toNat = j at e hk1 hk2
      subst e
      rw [← hr5]
      interval_cases j <;> simp only [upd_apply, BitVec.reduceEq, BitVec.ofNat_eq_ofNat, ite_false] <;>
        exact (readGpr_eq S0 _ (by decide)).symm
    generalize hbuf : rest.take L.toNat ++ [1#8] ++ List.replicate (15 - L.toNat) 0#8 = buf
    have hlb : buf.length = 16 := by rw [← hbuf]; simp; omega
    -- both paths reach +0x50 with the buffer padded
    have h1136 : ∃ (s1 : State) (r' : BitVec 5 → BitVec 64) (ps' : PState) (m' : Memory)
        (v' : BitVec 5 → BitVec 128), s1.status = .Running ∧
        Steps (P pl ex) S0 (mkS s1 (pl.base + 1136#64) r' (SP - 32#64) ps' m' v') ∧
        r' 19#5 = A ∧ r' 20#5 = M ∧
        (∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat ≤ 28 → r' k = S0.readReg64 (.gpr k)) ∧
        VRegFile.calleeSaved ⟨v'⟩ = calleeSavedVRegs S0 ∧
        m' ⊨ ((A + 72#64) ↦ₛ (buf ++ rest.drop 16)) ∗ memRegion (SP - 4128#64) 4096 ∗ Fr := by
      by_cases h15 : L.toNat = 15
      · have hc : decide ((BitVec.zeroExtend 64 15#12).toNat < (L + BitVec.zeroExtend 64 1#12).toNat)
            = true := by simp only [decide_eq_true_eq, eL1, h15]; decide
        rw [hc, if_pos rfl, show pl.base + 1108#64 + 28#64 = pl.base + 1136#64 by
          rw [BitVec.add_assoc]; rfl] at p6
        refine ⟨S0, r5, _, _, _, hrun, p6, r5_19, r5_20, r5_cs, rfl, ?_⟩
        rw [← hbuf, h15, ← set15 rest hl3]; rw [h15] at hw1; exact hw1
      · have hc : decide ((BitVec.zeroExtend 64 15#12).toNat < (L + BitVec.zeroExtend 64 1#12).toNat)
            = false := by simp only [decide_eq_false_iff_not, eL1]; simp; omega
        rw [hc, if_neg (by decide), show pl.base + 1108#64 + 4#64 = pl.base + 1112#64 by
          rw [BitVec.add_assoc]; rfl] at p6
        -- +0x38: add x0, x1, #0x49
        have q1 := stepS' p6 hrun (f_38 hP (cl hCL0 p6)) (ex_add_imm 0#5 1#5 (by decide) (by decide) _)
          (pc' := pl.base + 1116#64) (by simp [BitVec.add_assoc])
        -- +0x3c: mov x2, #15
        have q2 := stepS' q1 hrun (f_3c hP (cl hCL0 q1)) (ex_movz64 2#5 (by decide) _)
          (pc' := pl.base + 1120#64) (by simp [BitVec.add_assoc])
        -- +0x40: add x0, x19, x0
        have q3 := stepS' q2 hrun (f_40 hP (cl hCL0 q2))
          (ex_add_shift 0#5 19#5 0#5 (by decide) (by decide) (by decide) .LSL 0)
          (pc' := pl.base + 1124#64) (by simp [BitVec.add_assoc])
        -- +0x44: sub x2, x2, x1
        have q4 := stepS' q3 hrun (f_44 hP (cl hCL0 q3))
          (ex_sub_shift 2#5 2#5 1#5 (by decide) (by decide) (by decide))
          (pc' := pl.base + 1128#64) (by simp [BitVec.add_assoc])
        -- +0x48: mov w1, #0
        have q5 := stepS' q4 hrun (f_48 hP (cl hCL0 q4)) (ex_movz32 1#5 (by decide) _)
          (pc' := pl.base + 1132#64) (by simp [BitVec.add_assoc])
        -- +0x4c: bl memset
        have q6 := stepS q5 hrun (f_4c hP (cl hCL0 q5)) (ex_bl _)
        rw [show pl.base + 1132#64 + (pl.ρ "memset" - (pl.base + 1132#64)) = pl.ρ "memset" by
          bv_omega] at q6
        simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true, r5_1, r5_19, n_lsl0] at q6
        generalize hrL : rest.set L.toNat 1#8 = restL at hw1
        have hlL : restL.length = 24 := by rw [← hrL]; simp [hl3]
        have esplit : restL = restL.take (L.toNat + 1) ++
            (restL.drop (L.toNat + 1)).take (15 - L.toNat) ++ restL.drop 16 := by
          rw [List.append_assoc, show restL.drop 16 = (restL.drop (L.toNat + 1)).drop (15 - L.toNat) by
            rw [List.drop_drop]; congr 1; omega, List.take_append_drop, List.take_append_drop]
        rw [esplit] at hw1
        obtain ⟨sf, gsf, hrunf, hpcf, hspf, hcsf, hmf⟩ := memset_call hrun q6
          (by simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true]
              simp only [List.length_take, hlL]; rw [← eL]; bv_omega)
          (by simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true]; rfl)
          (by simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true]
              simp only [List.length_take, List.length_drop, hlL]
              rw [BitVec.toNat_sub]; simp; omega)
          hal32 hw1 hfm hatm
        obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, -, cv⟩ := hcsf
        have sf19 : sf.regs.regs 19#5 = A := by
          rw [← readGpr_eq sf _ (by decide), c19]; simp [upd_apply, r5_19]
        have sf20 : sf.regs.regs 20#5 = M := by
          rw [← readGpr_eq sf _ (by decide), c20]; simp [upd_apply, r5_20]
        have hpc' : sf.pc = pl.base + 1136#64 := by
          rw [hpcf]; simp only [upd_apply, BitVec.reduceEq, ite_true]; rw [BitVec.add_assoc]; rfl
        refine ⟨sf, sf.regs.regs, sf.pstate, sf.mem, sf.vregs.regs, hrunf, ?_, sf19, sf20, ?_, ?_, ?_⟩
        · rw [← hpc', ← hspf, mkS_self]; exact gsf
        · intro k hk1 hk2
          have e : k = BitVec.ofNat 5 k.toNat := by simp
          generalize hj : k.toNat = j at e hk1 hk2
          subst e
          interval_cases j <;> rw [← readGpr_eq sf _ (by decide), ← r5_cs _ (by decide) (by decide)] <;>
            (first | rw [c21] | rw [c22] | rw [c23] | rw [c24] | rw [c25] | rw [c26] | rw [c27] | rw [c28]) <;>
            simp [upd_apply]
        · show calleeSavedVRegs sf = calleeSavedVRegs S0
          rw [cv]; rfl
        · have e1 : restL.take (L.toNat + 1) = rest.take L.toNat ++ [1#8] := by
            rw [← hrL]; exact set_take rest L.toNat _ (by omega)
          have e2 : restL.drop 16 = rest.drop 16 := by
            rw [← hrL]; exact List.drop_set_of_lt (by omega)
          have e3 : ((restL.drop (L.toNat + 1)).take (15 - L.toNat)).length = 15 - L.toNat := by
            simp [hlL]; omega
          rw [e1, e2, e3] at hmf
          rw [← hbuf]; exact hmf
    obtain ⟨s1, r6, ps6, m6, v6, hrun1, q1, r6_19, r6_20, r6_cs, hv6, hs6⟩ := h1136
    -- +0x50: mov w0, #1
    have q2 := stepS' q1 hrun1 (f_50 hP (cl hCL0 q1)) (ex_movz32 0#5 (by decide) _)
      (pc' := pl.base + 1140#64) (by simp [BitVec.add_assoc])
    -- +0x54: strb w0, [x19, #0x58]
    have hw2 := sat_bytes_write hs6 16 (by simp [hlb]; omega) 1#8
    have e58 : A + 0x58#64 = A + 72#64 + BitVec.ofNat 64 16 := by bv_omega
    have q3 := stepS' q2 hrun1 (f_54 hP (cl hCL0 q2))
      (ex_strb_off 0#5 19#5 (by decide) (by decide) 0x58#64
        (by simp only [upd_apply, BitVec.reduceEq, ite_false]; rw [r6_19, e58];
            exact canWrite1_of_sat hs6 16 (by simp [hlb]; omega)))
      (pc' := pl.base + 1144#64) (by simp [BitVec.add_assoc])
    simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true, r6_19, e58] at q3
    rw [show BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 1#16)))
      = 1#8 by decide] at q3
    -- +0x58: add x1, x19, #0x48
    have q4 := stepS' q3 hrun1 (f_58 hP (cl hCL0 q3)) (ex_add_imm 1#5 19#5 (by decide) (by decide) _)
      (pc' := pl.base + 1148#64) (by simp [BitVec.add_assoc])
    -- +0x5c: mov x0, x19
    have q5 := stepS' q4 hrun1 (f_5c hP (cl hCL0 q4)) (ex_mov 0#5 19#5 (by decide) (by decide))
      (pc' := pl.base + 1152#64) (by simp [BitVec.add_assoc])
    -- +0x60: mov x2, #16
    have q6 := stepS' q5 hrun1 (f_60 hP (cl hCL0 q5)) (ex_movz64 2#5 (by decide) _)
      (pc' := pl.base + 1156#64) (by simp [BitVec.add_assoc])
    -- +0x64: bl poly1305_blocks
    have q7 := stepS q6 hrun1 (f_64 hP (cl hCL0 q6)) (ex_bl _)
    rw [show pl.base + 1156#64 + 0xfffffffffffffd1c#64 = pl.base + 416#64 by bv_omega] at q7
    simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true, r6_19] at q7
    have hset : (buf ++ List.drop 16 rest).set 16 1#8 = buf ++ [1#8] ++ rest.drop 17 := by
      rw [List.set_append_right _ _ (by omega), hlb, show 16 - 16 = 0 from rfl,
        List.drop_eq_getElem_cons (by omega : 16 < rest.length), List.set_cons_zero]
      simp
    rw [hset] at hw2
    generalize hrc : upd (upd (upd (upd (upd r6 (0#5) (BitVec.zeroExtend 64 (BitVec.truncate 32
      (BitVec.zeroExtend 64 1#16)))) (1#5) (A + BitVec.zeroExtend 64 0x048#12)) (0#5) A) (2#5)
      (BitVec.zeroExtend 64 16#16)) (30#5) (pl.base + 1156#64 + 4#64) = rc at q7
    generalize hm7 : m6.write8 (A + 72#64 + 16#64) 1#8 = m7 at q7 hw2
    have rc0 : rc 0#5 = A := by rw [← hrc]; simp [upd_apply]
    have rc1 : rc 1#5 = A + 72#64 := by rw [← hrc]; simp [upd_apply]
    have rc2 : (rc 2#5).toNat = 16 := by rw [← hrc]; simp [upd_apply]
    have rc19 : rc 19#5 = A := by rw [← hrc]; simp [upd_apply, r6_19]
    have rc20 : rc 20#5 = M := by rw [← hrc]; simp [upd_apply, r6_20]
    have rc30 : rc 30#5 = pl.base + 1160#64 := by
      rw [← hrc]; simp [upd_apply]; rw [BitVec.add_assoc]; rfl
    have rccs : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat ≤ 28 → rc k = S0.readReg64 (.gpr k) := by
      intro k hk1 hk2
      have h0 : k ≠ 0#5 := fun e => by subst e; simp at hk1
      have h1 : k ≠ 1#5 := fun e => by subst e; simp at hk1
      have h2 : k ≠ 2#5 := fun e => by subst e; simp at hk1
      have h30 : k ≠ 30#5 := fun e => by subst e; simp at hk2
      rw [← hrc]; simp [upd_apply, h0, h1, h2, h30]; exact r6_cs k hk1 hk2
    generalize hsc : mkS s1 (pl.base + 416#64) rc (SP - 32#64) ps6 m7 v6 = sc at q7
    have sreg : ∀ k : BitVec 5, k ≠ 31#5 → sc.readReg64 (.gpr k) = rc k := by
      intro k hk; rw [← hsc]; simp [hk]
    -- blocks' precondition, with everything else as frame
    have eb3 : ((A + 72#64) ↦ₛ (buf ++ [1#8] ++ rest.drop 17)) =
        ((A + 72#64) ↦ₛ buf) ∗ ((A + 88#64) ↦ₛ [1#8]) ∗ ((A + 89#64) ↦ₛ rest.drop 17) := by
      rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append, hlb]
      simp only [List.length_singleton]
      rw [show A + 72#64 + BitVec.ofNat 64 16 = A + 88#64 by bv_omega,
        show A + 88#64 + BitVec.ofNat 64 1 = A + 89#64 by bv_omega]
    rw [eb3, ← hFr] at hw2
    have hpreC : sc.mem ⊨ blocksW.pre (false, rh, 1#8, buf) sc ∗
        (((A + 48#64) ↦ₛ mid) ∗ ((A + 89#64) ↦ₛ rest.drop 17) ∗ (M ↦ₛ mac) ∗
        ((SP - 32#64) ↦ₛ (unpack64 (S0.readReg64 (.gpr 29#5)) ++ unpack64 (S0.readReg64 (.gpr 30#5)) ++
          unpack64 (S0.readReg64 (.gpr 19#5)) ++ unpack64 (S0.readReg64 (.gpr 20#5)))) ∗
        memRegion (SP - 4128#64) 4096 ∗ R) := by
      simp only [blocksW, blocksSpec, bytesIn, Bool.false_eq_true, if_false]
      rw [sepConj_assoc, sat_pure_sep, sepConj_assoc, sat_pure_sep]
      refine ⟨by rw [hlb], ⟨hok', by rw [Reg.x2, sreg _ (by decide), rc2, hlb], by omega⟩, ?_⟩
      rw [Reg.x0, Reg.x1, sreg _ (by decide), sreg _ (by decide), rc0, rc1,
        show sc.mem = m7 by rw [← hsc]; rfl]
      exact Satisfies.of_eq hw2 (by ac_rfl)
    have halC : sc.spAligned = true := by rw [← hsc]; simp [hal32]
    obtain ⟨sf, hsf, hout⟩ := hB (false, rh, 1#8, buf) _ sc (by rw [← hsc]; rfl)
      (by rw [← hsc]; exact hrun1) hpreC halC (cl hCL0 q7)
    rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcsf⟩, hpost⟩ | ⟨_, hp⟩ | ⟨c, _, hp⟩ | ⟨_, hp⟩
    rotate_left
    · exact absurd hp not_sat_false'
    · exact absurd hp not_sat_false'
    · exact absurd hp not_sat_false'
    -- blocks' postcondition
    simp only [blocksW, blocksSpec, bytesIn, Bool.false_eq_true, if_false] at hpost
    rw [Reg.x0, Reg.x1, sreg 0#5 (by decide), sreg 1#5 (by decide), rc0, rc1] at hpost
    rw [sepConj_assoc, sat_pure_sep] at hpost
    obtain ⟨-, hpost⟩ := hpost
    rw [sepConj_assoc, sepExists_sepConj, sat_sepExists] at hpost
    obtain ⟨rh', hpost⟩ := hpost
    rw [sepConj_comm (A ↦ₛ rh'), sepConj_assoc, sat_pure_sep] at hpost
    obtain ⟨⟨hok2, -, hacc⟩, hpost'⟩ := hpost
    have hspf' : sf.sp = SP - 32#64 := by rw [hspf, ← hsc]; rfl
    have hpcf' : sf.pc = pl.base + 1160#64 := by
      rw [hpcf, Reg.lr, sreg _ (by decide), rc30]
    have gsf := Steps.trans' q7 hsf
    have em : mkS sf (pl.base + 1160#64) sf.regs.regs (SP - 32#64) sf.pstate sf.mem sf.vregs.regs = sf := by
      rw [← hpcf', ← hspf']; exact mkS_self sf
    rw [← em] at gsf
    obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, cfp, cv⟩ := hcsf
    have sf20 : sf.regs.regs 20#5 = M := by
      rw [← readGpr_eq sf _ (by decide), c20, sreg _ (by decide), rc20]
    have sf19 : sf.regs.regs 19#5 = A := by
      rw [← readGpr_eq sf _ (by decide), c19, sreg _ (by decide), rc19]
    have hl3' : (buf ++ [1#8] ++ rest.drop 17).length = 24 := by simp [hlb, hl3]
    have hq : sf.mem ⊨ (A ↦ₛ rh') ∗ ((A + 48#64) ↦ₛ mid) ∗ ((A + 72#64) ↦ₛ (buf ++ [1#8] ++ rest.drop 17)) ∗
        (M ↦ₛ mac) ∗
        ((SP - 32#64) ↦ₛ (unpack64 (S0.readReg64 (.gpr 29#5)) ++ unpack64 (S0.readReg64 (.gpr 30#5)) ++
          unpack64 (S0.readReg64 (.gpr 19#5)) ++ unpack64 (S0.readReg64 (.gpr 20#5)))) ∗
        memRegion (SP - 4128#64) 4096 ∗ R := by
      rw [eb3]; exact Satisfies.of_eq hpost' (by ac_rfl)
    refine join (rh := rh') (mid := mid) (rest := buf ++ [1#8] ++ rest.drop 17) hP hCL0 hrunf gsf
      sf19 sf20 hA hM hSP hal32 halS ?_ ?_ ⟨hok2.1, hl2, hl3', hl16⟩ hok2 ?_ hq hf hat
    · intro k hk1 hk2
      have e : k = BitVec.ofNat 5 k.toNat := by simp
      generalize hj : k.toNat = j at e hk1 hk2
      subst e
      interval_cases j <;> rw [← readGpr_eq sf _ (by decide)] <;>
        (first | rw [c21] | rw [c22] | rw [c23] | rw [c24] | rw [c25] | rw [c26] | rw [c27] | rw [c28]) <;>
        rw [sreg _ (by decide)] <;> exact rccs _ (by decide) (by decide)
    · show calleeSavedVRegs sf = calleeSavedVRegs S0
      rw [cv, ← hsc]; exact hv6
    · -- the tag
      have hu : u64At st 64 = L.toNat := vL.symm
      have hne : L.toNat ≠ 0 := by omega
      unfold finishTag
      simp only [hu, if_neg hne]
      rw [hacc, blocksAcc16 _ _ _ hlb, ← hbuf, leBytes_append (rest.take L.toNat ++ [1#8]),
        leBytes_zeros, Nat.mul_zero, Nat.add_zero, Nat.mod_mod, ← hrh, ← hmid, ← hrest,
        List.take_take, show min 16 24 = 16 from rfl,
        limbVal_take st rLimb (fun i hi => rLimb_take' st i hi),
        limbVal_take st hLimb (fun i hi => hLimb_take' st i hi), Nat.mod_mod]

end Poly1305Debian.FD

end
end

section
section
/-! # Debian's `poly1305_finish` meets `finishSpec` under `internalOk`, given `poly1305_blocks`'s contract

Only the 16-byte call `poly1305_blocks(st, st->buffer, 16)` is used from the blocks contract. -/

set_option autoImplicit false

namespace Poly1305Debian.FD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj

theorem finish_of_blocksW
    (hB : internalOk "poly1305_blocks [libsodium_la_poly1305_donna]" (fun _ => blocksW)) :
    internalOk "poly1305_finish [libsodium_la_poly1305_donna]" (fun _ => finishSpec) := by
  refine ⟨by decide, fun pl hP hG externs hMz hMs hL => ?_⟩
  obtain ⟨f, hfx, hf⟩ := hMz
  obtain ⟨fm, hfmx, hfm⟩ := hMs
  have hB' := hB.2 pl hP hG externs ⟨f, hfx, hf⟩ ⟨fm, hfmx, hfm⟩ hL
  rw [fnAddr_blocks] at hB'
  rw [fnAddr_finish]
  rintro ⟨st, mac⟩ R S0 hpc hrun hpre hal hCL0
  exact finish_main hP hf ((hookAt_of_linkOk hL "sodium_memzero" (by decide)).trans hfx) hfm
    ((hookAt_of_linkOk hL "memset" (by decide)).trans hfmx) hB' st mac R S0 hpc hrun hpre hal hCL0

end Poly1305Debian.FD

namespace Poly1305Debian.FD

end Poly1305Debian.FD

end
end

section
section
namespace Poly1305Debian

open Arm64

theorem internalOk_poly1305_finish_of_blocks_whole_dev :
    internalOk "poly1305_blocks [libsodium_la_poly1305_donna]"
        (fun _ => { blocksSpec with
          pre := fun g s0 =>
            match g with
            | (_, _, _, m) => ⌜m.length % 16 = 0⌝ ∗ blocksSpec.pre g s0 }) →
      internalOk "poly1305_finish [libsodium_la_poly1305_donna]" (fun _ => finishSpec) :=
  FD.finish_of_blocksW

end Poly1305Debian

end
end

section
open Poly1305Debian

open Arm64


theorem solution :
    internalOk "poly1305_blocks [libsodium_la_poly1305_donna]"
        (fun _ => { blocksSpec with
          pre := fun g s0 =>
            match g with
            | (_, _, _, m) => ⌜m.length % 16 = 0⌝ ∗ blocksSpec.pre g s0 }) →
      internalOk "poly1305_finish [libsodium_la_poly1305_donna]" (fun _ => finishSpec) := by
  apply Poly1305Debian.internalOk_poly1305_finish_of_blocks_whole_dev <;> assumption

end
