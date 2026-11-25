-- Prove2me | solution 1 for Poly1305Debian.internalOk_poly1305_update_of_blocks_whole
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-25T21:08:23.219405+00:00
-- url     : https://prove2.me/submissions/d9e64503-017a-41cc-859e-02aeb6b38ab4

import Definitions.Def_Poly1305Debian_PlacedObj
import Definitions.Def_Poly1305Debian_Spec
import Mathlib.Tactic.IntervalCases
import Definitions.Def_Link_LinkOk
import Theorems.Thm_Arm64Facts_steps_codeLoaded_v2

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
theorem holds_pointsTo8RO_iff {a : BitVec 64} {v : BitVec 8} {h : Heap} :
    (pointsTo8RO a v).holds h ↔ h = Heap.singletonRO a v := Iff.rfl

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

theorem Entails.trans {P Q R : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ R) : P ⊢ R :=
  SepProp.entails_iff.mpr fun h hp => SepProp.entails_iff.mp h2 h (SepProp.entails_iff.mp h1 h hp)

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

theorem bytesRO_phys : ∀ {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap},
    (a ↦ᵣ bs).holds h → ∀ (j : Nat) (hj : j < bs.length),
      h.phys (a + BitVec.ofNat 64 j) = some (.ro bs[j])
  | _, [], _, _, j, hj => by simp at hj
  | a, b :: bs, h, hh, j, hj => by
    obtain ⟨h1, h2, hd, rfl, h1e, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
    rw [holds_pointsTo8RO_iff] at h1e; subst h1e
    cases j with
    | zero => simp [Heap.union, Heap.singletonRO]
    | succ j =>
      have ih := bytesRO_phys h2h j (by simp at hj; omega)
      have ha : a + BitVec.ofNat 64 (j + 1) = a + 1#64 + BitVec.ofNat 64 j := by
        rw [BitVec.add_assoc]; congr 1; bv_omega
      rw [ha]
      by_cases hne : a + 1#64 + BitVec.ofNat 64 j = a
      · -- both sides own the same read-only cell: the values agree by disjointness
        rcases hd.1 a with h0 | h0 | ⟨c, h1c, h2c⟩
        · simp [Heap.singletonRO] at h0
        · rw [← hne] at h0; rw [ih] at h0; cases h0
        · simp only [Heap.singletonRO, if_true, Option.some.injEq, HeapCell.ro.injEq] at h1c
          rw [← hne] at h2c; rw [ih] at h2c
          simp only [Option.some.injEq, HeapCell.ro.injEq] at h2c
          simp only [Heap.union, Heap.singletonRO, hne, if_true, List.getElem_cons_succ]
          rw [h1c, h2c]
      · simp only [Heap.union, Heap.singletonRO, hne, if_false, ih, List.getElem_cons_succ]

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

theorem sat_bytesRO_read {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ᵣ bs) ∗ F) (j : Nat) (hj : j < bs.length) :
    m.read8 (a + BitVec.ofNat 64 j) = bs[j] ∧ (m.perm (a + BitVec.ofNat 64 j)).r = true ∧
      m.isLazyFree (a + BitVec.ofNat 64 j) = false := by
  obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
  obtain ⟨h1, h2, hd, rfl, h1h, _⟩ := SepProp.holds_sepConj_iff.mp hh
  have hp := bytesRO_phys h1h j hj
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

theorem pointsToBytesRO_split (a : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (hn : n ≤ bs.length) :
    (a ↦ᵣ bs) = (a ↦ᵣ bs.take n) ∗ ((a + BitVec.ofNat 64 n) ↦ᵣ bs.drop n) := by
  have h := pointsToBytesRO_append a (bs.take n) (bs.drop n)
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

namespace Poly1305Debian.UD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

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

theorem mkS_self (s : State) : mkS s s.pc s.regs.regs s.sp s.pstate s.mem s.vregs.regs = s := rfl

end Poly1305Debian.UD

end
end

section
section
/-! # Execution by backward chaining, and instruction fetch in the placed libsodium library

`P pl ex` is the placed program with hook table `ex`. No hook has its entry point inside the text
block (`hook_none_in`), so inside the block `Step` is fetch-and-execute. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.UD

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj

abbrev P (pl : Placement) (ex : String → Option (State → State)) : Program :=
  libsodiumDebianOnetimeauthLib.program pl ex

/-! ## Reaching a final state -/

def Reach (p : Program) (s : State) (Q : State → Prop) : Prop := ∃ sf, Steps p s sf ∧ Q sf

theorem Steps.trans' {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Steps p b c) :
    Steps p a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

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

end Poly1305Debian.UD

end
end

section
section
/-! # One lemma per instruction shape of `poly1305_finish`, on abstract states `mkS`

Some lemmas are copied from the x25519 `G` tree (`Solutions/X25519DalekField/G/Steps.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.UD

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

theorem ex_ldr64_gpr (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hr : m.canRead (r n + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a (m.read64 (r n + off))) sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hr, ha, hn,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_strb_reg (t n k : BitVec 5) (ht : t ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (hw : m.canWrite (r n + r k) 1 = true) :
    execInstWithSvc svc (.str .B8 (.gpr t) (.RegOffset (.gpr n) (.gpr k) .UXTX 0))
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write8 (r n + r k) ((r t).truncate 8)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, extendVal, hw, ht, hn,
    hk, Memory.writeSized, AddrMode.baseReg]

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

theorem ex_and_imm (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm .W64 .AND (.gpr d) (.gpr n) mask) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n &&& mask)) sp ps m v := by
  simp [execInstWithSvc, evalLogical, State.readReg, State.writeReg, hd, hn]

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
theorem ne_cmp (x y : BitVec 64) :
    ConditionHolds .NE (AddWithCarry64 x (~~~y) true).2 = decide (x ≠ y) := by
  simp only [ConditionHolds, res_eq]; simp

end Poly1305Debian.UD

end
end

section
section
/-! # 64-bit reads and writes inside owned byte lists; stack regions

`memRegion_split`, `memRegion_merge`, `pack64` and `unpack64_pack64` are copied from the x25519
`G` tree (`Solutions/X25519DalekField/G/Mem.lean`, `Solutions/X25519DalekEdwards/Dbl/Frame.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.UD

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

end Poly1305Debian.UD

end
end

section
section
/-! # The instruction at each address of Debian's `poly1305_update` (text offsets 0x2b0..0x3a8)

Generated from `decode (wordAt off)`; `poly1305_update` has no relocations (its two `bl` go to
`poly1305_blocks` in the same object). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.UD

open Arm64 Arm64.Obj

section
variable {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
  (hP : libsodiumDebianOnetimeauthLib.Placeable pl) (hCL : (P pl ex).CodeLoaded m)
include hP hCL

theorem f_0 : (P pl ex).fetchMem m (pl.base + 688#64) = some (Arm64.Instr.hint 0x19#7) := by
  rw [show pl.base + 688#64 = pl.base + BitVec.ofNat 64 688 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_4 : (P pl ex).fetchMem m (pl.base + 692#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xffffffffffffffe0#64)) := by
  rw [show pl.base + 692#64 = pl.base + BitVec.ofNat 64 692 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_8 : (P pl ex).fetchMem m (pl.base + 696#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 696#64 = pl.base + BitVec.ofNat 64 696 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c : (P pl ex).fetchMem m (pl.base + 700#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 700#64 = pl.base + BitVec.ofNat 64 700 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_10 : (P pl ex).fetchMem m (pl.base + 704#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.sp) 0x000#12 false) := by
  rw [show pl.base + 704#64 = pl.base + BitVec.ofNat 64 704 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_14 : (P pl ex).fetchMem m (pl.base + 708#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x06#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000040#64)) := by
  rw [show pl.base + 708#64 = pl.base + BitVec.ofNat 64 708 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_18 : (P pl ex).fetchMem m (pl.base + 712#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x06#5) 0x0000000000000074#64) := by
  rw [show pl.base + 712#64 = pl.base + BitVec.ofNat 64 712 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1c : (P pl ex).fetchMem m (pl.base + 716#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0010#16 0) := by
  rw [show pl.base + 716#64 = pl.base + BitVec.ofNat 64 716 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_20 : (P pl ex).fetchMem m (pl.base + 720#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x06#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 720#64 = pl.base + BitVec.ofNat 64 720 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_24 : (P pl ex).fetchMem m (pl.base + 724#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 724#64 = pl.base + BitVec.ofNat 64 724 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_28 : (P pl ex).fetchMem m (pl.base + 728#64) = some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSEL) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x02#5) (Arm64.CondCode.LS)) := by
  rw [show pl.base + 728#64 = pl.base + BitVec.ofNat 64 728 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_2c : (P pl ex).fetchMem m (pl.base + 732#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x01#5) 0x0000000000000024#64) := by
  rw [show pl.base + 732#64 = pl.base + BitVec.ofNat 64 732 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_30 : (P pl ex).fetchMem m (pl.base + 736#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x06#5) 0x048#12 false) := by
  rw [show pl.base + 736#64 = pl.base + BitVec.ofNat 64 736 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_34 : (P pl ex).fetchMem m (pl.base + 740#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x03#5) 0x0000#16 0) := by
  rw [show pl.base + 740#64 = pl.base + BitVec.ofNat 64 740 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_38 : (P pl ex).fetchMem m (pl.base + 744#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x05#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 744#64 = pl.base + BitVec.ofNat 64 744 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_3c : (P pl ex).fetchMem m (pl.base + 748#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x02#5) (Arm64.AddrMode.RegOffset (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ExtendType.UXTX) 0)) := by
  rw [show pl.base + 748#64 = pl.base + BitVec.ofNat 64 748 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_40 : (P pl ex).fetchMem m (pl.base + 752#64) = some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x02#5) (Arm64.AddrMode.RegOffset (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ExtendType.UXTX) 0)) := by
  rw [show pl.base + 752#64 = pl.base + BitVec.ofNat 64 752 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_44 : (P pl ex).fetchMem m (pl.base + 756#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) 0x001#12 false) := by
  rw [show pl.base + 756#64 = pl.base + BitVec.ofNat 64 756 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_48 : (P pl ex).fetchMem m (pl.base + 760#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 760#64 = pl.base + BitVec.ofNat 64 760 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_4c : (P pl ex).fetchMem m (pl.base + 764#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0xfffffffffffffff0#64) := by
  rw [show pl.base + 764#64 = pl.base + BitVec.ofNat 64 764 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_50 : (P pl ex).fetchMem m (pl.base + 768#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 768#64 = pl.base + BitVec.ofNat 64 768 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_54 : (P pl ex).fetchMem m (pl.base + 772#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x06#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000040#64)) := by
  rw [show pl.base + 772#64 = pl.base + BitVec.ofNat 64 772 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_58 : (P pl ex).fetchMem m (pl.base + 776#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x06#5) 0x00f#12 false) := by
  rw [show pl.base + 776#64 = pl.base + BitVec.ofNat 64 776 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_5c : (P pl ex).fetchMem m (pl.base + 780#64) = some (Arm64.Instr.bCond (Arm64.CondCode.HI) 0x0000000000000010#64) := by
  rw [show pl.base + 780#64 = pl.base + BitVec.ofNat 64 780 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_60 : (P pl ex).fetchMem m (pl.base + 784#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000020#64)) := by
  rw [show pl.base + 784#64 = pl.base + BitVec.ofNat 64 784 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_64 : (P pl ex).fetchMem m (pl.base + 788#64) = some (Arm64.Instr.hint 0x1d#7) := by
  rw [show pl.base + 788#64 = pl.base + BitVec.ofNat 64 788 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_68 : (P pl ex).fetchMem m (pl.base + 792#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) := by
  rw [show pl.base + 792#64 = pl.base + BitVec.ofNat 64 792 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_6c : (P pl ex).fetchMem m (pl.base + 796#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 796#64 = pl.base + BitVec.ofNat 64 796 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_70 : (P pl ex).fetchMem m (pl.base + 800#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 800#64 = pl.base + BitVec.ofNat 64 800 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_74 : (P pl ex).fetchMem m (pl.base + 804#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x02#5) 0x0010#16 0) := by
  rw [show pl.base + 804#64 = pl.base + BitVec.ofNat 64 804 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_78 : (P pl ex).fetchMem m (pl.base + 808#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x00#5) 0x048#12 false) := by
  rw [show pl.base + 808#64 = pl.base + BitVec.ofNat 64 808 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_7c : (P pl ex).fetchMem m (pl.base + 812#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) := by
  rw [show pl.base + 812#64 = pl.base + BitVec.ofNat 64 812 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_80 : (P pl ex).fetchMem m (pl.base + 816#64) = some (Arm64.Instr.bl 0xfffffffffffffe70#64) := by
  rw [show pl.base + 816#64 = pl.base + BitVec.ofNat 64 816 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_84 : (P pl ex).fetchMem m (pl.base + 820#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.xzr) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000040#64)) := by
  rw [show pl.base + 820#64 = pl.base + BitVec.ofNat 64 820 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_88 : (P pl ex).fetchMem m (pl.base + 824#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) := by
  rw [show pl.base + 824#64 = pl.base + BitVec.ofNat 64 824 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_8c : (P pl ex).fetchMem m (pl.base + 828#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x04#5) 0x00f#12 false) := by
  rw [show pl.base + 828#64 = pl.base + BitVec.ofNat 64 828 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_90 : (P pl ex).fetchMem m (pl.base + 832#64) = some (Arm64.Instr.bCond (Arm64.CondCode.HI) 0x0000000000000048#64) := by
  rw [show pl.base + 832#64 = pl.base + BitVec.ofNat 64 832 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_94 : (P pl ex).fetchMem m (pl.base + 836#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x04#5) 0xffffffffffffffcc#64) := by
  rw [show pl.base + 836#64 = pl.base + BitVec.ofNat 64 836 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_98 : (P pl ex).fetchMem m (pl.base + 840#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x05#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000040#64)) := by
  rw [show pl.base + 840#64 = pl.base + BitVec.ofNat 64 840 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_9c : (P pl ex).fetchMem m (pl.base + 844#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x03#5) 0x0000#16 0) := by
  rw [show pl.base + 844#64 = pl.base + BitVec.ofNat 64 844 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a0 : (P pl ex).fetchMem m (pl.base + 848#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x05#5) 0x048#12 false) := by
  rw [show pl.base + 848#64 = pl.base + BitVec.ofNat 64 848 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a4 : (P pl ex).fetchMem m (pl.base + 852#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 852#64 = pl.base + BitVec.ofNat 64 852 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a8 : (P pl ex).fetchMem m (pl.base + 856#64) = some (Arm64.Instr.nop) := by
  rw [show pl.base + 856#64 = pl.base + BitVec.ofNat 64 856 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ac : (P pl ex).fetchMem m (pl.base + 860#64) = some (Arm64.Instr.nop) := by
  rw [show pl.base + 860#64 = pl.base + BitVec.ofNat 64 860 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b0 : (P pl ex).fetchMem m (pl.base + 864#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.RegOffset (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ExtendType.UXTX) 0)) := by
  rw [show pl.base + 864#64 = pl.base + BitVec.ofNat 64 864 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b4 : (P pl ex).fetchMem m (pl.base + 868#64) = some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.RegOffset (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ExtendType.UXTX) 0)) := by
  rw [show pl.base + 868#64 = pl.base + BitVec.ofNat 64 868 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b8 : (P pl ex).fetchMem m (pl.base + 872#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) 0x001#12 false) := by
  rw [show pl.base + 872#64 = pl.base + BitVec.ofNat 64 872 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_bc : (P pl ex).fetchMem m (pl.base + 876#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 876#64 = pl.base + BitVec.ofNat 64 876 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c0 : (P pl ex).fetchMem m (pl.base + 880#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0xfffffffffffffff0#64) := by
  rw [show pl.base + 880#64 = pl.base + BitVec.ofNat 64 880 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c4 : (P pl ex).fetchMem m (pl.base + 884#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x04#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 884#64 = pl.base + BitVec.ofNat 64 884 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c8 : (P pl ex).fetchMem m (pl.base + 888#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x05#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000040#64)) := by
  rw [show pl.base + 888#64 = pl.base + BitVec.ofNat 64 888 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_cc : (P pl ex).fetchMem m (pl.base + 892#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000020#64)) := by
  rw [show pl.base + 892#64 = pl.base + BitVec.ofNat 64 892 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d0 : (P pl ex).fetchMem m (pl.base + 896#64) = some (Arm64.Instr.hint 0x1d#7) := by
  rw [show pl.base + 896#64 = pl.base + BitVec.ofNat 64 896 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d4 : (P pl ex).fetchMem m (pl.base + 900#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) := by
  rw [show pl.base + 900#64 = pl.base + BitVec.ofNat 64 900 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d8 : (P pl ex).fetchMem m (pl.base + 904#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) 0xfffffffffffffff0#64) := by
  rw [show pl.base + 904#64 = pl.base + BitVec.ofNat 64 904 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_dc : (P pl ex).fetchMem m (pl.base + 908#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x12#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 908#64 = pl.base + BitVec.ofNat 64 908 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e0 : (P pl ex).fetchMem m (pl.base + 912#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) := by
  rw [show pl.base + 912#64 = pl.base + BitVec.ofNat 64 912 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e4 : (P pl ex).fetchMem m (pl.base + 916#64) = some (Arm64.Instr.bl 0xfffffffffffffe0c#64) := by
  rw [show pl.base + 916#64 = pl.base + BitVec.ofNat 64 916 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e8 : (P pl ex).fetchMem m (pl.base + 920#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) := by
  rw [show pl.base + 920#64 = pl.base + BitVec.ofNat 64 920 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ec : (P pl ex).fetchMem m (pl.base + 924#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 924#64 = pl.base + BitVec.ofNat 64 924 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f0 : (P pl ex).fetchMem m (pl.base + 928#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 928#64 = pl.base + BitVec.ofNat 64 928 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f4 : (P pl ex).fetchMem m (pl.base + 932#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x04#5) 0xffffffffffffff6c#64) := by
  rw [show pl.base + 932#64 = pl.base + BitVec.ofNat 64 932 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f8 : (P pl ex).fetchMem m (pl.base + 936#64) = some (Arm64.Instr.b 0xffffffffffffffa0#64) := by
  rw [show pl.base + 936#64 = pl.base + BitVec.ofNat 64 936 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

end

end Poly1305Debian.UD

end
end

section
section
/-! # More instruction shapes, small frames, and calling a function through its contract -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.UD

open Arm64 Arm64.Obj

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_hint (k : BitVec 7) :
    execInstWithSvc svc (.hint k) (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) r sp ps m v := by
  simp [execInstWithSvc]

theorem ex_nop :
    execInstWithSvc svc .nop (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) r sp ps m v := by
  simp [execInstWithSvc]

theorem ex_ret :
    execInstWithSvc svc (.ret (.gpr 30#5)) (mkS s0 pc r sp ps m v) =
      mkS s0 (r 30#5) r sp ps m v := by
  simp [execInstWithSvc]

theorem ex_ldrb_reg (t n k : BitVec 5) (ht : t ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (hr : m.canRead (r n + r k) 1 = true) :
    execInstWithSvc svc (.ldr .W32 .B8 false (.gpr t) (.RegOffset (.gpr n) (.gpr k) .UXTX 0))
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r t ((m.read8 (r n + r k)).zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, extendVal, hr, ht,
    hn, hk, Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_movz64 (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 16) :
    execInstWithSvc svc (.moveWide .W64 .MOVZ (.gpr d) imm 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (imm.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, execMoveWide, State.writeReg, hd]

theorem ex_sub_shift0 (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .SUB (.gpr d) (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n - r k)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, shiftVal, shift64, awc_sub,
    hd, hn, hk]

theorem ex_add_shift0 (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n + r k)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, shiftVal, shift64,
    awc_false_fst, hd, hn, hk]

theorem ex_cmp_reg (n k : BitVec 5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .SUBS .xzr (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp (AddWithCarry64 (r n) (~~~(r k)) true).2 m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, shiftVal, shift64, hn, hk]

theorem ex_csel (c : CondCode) (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5)
    (hk : k ≠ 31#5) :
    execInstWithSvc svc (.condSelect .W64 .CSEL (.gpr d) (.gpr n) (.gpr k) c)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (if ConditionHolds c ps = true then r n else r k)) sp ps m v := by
  by_cases h : ConditionHolds c ps = true <;>
    simp [execInstWithSvc, State.readReg, State.writeReg, hd, hn, hk, h]

theorem ex_str64_gpr (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hw : m.canWrite (r n + off) 8 = true) :
    execInstWithSvc svc (.str .X64 (.gpr a) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 (r n + off) (r a)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw, ha, hn,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_str64_xzr (n : BitVec 5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hw : m.canWrite (r n + off) 8 = true) :
    execInstWithSvc svc (.str .X64 .xzr (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 (r n + off) 0#64) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw, hn,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_str64_sp (a : BitVec 5) (ha : a ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw : m.canWrite (sp + off) 8 = true) :
    execInstWithSvc svc (.str .X64 (.gpr a) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 (sp + off) (r a)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hw, ha,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_ldr64_sp (a : BitVec 5) (ha : a ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr : m.canRead (sp + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a (m.read64 (sp + off))) sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hr, ha,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

end exec

theorem trunc_zext8 (x : BitVec 8) : (x.zeroExtend 64).truncate 8 = x := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp [BitVec.toNat_setWidth] <;> omega

theorem al16_iff (x : BitVec 64) : (x &&& 0b1111#64 = 0#64) ↔ x.toNat % 16 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and]
  have : (0b1111#64 : BitVec 64).toNat = 2 ^ 4 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem al16_sub (x : BitVec 64) (k : Nat) (hk : k % 16 = 0) (hk2 : k < 2 ^ 64)
    (h : x &&& 0b1111#64 = 0#64) : (x - BitVec.ofNat 64 k) &&& 0b1111#64 = 0#64 := by
  rw [al16_iff] at h ⊢
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk2]
  have := x.isLt
  omega

theorem sat_false {m : Memory} {F : SepProp} (h : m ⊨ ⌜False⌝ ∗ F) : False :=
  (sat_pure_sep.mp h).1

theorem readGpr_unfold (s : State) (i : BitVec 5) :
    s.readReg64 (.gpr i) = if i = 31#5 then 0#64 else s.regs.regs i := by
  simp [State.readReg64, RegFile.read]

theorem mkS_vregs' (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64)
    (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128) :
    (mkS s0 pc r sp ps m v).vregs = ⟨v⟩ := rfl

theorem mkS_regs' (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64)
    (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128) :
    (mkS s0 pc r sp ps m v).regs = ⟨r⟩ := rfl

theorem reach_congr {p : Program} {s s' : State} {Q : State → Prop} (h : s' = s)
    (H : Reach p s' Q) : Reach p s Q := by subst h; exact H

/-! ## Two-cell frames -/

theorem memRegion_eq_cells (a : BitVec 64) :
    memRegion a 16 ⊢ ∃∗ v0, ∃∗ v1, (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) := by
  intro h hh
  obtain ⟨bs, hb⟩ := memRegion_entails_bytes a 16 (by omega) h hh
  obtain ⟨hl, hb⟩ := pure_sepConj_holds.mp hb
  rw [pointsToBytes_split a bs 8 (by omega)] at hb
  refine ⟨pack64 (bs.take 8), pack64 (bs.drop 8), ?_⟩
  show ((a ↦₆₄ _) ∗ ((a + 8#64) ↦₆₄ _)).holds h
  rw [pointsTo64_eq_bytes, pointsTo64_eq_bytes, unpack64_pack64 _ (by simp [hl]),
    unpack64_pack64 _ (by simp [hl])]
  exact hb

theorem cells_entails_memRegion (a v0 v1 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) ⊢ memRegion a 16 := by
  rw [pointsTo64_eq_bytes, pointsTo64_eq_bytes]
  have := pointsToBytes_append a (unpack64 v0) (unpack64 v1)
  simp only [unpack64_length] at this
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← this]
  exact bytes_entails_memRegion a _

/-- The four saved cells of the 32-byte frame at `T`. -/
def Cells4 (T u0 u1 u2 u3 : BitVec 64) : SepProp :=
  (T ↦₆₄ u0) ∗ ((T + 8#64) ↦₆₄ u1) ∗ ((T + 0x10#64) ↦₆₄ u2) ∗ ((T + 0x10#64 + 8#64) ↦₆₄ u3)

theorem cells4_of_region {m : Memory} {T : BitVec 64} {F : SepProp}
    (h : m ⊨ memRegion T 32 ∗ F) : ∃ u0 u1 u2 u3, m ⊨ Cells4 T u0 u1 u2 u3 ∗ F := by
  have h1 := sat_sep_mono h (memRegion_split T 16 16 (by norm_num))
  rw [sepConj_assoc] at h1
  have h2 := sat_sep_mono h1 (memRegion_eq_cells T)
  rw [sepExists_sepConj, sat_sepExists] at h2
  obtain ⟨u0, h2⟩ := h2
  rw [sepExists_sepConj, sat_sepExists] at h2
  obtain ⟨u1, h2⟩ := h2
  have h3 := sat_sep_mono (Satisfies.of_eq h2 (Q := memRegion (T + BitVec.ofNat 64 16) 16 ∗
    (((T ↦₆₄ u0) ∗ ((T + 8#64) ↦₆₄ u1)) ∗ F))) (memRegion_eq_cells _)
  rw [sepExists_sepConj, sat_sepExists] at h3
  obtain ⟨u2, h3⟩ := h3
  rw [sepExists_sepConj, sat_sepExists] at h3
  obtain ⟨u3, h3⟩ := h3
  exact ⟨u0, u1, u2, u3, by simp only [Cells4]; exact Satisfies.of_eq h3⟩

theorem region_of_cells4 (T u0 u1 u2 u3 : BitVec 64) :
    Cells4 T u0 u1 u2 u3 ⊢ memRegion T 32 := by
  simp only [Cells4]
  have a1 := sepConj_mono (cells_entails_memRegion T u0 u1)
    (cells_entails_memRegion (T + 0x10#64) u2 u3)
  have a2 := memRegion_merge T (T + 0x10#64) 16 16 rfl (by norm_num) (by norm_num)
  refine Entails.trans (Entails.of_eq (by ac_rfl)) (Entails.trans a1 a2)

/-! ## Stepping, and calls -/

/-- One step, keeping track of the loaded code. -/
theorem Reach.mkC {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {i : Instr} (hrun : s0.status = .Running) (hCL : p.CodeLoaded m)
    (hf : p.fetchMem m pc = some i)
    (h : p.CodeLoaded (execInstWithSvc (evalSvc p.svc) i (mkS s0 pc r sp ps m v)).mem →
      Reach p (execInstWithSvc (evalSvc p.svc) i (mkS s0 pc r sp ps m v)) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  have hst : Step p (mkS s0 pc r sp ps m v) (execInstWithSvc (evalSvc p.svc) i (mkS s0 pc r sp ps m v)) :=
    Step.exec hrun hf
  exact Reach.exec hrun hf (h (Arm64Facts.steps_codeLoaded_v2 (Steps.step hst (Steps.refl _)) hCL))

/-- The callee-saved registers `x19`–`x29` of `sf` are those of `r`. -/
def KeptRegs (sf : State) (r : BitVec 5 → BitVec 64) : Prop :=
  ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 30 → sf.regs.regs k = r k

theorem kept_of_cs {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
    {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {sf : State}
    (h : CalleeSavedPreserved (mkS s0 pc r sp ps m v) sf) : KeptRegs sf r := by
  intro k hk1 hk2
  obtain ⟨a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, -⟩ := h
  simp (config := { decide := true }) only [readGpr_unfold, mkS_readGpr, mkS_regs', Reg.fp, if_false] at a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29
  have hk : k = BitVec.ofNat 5 k.toNat := by simp
  generalize hj : k.toNat = j at hk hk1 hk2
  subst hk
  interval_cases j
  all_goals first | exact a19 | exact a20 | exact a21 | exact a22 | exact a23 | exact a24 | exact a25 | exact a26 | exact a27 | exact a28 | exact a29

/-- A call `bl tgt` at `pc` to a function with contract `spec` at `tgt`, with caller frame `F`. -/
theorem call_ok {α : Type} {pl : Placement} {X : String → Option (State → State)} (spec : Spec α)
    {tgt : BitVec 64} (x : α)
    (hOk : ∀ (R : SepProp) (s0 : State), s0.pc = tgt → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true → reaches_outcome (P pl X) spec x R s0 s0)
    (hpan : ∀ x s s', spec.onPanic x s s' = ⌜False⌝)
    (hexit : ∀ x c s s', spec.onExit x c s s' = ⌜False⌝)
    (hoom : ∀ x s s', spec.onOom x s s' = ⌜False⌝)
    {sb : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState}
    {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop} (F : SepProp)
    (hrun : sb.status = .Running)
    (hf : (P pl X).fetchMem m pc = some (.bl (tgt - pc)))
    (hal : sp &&& 0b1111#64 = 0#64)
    (hCL : (P pl X).CodeLoaded m)
    (hpre : m ⊨ spec.pre x (mkS sb tgt (upd r 30#5 (pc + 4#64)) sp ps m v) ∗ F)
    (hcont : ∀ sf : State, sf.status = .Running → sf.pc = pc + 4#64 → sf.sp = sp →
      KeptRegs sf r → calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      (P pl X).CodeLoaded sf.mem →
      (sf.mem ⊨ spec.post x (mkS sb tgt (upd r 30#5 (pc + 4#64)) sp ps m v) sf ∗ F) →
      Reach (P pl X) sf Q) :
    Reach (P pl X) (mkS sb pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  rw [ex_bl]
  have epc : pc + (tgt - pc) = tgt := by bv_omega
  rw [epc]
  set s1 := mkS sb tgt (upd r 30#5 (pc + 4#64)) sp ps m v with hs1
  have hCL1 : (P pl X).CodeLoaded s1.mem := hCL
  obtain ⟨sf, hsteps, hout⟩ := hOk F s1 rfl hrun hpre (by simp [hs1, hal]) hCL1
  refine Reach.steps hsteps ?_
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨_, hpanc⟩ | ⟨code, _, hex⟩ | ⟨_, hoomc⟩
  rotate_left
  · rw [hpan] at hpanc; exact (sat_false hpanc).elim
  · rw [hexit] at hex; exact (sat_false hex).elim
  · rw [hoom] at hoomc; exact (sat_false hoomc).elim
  have hpc' : sf.pc = pc + 4#64 := by rw [hpcf]; simp [hs1, upd_apply]
  have hsp' : sf.sp = sp := by rw [hspf]; rfl
  refine hcont sf hrunf hpc' hsp' ?_ ?_ (Arm64Facts.steps_codeLoaded_v2 hsteps hCL1) hpost
  · intro k hk1 hk2
    have := kept_of_cs hcs k hk1 hk2
    rw [this, upd_apply, if_neg]
    intro e; subst e; simp at hk2
  · have := hcs.2.2.2.2.2.2.2.2.2.2.2
    rw [this]; rfl

end Poly1305Debian.UD

end
end

section
section
/-! # GCC's byte-copy loop

`L: ldrb wT, [xS, xI]; strb wT, [xD, xI]; add xI, xI, #1; cmp xC, xI; b.ne L` copies the bytes
`xI .. xC - 1` of the source at `xS` to the destination at `xD`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.UD

open Arm64 Arm64.Obj
open Poly1305Libsodium (bytesIn)

/-- `buf` with the bytes `d` copied in at offset `L`. -/
def copyInto (buf : List (BitVec 8)) (L : Nat) (d : List (BitVec 8)) : List (BitVec 8) :=
  buf.take L ++ d ++ buf.drop (L + d.length)

theorem copyInto_step (D S : List (BitVec 8)) (i j k : Nat) (hi : i < S.length)
    (hj : j + (k + 1) ≤ D.length) (hik : i + (k + 1) ≤ S.length) :
    copyInto D j ((S.drop i).take (k + 1)) =
      copyInto (D.set j S[i]) (j + 1) ((S.drop (i + 1)).take k) := by
  have hd : (S.drop i).take (k + 1) = S[i] :: (S.drop (i + 1)).take k := by
    rw [List.drop_eq_getElem_cons hi, List.take_succ_cons]
  have hl : ((S.drop (i + 1)).take k).length = k := by simp; omega
  have hj' : j < D.length := by omega
  have hs : D.set j S[i] = D.take j ++ S[i] :: D.drop (j + 1) := by
    rw [List.set_eq_take_append_cons_drop, if_pos hj']
  have htj : (D.take j).length = j := by simp; omega
  have h1 : (D.set j S[i]).take (j + 1) = D.take j ++ [S[i]] := by
    rw [hs, List.take_append, htj, Nat.add_sub_cancel_left, List.take_of_length_le (by omega)]
    simp
  have h2 : (D.set j S[i]).drop (j + 1 + k) = D.drop (j + (k + 1)) := by
    rw [hs, List.drop_append, htj, List.drop_of_length_le (by omega)]
    rw [show j + 1 + k - j = k + 1 by omega, List.drop_succ_cons, List.drop_drop]
    simp only [List.nil_append]
    try (congr 1; omega)
  simp only [copyInto, hd, hl, h1, h2, List.length_cons, List.append_assoc, List.cons_append,
    List.singleton_append, List.nil_append]

theorem copyInto_nil (D : List (BitVec 8)) (j : Nat) (hj : j ≤ D.length) : copyInto D j [] = D := by
  simp [copyInto]

/-- The source byte `S[i]`: its value and read permission. -/
theorem src_byte {m : Memory} {ro : Bool} {P : BitVec 64} {S : List (BitVec 8)} {G : SepProp}
    (hm : m ⊨ bytesIn ro P S ∗ G) (i : Nat) (hi : i < S.length) :
    m.read8 (P + BitVec.ofNat 64 i) = S[i] ∧ m.canRead (P + BitVec.ofNat 64 i) 1 = true := by
  have e : ∀ n, n < 1 → P + BitVec.ofNat 64 i + BitVec.ofNat 64 n = P + BitVec.ofNat 64 i := by
    intro n hn
    rw [show n = 0 by omega]
    simp
  cases ro
  · simp only [bytesIn, Bool.false_eq_true, ↓reduceIte] at hm
    have H := sat_bytes_read hm i hi
    refine ⟨H.1, canRead_of (fun n hn => ?_)⟩
    rw [e n hn, H.2.1]
    exact ⟨rfl, H.2.2⟩
  · simp only [bytesIn, ↓reduceIte] at hm
    have H := sat_bytesRO_read hm i hi
    refine ⟨H.1, canRead_of (fun n hn => ?_)⟩
    rw [e n hn]
    exact H.2

theorem dst_byte {m : Memory} {A : BitVec 64} {D : List (BitVec 8)} {G : SepProp}
    (hm : m ⊨ (A ↦ₛ D) ∗ G) (j : Nat) (hj : j < D.length) :
    m.canWrite (A + BitVec.ofNat 64 j) 1 = true := by
  have H := sat_bytes_read hm j hj
  refine canWrite_of (fun n hn => ?_)
  rw [show n = 0 by omega]
  simpa using H.2.1

theorem ofNat_succ (i : Nat) : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.ofNat_add]

theorem ne_ofNat_iff (c i : Nat) (hc : c < 2 ^ 64) (hi : i ≤ c) :
    (BitVec.ofNat 64 c ≠ BitVec.ofNat 64 i) ↔ c ≠ i := by
  constructor
  · intro h e; exact h (by rw [e])
  · intro h e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt (by omega)] at this
    exact h this

theorem copyLoop (p : Program) (pc : BitVec 64) (s t d c x : BitVec 5) (Q : State → Prop)
    (sb : State) (sp : BitVec 64) (v : BitVec 5 → BitVec 128) (ro : Bool) (P A : BitVec 64)
    (S : List (BitVec 8)) (F : SepProp) (i0 j0 cnt : Nat)
    (hs : s ≠ 31#5) (ht : t ≠ 31#5) (hd : d ≠ 31#5) (hc : c ≠ 31#5) (hx : x ≠ 31#5)
    (hts : t ≠ s) (htd : t ≠ d) (htc : t ≠ c) (htx : t ≠ x)
    (hxs : x ≠ s) (hxd : x ≠ d) (hxc : x ≠ c)
    (hrun : sb.status = .Running)
    (hf1 : ∀ m', p.CodeLoaded m' → p.fetchMem m' pc =
      some (.ldr .W32 .B8 false (.gpr t) (.RegOffset (.gpr s) (.gpr x) .UXTX 0)))
    (hf2 : ∀ m', p.CodeLoaded m' → p.fetchMem m' (pc + 4#64) =
      some (.str .B8 (.gpr t) (.RegOffset (.gpr d) (.gpr x) .UXTX 0)))
    (hf3 : ∀ m', p.CodeLoaded m' → p.fetchMem m' (pc + 8#64) =
      some (.addSubImm .W64 .ADD (.gpr x) (.gpr x) 0x001#12 false))
    (hf4 : ∀ m', p.CodeLoaded m' → p.fetchMem m' (pc + 12#64) =
      some (.addSubShift .W64 .SUBS .xzr (.gpr c) (.gpr x) .LSL 0))
    (hf5 : ∀ m', p.CodeLoaded m' → p.fetchMem m' (pc + 16#64) =
      some (.bCond .NE 0xfffffffffffffff0#64))
    (hcnt : cnt < 2 ^ 64) (hS : i0 + cnt ≤ S.length) :
    ∀ k : Nat, 0 < k →
    ∀ (i : Nat) (r : BitVec 5 → BitVec 64) (ps : PState) (m : Memory) (D : List (BitVec 8)),
    i + k = cnt → j0 + cnt ≤ D.length →
    p.CodeLoaded m →
    r s = P + BitVec.ofNat 64 i0 → r d = A + BitVec.ofNat 64 j0 → r c = BitVec.ofNat 64 cnt →
    r x = BitVec.ofNat 64 i →
    (m ⊨ bytesIn ro P S ∗ (A ↦ₛ D) ∗ F) →
    (∀ (r' : BitVec 5 → BitVec 64) (ps' : PState) (m' : Memory),
      p.CodeLoaded m' →
      (∀ y, y ≠ t → y ≠ x → r' y = r y) →
      r' x = BitVec.ofNat 64 cnt →
      (m' ⊨ bytesIn ro P S ∗ (A ↦ₛ copyInto D (j0 + i) ((S.drop (i0 + i)).take k)) ∗ F) →
      Reach p (mkS sb (pc + 20#64) r' sp ps' m' v) Q) →
    Reach p (mkS sb pc r sp ps m v) Q := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
  intro _ i r ps m D hik hD hCL hrs hrd hrc hrx hm hcont
  have hi : i0 + i < S.length := by omega
  have hj : j0 + i < D.length := by omega
  obtain ⟨hb, hcr⟩ := src_byte hm (i0 + i) hi
  have hm' : m ⊨ (A ↦ₛ D) ∗ (bytesIn ro P S ∗ F) := Satisfies.of_eq hm
  have hcw := dst_byte hm' (j0 + i) hj
  have hW := sat_bytes_write hm' (j0 + i) hj S[i0 + i]
  have eS : r s + r x = P + BitVec.ofNat 64 (i0 + i) := by rw [hrs, hrx, pc_add]
  -- ldrb
  refine Reach.mkC hrun hCL (hf1 m hCL) ?_
  rw [ex_ldrb_reg t s x ht hs hx (by rw [eS]; exact hcr), eS, hb]
  intro hCL1
  simp only [mkS_mem] at hCL1
  -- strb
  have eD : upd r t ((S[i0 + i]).zeroExtend 64) d + upd r t ((S[i0 + i]).zeroExtend 64) x =
      A + BitVec.ofNat 64 (j0 + i) := by
    rw [upd_ne _ _ (Ne.symm htd), upd_ne _ _ (Ne.symm htx), hrd, hrx, pc_add]
  refine Reach.mkC hrun hCL1 (hf2 m hCL1) ?_
  rw [ex_strb_reg t d x ht hd hx (by rw [eD]; exact hcw), eD, upd_same, trunc_zext8]
  intro hCL2
  simp only [mkS_mem] at hCL2
  rw [show pc + 4#64 + 4#64 = pc + 8#64 by bv_omega]
  -- add
  refine Reach.mkC hrun hCL2 (hf3 _ hCL2) ?_
  rw [ex_add_imm x x hx hx, upd_ne _ _ (Ne.symm htx), hrx,
    show (0x001#12 : BitVec 12).zeroExtend 64 = 1#64 from rfl, ofNat_succ]
  intro hCL3
  simp only [mkS_mem] at hCL3
  rw [show pc + 8#64 + 4#64 = pc + 12#64 by bv_omega]
  -- cmp
  refine Reach.mkC hrun hCL3 (hf4 _ hCL3) ?_
  rw [ex_cmp_reg c x hc hx, upd_ne _ _ hxc.symm, upd_ne _ _ (Ne.symm htc), upd_same, hrc]
  intro hCL4
  simp only [mkS_mem] at hCL4
  rw [show pc + 12#64 + 4#64 = pc + 16#64 by bv_omega]
  -- b.ne
  refine Reach.mkC hrun hCL4 (hf5 _ hCL4) ?_
  rw [ex_bcond, ne_cmp, show decide (BitVec.ofNat 64 cnt ≠ BitVec.ofNat 64 (i + 1)) =
    decide (cnt ≠ i + 1) from by
      simp only [decide_eq_decide]; exact ne_ofNat_iff cnt (i + 1) hcnt (by omega)]
  intro hCL5
  simp only [mkS_mem] at hCL5
  have hstep := copyInto_step D S (i0 + i) (j0 + i) k hi (by omega) (by omega)
  by_cases hk0 : k = 0
  · subst hk0
    have e1 : ¬ (cnt ≠ i + 1) := by omega
    simp only [e1, decide_false, Bool.false_eq_true, if_false]
    rw [show pc + 16#64 + 4#64 = pc + 20#64 by bv_omega]
    refine hcont _ _ _ hCL5 ?_ ?_ ?_
    · intro y h1 h2
      simp [upd_apply, h1, h2]
    · simp only [upd_same]; congr 1
    · rw [hstep, List.take_zero, copyInto_nil _ _ (by simp; omega)]
      exact Satisfies.of_eq hW
  · have e1 : cnt ≠ i + 1 := by omega
    simp only [e1, ne_eq, not_false_eq_true, decide_true, if_true]
    rw [show pc + 16#64 + 0xfffffffffffffff0#64 = pc by bv_omega]
    refine ih (by omega) (i + 1) _ _ _ (D.set (j0 + i) S[i0 + i]) (by omega) (by simp; omega)
      hCL5 ?_ ?_ ?_ ?_ (Satisfies.of_eq hW) ?_
    · simp [upd_apply, Ne.symm hxs, Ne.symm hts, hrs]
    · simp [upd_apply, Ne.symm hxd, Ne.symm htd, hrd]
    · simp [upd_apply, Ne.symm hxc, Ne.symm htc, hrc]
    · simp [upd_apply]
    · intro r' ps' m' hCL' hother hx' hmm
      refine hcont r' ps' m' hCL' ?_ hx' ?_
      · intro y h1 h2
        rw [hother y h1 h2]
        simp [upd_apply, h1, h2]
      · rw [hstep]
        rw [show j0 + (i + 1) = j0 + i + 1 by omega,
          show i0 + (i + 1) = i0 + i + 1 by omega] at hmm
        exact hmm

end Poly1305Debian.UD

end
end

section
section
/-! # Arithmetic and byte-list facts: the state as fields, and `Absorbs` -/

set_option autoImplicit false

namespace Poly1305Debian.UD

open Arm64 Poly1305Boringssl
open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

theorem leBytesToNum_unpack64 (v : BitVec 64) : leBytesToNum (unpack64 v) = v.toNat := by
  have h := v.isLt
  simp only [unpack64, leBytesToNum, List.foldr_cons, List.foldr_nil, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  generalize v.toNat = x at h ⊢
  norm_num at h ⊢
  omega

theorem pack64_toNat (l : List (BitVec 8)) (h : l.length = 8) :
    (pack64 l).toNat = leBytesToNum l := by
  rw [← leBytesToNum_unpack64, unpack64_pack64 l h]


theorem u64At_take (xs : List (BitVec 8)) (n off : Nat) (h : off + 8 ≤ n) :
    u64At (xs.take n) off = u64At xs off := by
  unfold u64At
  rw [List.drop_take, List.take_take, show min 8 (n - off) = 8 by omega]

theorem limbVal_rLimb_take (xs : List (BitVec 8)) (n : Nat) (h : 24 ≤ n) :
    limbVal (rLimb (xs.take n)) = limbVal (rLimb xs) := by
  have e : ∀ i, i ≤ 2 → rLimb (xs.take n) i = rLimb xs i := fun i hi =>
    u64At_take xs n _ (by omega)
  simp only [limbVal]
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega)]

theorem limbVal_hLimb_take (xs : List (BitVec 8)) (n : Nat) (h : 48 ≤ n) :
    limbVal (hLimb (xs.take n)) = limbVal (hLimb xs) := by
  have e : ∀ i, i ≤ 2 → hLimb (xs.take n) i = hLimb xs i := fun i hi =>
    u64At_take xs n _ (by omega)
  simp only [limbVal]
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega)]

theorem layout {rh pad w buf rest : List (BitVec 8)} {fin : BitVec 8}
    (h1 : rh.length = 48) (h2 : pad.length = 16) (h3 : w.length = 8) (h4 : buf.length = 16) :
    (rh ++ pad ++ w ++ buf ++ fin :: rest).take 48 = rh ∧
    ((rh ++ pad ++ w ++ buf ++ fin :: rest).drop 48).take 16 = pad ∧
    ((rh ++ pad ++ w ++ buf ++ fin :: rest).drop 64).take 8 = w ∧
    (rh ++ pad ++ w ++ buf ++ fin :: rest).drop 72 = buf ++ fin :: rest ∧
    (rh ++ pad ++ w ++ buf ++ fin :: rest).getD 88 0#8 = fin ∧
    (rh ++ pad ++ w ++ buf ++ fin :: rest).length = 89 + rest.length := by
  simp only [List.append_assoc]
  refine ⟨List.take_left' h1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.drop_left' h1, List.take_left' h2]
  · rw [show 64 = 48 + 16 from rfl, ← List.drop_drop, List.drop_left' h1, List.drop_left' h2,
      List.take_left' h3]
  · rw [show 72 = 48 + 16 + 8 from rfl, ← List.drop_drop, ← List.drop_drop, List.drop_left' h1,
      List.drop_left' h2, List.drop_left' h3]
  · rw [List.getD_eq_getElem?_getD]
    simp [List.getElem?_append_right, h1, h2, h3, h4]
  · simp [h1, h2, h3, h4]; omega

theorem foldl_ext' (f g : Nat → Nat → Nat) (l : List Nat) (a : Nat)
    (H : ∀ a b, b ∈ l → f a b = g a b) : l.foldl f a = l.foldl g a := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldl_cons]
    rw [H a b List.mem_cons_self]
    exact ih _ (fun a b hb => H a b (List.mem_cons_of_mem _ hb))

theorem foldl_mod {f : Nat → Nat → Nat} (hf : ∀ a i, f a i = f (a % p1305) i) (l : List Nat)
    (a : Nat) : l.foldl f a % p1305 = l.foldl f (a % p1305) % p1305 := by
  cases l with
  | nil => simp
  | cons i l => simp only [List.foldl_cons]; rw [hf a i]

theorem mul_add_mod_left (r a t : Nat) :
    r * (a + t) % p1305 = r * (a % p1305 + t) % p1305 := by
  have : (a % p1305 + t) % p1305 = (a + t) % p1305 := Nat.mod_add_mod _ _ _
  symm
  rw [← Nat.mul_mod_mod, this, Nat.mul_mod_mod]

theorem blocksAcc_mod (r hb a : Nat) (c : List (BitVec 8)) :
    blocksAcc r hb a c % p1305 = blocksAcc r hb (a % p1305) c % p1305 := by
  unfold blocksAcc
  apply foldl_mod
  intro a i
  rw [Nat.add_assoc, Nat.add_assoc, mul_add_mod_left]

theorem blocksAcc_append (r hb a : Nat) (x c : List (BitVec 8)) (hx : x.length % 16 = 0) :
    blocksAcc r hb a (x ++ c) = blocksAcc r hb (blocksAcc r hb a x) c := by
  unfold blocksAcc
  have hlen : (x ++ c).length / 16 = x.length / 16 + c.length / 16 := by simp; omega
  rw [hlen, List.range_add, List.foldl_append, List.foldl_map]
  have e1 : (List.range (x.length / 16)).foldl
      (fun a i => r * (a + leBytesToNum (((x ++ c).drop (16 * i)).take 16) + hb) % p1305) a =
      (List.range (x.length / 16)).foldl
      (fun a i => r * (a + leBytesToNum ((x.drop (16 * i)).take 16) + hb) % p1305) a := by
    apply foldl_ext'
    intro a i hi
    rw [List.mem_range] at hi
    rw [List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by simp; omega)]
  rw [e1]
  apply foldl_ext'
  intro a j _
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    show 16 * (x.length / 16 + j) - x.length = 16 * j by omega]


theorem blocksAcc_short (r hb a : Nat) (x : List (BitVec 8)) (hx : x.length < 16) :
    blocksAcc r hb a x = a := by
  unfold blocksAcc
  rw [show x.length / 16 = 0 by omega]
  rfl

/-- The 96 state bytes at `a` as fields: `buffer` (16 at 72), `leftover` (a cell at 64), `r,h`
(48), `final` (one byte at 88), `pad` (16 at 48), the rest (7 from 89). -/
def Fields (a : BitVec 64) (rh pad : List (BitVec 8)) (lo : BitVec 64) (buf : List (BitVec 8))
    (fin : BitVec 8) (rest : List (BitVec 8)) : SepProp :=
  ((a + 72#64) ↦ₛ buf) ∗ ((a + 64#64) ↦₆₄ lo) ∗ (a ↦ₛ rh) ∗ ((a + 88#64) ↦ₛ [fin]) ∗
    ((a + 48#64) ↦ₛ pad) ∗ ((a + 89#64) ↦ₛ rest)

theorem fields_eq (a : BitVec 64) (rh pad buf rest : List (BitVec 8)) (lo : BitVec 64)
    (fin : BitVec 8) (h1 : rh.length = 48) (h2 : pad.length = 16) (h4 : buf.length = 16) :
    (a ↦ₛ (rh ++ pad ++ unpack64 lo ++ buf ++ fin :: rest)) = Fields a rh pad lo buf fin rest := by
  simp only [List.append_assoc, Fields]
  rw [show fin :: rest = [fin] ++ rest from rfl, pointsToBytes_append, pointsToBytes_append,
    pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, ← pointsTo64_eq_bytes]
  simp only [h1, h2, h4, unpack64_length, List.length_singleton, pc_add, Nat.reduceAdd]
  ac_rfl

/-- The pending bytes `t` (the old buffer's first `L` bytes followed by the message): `rh'`,
`lo'`, `buf'` are the fields of a state that has absorbed the complete blocks of `t`. -/
def Good (rh0 : List (BitVec 8)) (fin : BitVec 8) (t : List (BitVec 8)) (rh' : List (BitVec 8))
    (lo' : BitVec 64) (buf' : List (BitVec 8)) : Prop :=
  rh'.length = 48 ∧ buf'.length = 16 ∧ StateOk rh' ∧ rh'.take 24 = rh0.take 24 ∧
    lo'.toNat = t.length - 16 * (t.length / 16) ∧
    buf'.take (t.length - 16 * (t.length / 16)) = t.drop (16 * (t.length / 16)) ∧
    limbVal (hLimb rh') % p1305 =
      blocksAcc (limbVal (rLimb rh0)) (hibit fin) (limbVal (hLimb rh0))
        (t.take (16 * (t.length / 16))) % p1305

theorem absorbs_of {rh0 pad w0 buf0 rest rh' buf' msg : List (BitVec 8)} {fin : BitVec 8}
    {lo' : BitVec 64} (h1 : rh0.length = 48) (h2 : pad.length = 16) (h3 : w0.length = 8)
    (h4 : buf0.length = 16) (h5 : rest.length = 7) (hL : leBytesToNum w0 < 16)
    (hG : Good rh0 fin (buf0.take (leBytesToNum w0) ++ msg) rh' lo' buf') :
    Absorbs (rh0 ++ pad ++ w0 ++ buf0 ++ fin :: rest) msg
      (rh' ++ pad ++ unpack64 lo' ++ buf' ++ fin :: rest) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hG
  have L0 := layout (fin := fin) (rest := rest) h1 h2 h3 h4
  have L1 := layout (fin := fin) (rest := rest) g1 h2 (unpack64_length lo') g2
  have hu0 : u64At (rh0 ++ pad ++ w0 ++ buf0 ++ fin :: rest) 64 = leBytesToNum w0 := by
    unfold u64At; rw [L0.2.2.1]
  have hu1 : u64At (rh' ++ pad ++ unpack64 lo' ++ buf' ++ fin :: rest) 64 = lo'.toNat := by
    unfold u64At; rw [L1.2.2.1, leBytesToNum_unpack64]
  have hbuf : ((rh0 ++ pad ++ w0 ++ buf0 ++ fin :: rest).drop 72).take (leBytesToNum w0) =
      buf0.take (leBytesToNum w0) := by
    rw [L0.2.2.2.1, List.take_append_of_le_length (by omega)]
  have hk : (buf0.take (leBytesToNum w0) ++ msg).length - 16 *
      ((buf0.take (leBytesToNum w0) ++ msg).length / 16) < 16 := by omega
  unfold Absorbs
  simp only [hu0, hbuf]
  refine ⟨by rw [L1.2.2.2.2.2]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.append_assoc]
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
    exact g4
  · rw [L1.2.1, L0.2.1]
  · rw [L1.2.2.2.2.1, L0.2.2.2.2.1]
  · rw [L1.1]; exact g3
  · rw [hu1, g5]
  · rw [L1.2.2.2.1, List.take_append_of_le_length (by omega)]; exact g6
  · have e1 : limbVal (hLimb (rh' ++ pad ++ unpack64 lo' ++ buf' ++ fin :: rest)) =
        limbVal (hLimb rh') := by
      rw [← limbVal_hLimb_take _ 48 (le_refl _), L1.1]
    have e2 : limbVal (rLimb (rh0 ++ pad ++ w0 ++ buf0 ++ fin :: rest)) = limbVal (rLimb rh0) := by
      rw [← limbVal_rLimb_take _ 48 (by omega), L0.1]
    have e3 : limbVal (hLimb (rh0 ++ pad ++ w0 ++ buf0 ++ fin :: rest)) = limbVal (hLimb rh0) := by
      rw [← limbVal_hLimb_take _ 48 (le_refl _), L0.1]
    rw [e1, e2, e3, L0.2.2.2.2.1]
    exact g7

end Poly1305Debian.UD

end
end

section
section
/-! # The exit continuation and the epilogue (`ldp x29, x30, [sp], #32; autiasp; ret`)

The epilogue appears twice in `poly1305_update`, at text offsets 784 and 892. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.UD

open Arm64 Arm64.Obj Poly1305Boringssl
open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

/-- Registers `x19`–`x28` as in `r0`. -/
def Kept (r r0 : BitVec 5 → BitVec 64) : Prop :=
  ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 29 → r k = r0 k

theorem Kept.upd {r r0 : BitVec 5 → BitVec 64} (h : Kept r r0) (i : BitVec 5)
    (hi : i.toNat < 19 ∨ 29 ≤ i.toNat) (x : BitVec 64) : Kept (UD.upd r i x) r0 := by
  intro k h1 h2
  rw [upd_ne _ _ (by rintro rfl; omega)]
  exact h k h1 h2

theorem Kept.keptRegs {r r0 : BitVec 5 → BitVec 64} {sf : State} (h : Kept r r0)
    (hk : KeptRegs sf r) : Kept sf.regs.regs r0 := by
  intro k h1 h2
  rw [hk k (by omega) (by omega)]
  exact h k h1 h2

/-- The exit continuation: from an epilogue at `pcE` with stack pointer `T`, a state whose fields
have absorbed the complete blocks of `t` (`Good`) reaches `Q`. -/
def ExitK (pl : Placement) (X : String → Option (State → State)) (Q : State → Prop)
    (pcE T a p : BitVec 64) (ro : Bool) (msg pad rest rh0 t : List (BitVec 8)) (fin : BitVec 8)
    (r0 : BitVec 5 → BitVec 64) (v0 : BitVec 5 → BitVec 128) (x29 x30 : BitVec 64)
    (R : SepProp) : Prop :=
  ∀ (sb : State) (r : BitVec 5 → BitVec 64) (ps : PState) (m : Memory)
    (v : BitVec 5 → BitVec 128) (rh' buf' : List (BitVec 8)) (lo' u2 u3 : BitVec 64),
    sb.status = .Running → (P pl X).CodeLoaded m → Kept r r0 → r 0#5 = a →
    VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨v0⟩ →
    Good rh0 fin t rh' lo' buf' →
    (m ⊨ Fields a rh' pad lo' buf' fin rest ∗ bytesIn ro p msg ∗ Cells4 T x29 x30 u2 u3 ∗ R) →
    Reach (P pl X) (mkS sb pcE r T ps m v) Q

set_option maxHeartbeats 4000000 in
theorem exit_ok {pl : Placement} {X : String → Option (State → State)} (s0 : State) (ro : Bool)
    (rh0 pad w0 buf0 rest msg : List (BitVec 8)) (fin : BitVec 8) (R : SepProp)
    (h1 : rh0.length = 48) (h2 : pad.length = 16) (h3 : w0.length = 8) (h4 : buf0.length = 16)
    (h5 : rest.length = 7) (hL : leBytesToNum w0 < 16)
    (hal0 : s0.sp &&& 0b1111#64 = 0#64) (pcE : BitVec 64)
    (hf1 : ∀ m', (P pl X).CodeLoaded m' → (P pl X).fetchMem m' pcE =
      some (.ldp .W64 false (.gpr 0x1d#5) (.gpr 0x1e#5) (.PostIndex .sp 0x0000000000000020#64)))
    (hf2 : ∀ m', (P pl X).CodeLoaded m' → (P pl X).fetchMem m' (pcE + 4#64) = some (.hint 0x1d#7))
    (hf3 : ∀ m', (P pl X).CodeLoaded m' → (P pl X).fetchMem m' (pcE + 4#64 + 4#64) =
      some (.ret (.gpr 0x1e#5))) :
    ExitK pl X (fun sf => SubroutineOutcome updateIntSpec
        (ro, rh0 ++ pad ++ w0 ++ buf0 ++ fin :: rest, msg) R s0 sf)
      pcE (s0.sp - 32#64) (s0.readReg64 Reg.x0) (s0.readReg64 Reg.x1) ro msg pad rest rh0
      (buf0.take (leBytesToNum w0) ++ msg) fin s0.regs.regs s0.vregs.regs
      (s0.regs.regs 29#5) (s0.regs.regs 30#5) R := by
  intro sb r ps m v rh' buf' lo' u2 u3 hrun hCL hkept hr0 hv hgood hm
  set T := s0.sp - 32#64 with hT
  set a := s0.readReg64 Reg.x0 with ha
  set p := s0.readReg64 Reg.x1 with hp
  have hTal : T &&& 0b1111#64 = 0#64 := al16_sub _ 32 (by norm_num) (by norm_num) hal0
  generalize hx29 : s0.regs.regs 29#5 = x29 at hm
  generalize hx30 : s0.regs.regs 30#5 = x30 at hm
  generalize hG : Fields a rh' pad lo' buf' fin rest ∗ bytesIn ro p msg = G
  have hm0 := Satisfies.of_eq hm (Q := Cells4 T x29 x30 u2 u3 ∗ (G ∗ R)) (by rw [← hG]; ac_rfl)
  simp only [Cells4, sepConj_assoc] at hm0
  have d0 := sat64_read hm0
  have d1 := sat64_read (Satisfies.of_eq hm0 (Q := ((T + 8#64) ↦₆₄ x30) ∗ ((T ↦₆₄ x29) ∗
    ((T + 0x10#64) ↦₆₄ u2) ∗ ((T + 0x10#64 + 8#64) ↦₆₄ u3) ∗ (G ∗ R))))
  -- ldp x29, x30, [sp], #32
  refine Reach.mkC hrun hCL (hf1 m hCL) ?_
  rw [ex_ldp64_post_sp 29#5 30#5 (by decide) (by decide) 0x20#64 hTal d0.2.1 d1.2.1, d0.1, d1.1]
  intro hCL1
  -- autiasp
  refine Reach.mkC hrun hCL1 (hf2 m hCL1) ?_
  rw [ex_hint]
  intro hCL2
  -- ret
  refine Reach.mkC hrun hCL2 (hf3 m hCL2) ?_
  rw [ex_ret]
  intro _
  refine Reach.done ?_
  have hS : T + 0x20#64 = s0.sp := by rw [hT]; bv_omega
  left
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · simp [upd_apply, readGpr_unfold, Reg.lr, hx30]
  · exact hS
  · exact hrun
  · exact hS
  · simp (config := { decide := true }) only [CalleeSavedPreserved, readGpr_unfold, mkS_regs',
      mkS_vregs', upd_apply, ↓reduceIte, Reg.fp]
    refine ⟨hkept 19#5 (by decide) (by decide), hkept 20#5 (by decide) (by decide),
      hkept 21#5 (by decide) (by decide), hkept 22#5 (by decide) (by decide),
      hkept 23#5 (by decide) (by decide),
      hkept 24#5 (by decide) (by decide), hkept 25#5 (by decide) (by decide),
      hkept 26#5 (by decide) (by decide), hkept 27#5 (by decide) (by decide),
      hkept 28#5 (by decide) (by decide), hx29.symm, hv⟩
  · -- the memory
    show _ ⊨ (⌜_⌝ ∗ (∃∗ st' : List (BitVec 8),
        ⌜Absorbs (rh0 ++ pad ++ w0 ++ buf0 ++ fin :: rest) msg st'⌝ ∗ (a ↦ₛ st')) ∗
      bytesIn ro p msg ∗ stackFrame s0 32) ∗ R
    rw [sepConj_assoc, sat_pure_sep]
    have hr0' : r 0#5 = s0.regs.regs 0#5 := by rw [hr0, ha]; simp [readGpr_unfold, Reg.x0]
    refine ⟨by simp [readGpr_unfold, Reg.x0, mkS_regs', upd_apply, hr0'], ?_⟩
    rw [sepConj_assoc, sepExists_sepConj, sat_sepExists]
    refine ⟨rh' ++ pad ++ unpack64 lo' ++ buf' ++ fin :: rest, ?_⟩
    rw [sepConj_assoc, sat_pure_sep]
    refine ⟨absorbs_of h1 h2 h3 h4 h5 hL hgood, ?_⟩
    rw [fields_eq a rh' pad buf' rest lo' fin hgood.1 h2 hgood.2.1]
    have hm1 := Satisfies.of_eq hm (Q := Cells4 T x29 x30 u2 u3 ∗
      (Fields a rh' pad lo' buf' fin rest ∗ bytesIn ro p msg ∗ R))
    have hm2 := sat_sep_mono hm1 (region_of_cells4 T x29 x30 u2 u3)
    have es : T = s0.sp - BitVec.ofNat 64 32 := by rw [hT]
    rw [es] at hm2
    simp only [stackFrame]
    exact Satisfies.of_eq hm2

end Poly1305Debian.UD

end
end

section
section
/-! # `poly1305_update`, text offsets 840–888: "store leftover"

With `leftover = 0`, `x18` at the message's byte `j` and `x4 = c` (`0 < c < 16`) bytes left, the loop
copies them into the buffer and `leftover` becomes `c`; then the epilogue at 892. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.UD

open Arm64 Arm64.Obj Poly1305Boringssl
open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

set_option maxHeartbeats 4000000 in
theorem seg_copy {pl : Placement} (hP : libsodiumDebianOnetimeauthLib.Placeable pl)
    {X : String → Option (State → State)} {Q : State → Prop}
    {T a p : BitVec 64} {ro : Bool} {msg pad rest rh0 t : List (BitVec 8)} {fin : BitVec 8}
    {r0 : BitVec 5 → BitVec 64} {v0 : BitVec 5 → BitVec 128} {x29 x30 : BitVec 64} {R : SepProp}
    (K : ExitK pl X Q (pl.base + 892#64) T a p ro msg pad rest rh0 t fin r0 v0 x29 x30 R)
    {sb : State} {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128}
    (hrun : sb.status = .Running) (hCL : (P pl X).CodeLoaded m) (hkept : Kept r r0)
    (hr0 : r 0#5 = a) (hv : VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨v0⟩)
    (j c : Nat) (hc0 : 0 < c) (hc16 : c < 16) (hlen : msg.length = j + c)
    (hr18 : r 18#5 = p + BitVec.ofNat 64 j) (hr4 : r 4#5 = BitVec.ofNat 64 c)
    (rh buf : List (BitVec 8)) (hbuf : buf.length = 16) (u2 u3 : BitVec 64)
    (hgood : Good rh0 fin t rh (BitVec.ofNat 64 c) (copyInto buf 0 (msg.drop j)))
    (hm : m ⊨ Fields a rh pad 0#64 buf fin rest ∗ bytesIn ro p msg ∗ Cells4 T x29 x30 u2 u3 ∗ R) :
    Reach (P pl X) (mkS sb (pl.base + 840#64) r T ps m v) Q := by
  generalize hW : (a ↦ₛ rh) ∗ ((a + 88#64) ↦ₛ [fin]) ∗ ((a + 48#64) ↦ₛ pad) ∗
    ((a + 89#64) ↦ₛ rest) ∗ Cells4 T x29 x30 u2 u3 ∗ R = W
  have hm1 : m ⊨ ((a + 64#64) ↦₆₄ 0#64) ∗ (bytesIn ro p msg ∗ ((a + 72#64) ↦ₛ buf) ∗ W) :=
    Satisfies.of_eq hm (by rw [← hW]; simp only [Fields]; ac_rfl)
  have c0 := sat64_read hm1
  -- 840: ldr x5, [x0, #0x40]
  refine Reach.mkC hrun hCL (f_98 hP hCL) ?_
  rw [ex_ldr64_gpr 5#5 0#5 (by decide) (by decide) _ (by rw [hr0]; exact c0.2.1), hr0, c0.1, pc_add]
  intro hCL1
  -- 844: mov x3, #0
  refine Reach.mkC hrun hCL1 (f_9c hP hCL1) ?_
  rw [ex_movz64 3#5 (by decide), pc_add]
  intro hCL2
  -- 848: add x2, x5, #0x48
  refine Reach.mkC hrun hCL2 (f_a0 hP hCL2) ?_
  rw [ex_add_imm 2#5 5#5 (by decide) (by decide), pc_add]
  intro hCL3
  -- 852: add x2, x0, x2
  refine Reach.mkC hrun hCL3 (f_a4 hP hCL3) ?_
  rw [ex_add_shift0 2#5 0#5 2#5 (by decide) (by decide) (by decide), pc_add]
  intro hCL4
  -- 856, 860: nop
  refine Reach.mkC hrun hCL4 (f_a8 hP hCL4) ?_
  rw [ex_nop, pc_add]
  intro hCL5
  refine Reach.mkC hrun hCL5 (f_ac hP hCL5) ?_
  rw [ex_nop, pc_add]
  intro hCL6
  simp only [mkS_mem] at hCL1 hCL2 hCL3 hCL4 hCL5 hCL6
  -- 864: the loop
  have hm2 : m ⊨ bytesIn ro p msg ∗ ((a + 72#64) ↦ₛ buf) ∗ (((a + 64#64) ↦₆₄ 0#64) ∗ W) :=
    Satisfies.of_eq hm1
  refine copyLoop (P pl X) (pl.base + BitVec.ofNat 64 (840 + 4 + 4 + 4 + 4 + 4 + 4))
    18#5 1#5 2#5 4#5 3#5 Q sb T v ro p (a + 72#64) msg (((a + 64#64) ↦₆₄ 0#64) ∗ W) j 0 c
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hrun
    (fun m' h => f_b0 hP h) (fun m' h => by rw [pc_add]; exact f_b4 hP h)
    (fun m' h => by rw [pc_add]; exact f_b8 hP h)
    (fun m' h => by rw [pc_add]; exact f_bc hP h) (fun m' h => by rw [pc_add]; exact f_c0 hP h) (by omega) (by omega)
    c hc0 0 _ _ _ buf (by omega) (by omega) hCL6 ?_ ?_ ?_ ?_ hm2 ?_
  · simp [upd_apply, hr18]
  · simp [upd_apply, hr0]
  · simp [upd_apply, hr4]
  · simp [upd_apply]
  intro r' ps' m' hCL7 hother hr3 hm3
  have ne1 : ∀ k : BitVec 5, 19 ≤ k.toNat → k ≠ 1#5 := by
    intro k h e; subst e; revert h; decide
  have ne3 : ∀ k : BitVec 5, 19 ≤ k.toNat → k ≠ 3#5 := by
    intro k h e; subst e; revert h; decide
  have hr'0 : r' 0#5 = a := by rw [hother 0#5 (by decide) (by decide)]; simp [upd_apply, hr0]
  have hr'5 : r' 5#5 = 0#64 := by rw [hother 5#5 (by decide) (by decide)]; simp [upd_apply]
  have hr'4 : r' 4#5 = BitVec.ofNat 64 c := by
    rw [hother 4#5 (by decide) (by decide)]; simp [upd_apply, hr4]
  have hk' : Kept r' r0 := by
    intro k h1 h2
    rw [hother k (ne1 k h1) (ne3 k h1)]
    have e5 : k ≠ 5#5 := by rintro rfl; revert h1; decide
    have e3 : k ≠ 3#5 := ne3 k h1
    have e2 : k ≠ 2#5 := by rintro rfl; revert h1; decide
    simp only [upd_apply, e5, e3, e2, if_false]
    exact hkept k h1 h2
  have ecp : (msg.drop (j + 0)).take c = msg.drop j := by
    rw [Nat.add_zero, List.take_of_length_le (by simp; omega)]
  rw [Nat.add_zero, ecp] at hm3
  rw [pc_add]
  -- 884: add x5, x5, x4
  refine Reach.mkC hrun hCL7 (f_c4 hP hCL7) ?_
  rw [ex_add_shift0 5#5 5#5 4#5 (by decide) (by decide) (by decide), hr'5, hr'4, BitVec.zero_add,
    pc_add]
  intro hCL8
  simp only [mkS_mem] at hCL8
  -- 888: str x5, [x0, #0x40]
  have hm4 : m' ⊨ ((a + 64#64) ↦₆₄ 0#64) ∗ (bytesIn ro p msg ∗
      ((a + 72#64) ↦ₛ copyInto buf 0 (msg.drop j)) ∗ W) := Satisfies.of_eq hm3
  have c1 := sat64_read hm4
  refine Reach.mkC hrun hCL8 (f_c8 hP hCL8) ?_
  rw [ex_str64_gpr 5#5 0#5 (by decide) (by decide) _
    (by rw [upd_ne _ _ (by decide), hr'0]; exact c1.2.2), upd_same, upd_ne _ _ (by decide), hr'0,
    pc_add]
  intro hCL9
  simp only [mkS_mem] at hCL9
  have hm5 := sat64_write hm4 (BitVec.ofNat 64 c)
  refine K sb _ ps' _ v rh (copyInto buf 0 (msg.drop j)) (BitVec.ofNat 64 c) u2 u3 hrun hCL9
    (hk'.upd 5#5 (by decide) _) (by rw [upd_ne _ _ (by decide), hr'0]) hv hgood ?_
  rw [← hW] at hm5
  simp only [Fields]
  exact Satisfies.of_eq hm5

end Poly1305Debian.UD

end
end

section
section
/-! # The block invariant along the pending bytes `t`

`Inv rh0 fin t K rh`: the fields `rh` hold the accumulator after the first `K` bytes of `t`. -/

set_option autoImplicit false

namespace Poly1305Debian.UD

open Arm64 Poly1305Boringssl
open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

def Inv (rh0 : List (BitVec 8)) (fin : BitVec 8) (t : List (BitVec 8)) (K : Nat)
    (rh : List (BitVec 8)) : Prop :=
  StateOk rh ∧ rh.take 24 = rh0.take 24 ∧
    limbVal (hLimb rh) % p1305 =
      blocksAcc (limbVal (rLimb rh0)) (hibit fin) (limbVal (hLimb rh0)) (t.take K) % p1305

theorem good_exit0 {rh0 t rh buf : List (BitVec 8)} {fin : BitVec 8} {K : Nat}
    (ht : t.length = K) (hK : K % 16 = 0) (hbuf : buf.length = 16) (hI : Inv rh0 fin t K rh) :
    Good rh0 fin t rh 0#64 buf := by
  obtain ⟨h1, h2, h3⟩ := hI
  have e : 16 * (t.length / 16) = K := by omega
  refine ⟨h1.1, hbuf, h1, h2, ?_, ?_, ?_⟩
  · rw [e]; simp; omega
  · rw [e, ht, Nat.sub_self, List.take_zero, List.drop_eq_nil_of_le (by omega)]
  · rw [e]; exact h3

theorem good_copy {rh0 t rh buf d : List (BitVec 8)} {fin : BitVec 8} {K c : Nat}
    (ht : t.length = K + c) (hK : K % 16 = 0) (hc : c < 16) (htd : t.drop K = d)
    (hd : d.length = c) (hbuf : buf.length = 16) (hI : Inv rh0 fin t K rh) :
    Good rh0 fin t rh (BitVec.ofNat 64 c) (copyInto buf 0 d) := by
  obtain ⟨h1, h2, h3⟩ := hI
  have e : 16 * (t.length / 16) = K := by omega
  have e2 : t.length - K = c := by omega
  refine ⟨h1.1, by simp [copyInto, hbuf]; omega, h1, h2, ?_, ?_, ?_⟩
  · rw [e, e2]; simp; omega
  · rw [e, e2, htd]
    simp only [copyInto, List.take_zero, List.nil_append, hd, Nat.zero_add]
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  · rw [e]; exact h3

theorem inv_step {rh0 t rh rh2 : List (BitVec 8)} {fin : BitVec 8} {K B : Nat}
    (hK : K % 16 = 0) (hB : B % 16 = 0) (hKt : K ≤ t.length) (hI : Inv rh0 fin t K rh)
    (h1 : StateOk rh2) (h2 : rh2.take 24 = rh.take 24)
    (h3 : limbVal (hLimb rh2) % p1305 =
      blocksAcc (limbVal (rLimb rh)) (hibit fin) (limbVal (hLimb rh)) ((t.drop K).take B) % p1305) :
    Inv rh0 fin t (K + B) rh2 := by
  obtain ⟨i1, i2, i3⟩ := hI
  refine ⟨h1, h2.trans i2, ?_⟩
  have er : limbVal (rLimb rh) = limbVal (rLimb rh0) := by
    rw [← limbVal_rLimb_take rh 24 (le_refl _), i2, limbVal_rLimb_take rh0 24 (le_refl _)]
  rw [h3, er, blocksAcc_mod, i3, ← blocksAcc_mod, ← blocksAcc_append _ _ _ _ _ (by simp; omega),
    List.take_add]

theorem and_mask_hi (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n &&& 0xfffffffffffffff0#64) = BitVec.ofNat 64 (16 * (n / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,
    show (0xfffffffffffffff0#64 : BitVec 64).toNat = 2 ^ 4 * (2 ^ 60 - 1) + 0 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)]
  have hq : n / 16 < 2 ^ 60 := by omega
  have e : n = 2 ^ 4 * (n / 16) + n % 16 := by omega
  rw [show 16 * (n / 16) = 2 ^ 4 * (n / 16) + 0 by omega]
  conv_lhs => rw [e]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ (by omega),
    Nat.testBit_two_pow_mul_add _ (by norm_num), Nat.testBit_two_pow_mul_add _ (by norm_num)]
  split
  · simp
  · rw [Nat.testBit_two_pow_sub_one]
    by_cases h : i - 4 < 60
    · simp [h]
    · simp only [h, decide_false, Bool.and_false]
      symm
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem bytesIn_split (ro : Bool) (p : BitVec 64) (I : List (BitVec 8)) (k : Nat)
    (hk : k ≤ I.length) :
    bytesIn ro p I = bytesIn ro p (I.take k) ∗ bytesIn ro (p + BitVec.ofNat 64 k) (I.drop k) := by
  cases ro
  · simp only [bytesIn, Bool.false_eq_true, ↓reduceIte]; exact pointsToBytes_split p I k hk
  · simp only [bytesIn, ↓reduceIte]; exact pointsToBytesRO_split p I k hk

theorem ofNat_sub_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega

theorem ofNat_eq_zero (k : Nat) (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k = 0#64) ↔ k = 0 := by
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    simp at this
    omega
  · rintro rfl; rfl

end Poly1305Debian.UD

end
end

section
section
/-! # Calling `poly1305_blocks` (text offset 416) through its contract

`BlocksOk16` is `blocksSpec` at `poly1305_blocks` for messages whose length is a multiple of 16,
the only ones `poly1305_update` passes. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.UD

open Arm64 Arm64.Obj Poly1305Boringssl
open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

/-- `blocksSpec` holds at `poly1305_blocks` for every message of length a multiple of 16. -/
def BlocksOk16 (pl : Placement) (X : String → Option (State → State)) : Prop :=
  ∀ (ro : Bool) (rh : List (BitVec 8)) (fin : BitVec 8) (msg : List (BitVec 8)),
    msg.length % 16 = 0 → ∀ (R : SepProp) (s0 : State),
      s0.pc = pl.base + BitVec.ofNat 64 416 → s0.status = .Running →
      (s0.mem ⊨ blocksSpec.pre (ro, rh, fin, msg) s0 ∗ R) → s0.spAligned = true →
      reaches_outcome (P pl X) blocksSpec (ro, rh, fin, msg) R s0 s0

set_option maxHeartbeats 4000000 in
/-- A `bl poly1305_blocks` at `pc` with `x0 = a`, `x1 = q`, `x2 = |msg|`, through `blocksSpec`. -/
theorem call_blocks {pl : Placement} {X : String → Option (State → State)} (hB : BlocksOk16 pl X)
    {Q : State → Prop}
    {sb : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {T : BitVec 64} {ps : PState}
    {m : Memory} {v : BitVec 5 → BitVec 128} {ro : Bool} {rh msg : List (BitVec 8)}
    {fin : BitVec 8} {a q : BitVec 64} {Fr : SepProp}
    (hrun : sb.status = .Running)
    {off : BitVec 64} (hf : (P pl X).fetchMem m pc = some (.bl off))
    (hoff : pc + off = pl.base + BitVec.ofNat 64 416)
    (hTal : T &&& 0b1111#64 = 0#64) (hCL : (P pl X).CodeLoaded m)
    (h0 : r 0#5 = a) (h1 : r 1#5 = q) (h2 : (r 2#5).toNat = msg.length) (h16 : 16 ≤ msg.length)
    (hmod : msg.length % 16 = 0) (hok : StateOk rh)
    (hm : m ⊨ (a ↦ₛ rh) ∗ ((a + 88#64) ↦ₛ [fin]) ∗ bytesIn ro q msg ∗ Fr)
    (hcont : ∀ sf : State, sf.status = .Running → sf.pc = pc + 4#64 → sf.sp = T →
      KeptRegs sf r → calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      (P pl X).CodeLoaded sf.mem → sf.regs.regs 0#5 = a → sf.regs.regs 18#5 = r 18#5 →
      ∀ rh' : List (BitVec 8), StateOk rh' → rh'.take 24 = rh.take 24 →
      limbVal (hLimb rh') % p1305 =
        blocksAcc (limbVal (rLimb rh)) (hibit fin) (limbVal (hLimb rh)) msg % p1305 →
      (sf.mem ⊨ (a ↦ₛ rh') ∗ ((a + 88#64) ↦ₛ [fin]) ∗ bytesIn ro q msg ∗ Fr) →
      Reach (P pl X) sf Q) :
    Reach (P pl X) (mkS sb pc r T ps m v) Q := by
  have e0 : (mkS sb (pl.base + BitVec.ofNat 64 416) (upd r 30#5 (pc + 4#64)) T ps m v).readReg64
      Reg.x0 = a := by simp [Reg.x0, h0]
  have e1 : (mkS sb (pl.base + BitVec.ofNat 64 416) (upd r 30#5 (pc + 4#64)) T ps m v).readReg64
      Reg.x1 = q := by simp [Reg.x1, h1]
  have e2 : ((mkS sb (pl.base + BitVec.ofNat 64 416) (upd r 30#5 (pc + 4#64)) T ps m v).readReg64
      Reg.x2).toNat = msg.length := by simp [Reg.x2, h2]
  have e18 : (mkS sb (pl.base + BitVec.ofNat 64 416) (upd r 30#5 (pc + 4#64)) T ps m v).readReg64
      Reg.x18 = r 18#5 := by simp [Reg.x18]
  have hoff' : off = pl.base + BitVec.ofNat 64 416 - pc := by rw [← hoff]; bv_omega
  rw [hoff'] at hf
  refine call_ok blocksSpec (ro, rh, fin, msg) (hB ro rh fin msg hmod) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) Fr hrun hf hTal hCL ?_ ?_
  · simp only [blocksSpec, e0, e1, e2]
    rw [sepConj_assoc, sat_pure_sep]
    exact ⟨⟨hok, trivial, h16⟩, Satisfies.of_eq hm⟩
  intro sf hrunf hpcf hspf hkr hvf hkf hpost
  simp only [blocksSpec, e0, e1, e18] at hpost
  rw [sepConj_assoc, sat_pure_sep] at hpost
  obtain ⟨⟨hx0, hx18⟩, hpost⟩ := hpost
  rw [sepConj_assoc, sepExists_sepConj, sat_sepExists] at hpost
  obtain ⟨rh', hpost⟩ := hpost
  have hp2 := Satisfies.of_eq hpost (Q := ⌜StateOk rh' ∧ rh'.take 24 = rh.take 24 ∧
      limbVal (hLimb rh') % p1305 =
        blocksAcc (limbVal (rLimb rh)) (hibit fin) (limbVal (hLimb rh)) msg % p1305⌝ ∗
    ((a ↦ₛ rh') ∗ ((a + 88#64) ↦ₛ [fin]) ∗ bytesIn ro q msg ∗ Fr))
  rw [sat_pure_sep] at hp2
  obtain ⟨⟨hok', ht, hh⟩, hp2⟩ := hp2
  have hx0' : sf.regs.regs 0#5 = a := by
    have := hx0; simp [readGpr_unfold, Reg.x0] at this; exact this
  have hx18' : sf.regs.regs 18#5 = r 18#5 := by
    have := hx18; simp [readGpr_unfold, Reg.x18] at this; exact this
  exact hcont sf hrunf hpcf hspf hkr hvf hkf hx0' hx18' rh' hok' ht hh hp2

end Poly1305Debian.UD

end
end

section
section
/-! # `poly1305_update`, text offsets 828–936: "process full blocks", then "store leftover"

With `leftover = 0`, the first `K` pending bytes absorbed (`Inv`), `x18` at the message's byte `j`
and `x4 = c` bytes left: when `c > 15` it calls `poly1305_blocks` on the largest multiple of 16;
the rest (fewer than 16 bytes) goes to the buffer (`seg_copy`) or, when none is left, to the
epilogue at 784. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.UD

open Arm64 Arm64.Obj Poly1305Boringssl
open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

theorem bytesIn_three (ro : Bool) (p : BitVec 64) (msg : List (BitVec 8)) (j B : Nat)
    (h : j + B ≤ msg.length) :
    bytesIn ro p msg = bytesIn ro p (msg.take j) ∗
      (bytesIn ro (p + BitVec.ofNat 64 j) ((msg.drop j).take B) ∗
        bytesIn ro (p + BitVec.ofNat 64 j + BitVec.ofNat 64 B) ((msg.drop j).drop B)) := by
  rw [bytesIn_split ro p msg j (by omega),
    bytesIn_split ro (p + BitVec.ofNat 64 j) (msg.drop j) B (by simp; omega)]

theorem hi15 (x : BitVec 64) :
    ConditionHolds .HI (AddWithCarry64 x (~~~((0x00f#12 : BitVec 12).zeroExtend 64)) true).2 =
      decide (15 < x.toNat) := by
  rw [hi_cmp]; rfl

set_option maxHeartbeats 8000000 in
theorem seg_tail {pl : Placement} (hP : libsodiumDebianOnetimeauthLib.Placeable pl)
    {X : String → Option (State → State)} (hB : BlocksOk16 pl X) {Q : State → Prop}
    {T a p : BitVec 64} {ro : Bool} {msg pad rest rh0 t : List (BitVec 8)} {fin : BitVec 8}
    {r0 : BitVec 5 → BitVec 64} {v0 : BitVec 5 → BitVec 128} {x29 x30 : BitVec 64} {R : SepProp}
    (K784 : ExitK pl X Q (pl.base + 784#64) T a p ro msg pad rest rh0 t fin r0 v0 x29 x30 R)
    (K892 : ExitK pl X Q (pl.base + 892#64) T a p ro msg pad rest rh0 t fin r0 v0 x29 x30 R)
    (hTal : T &&& 0b1111#64 = 0#64)
    {sb : State} {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128}
    (hrun : sb.status = .Running) (hCL : (P pl X).CodeLoaded m) (hkept : Kept r r0)
    (hr0 : r 0#5 = a) (hv : VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨v0⟩)
    (j c K : Nat) (hlen : msg.length = j + c) (hml : msg.length < 2 ^ 64)
    (ht : t.length = K + c) (htd : t.drop K = msg.drop j) (hK : K % 16 = 0)
    (hr18 : r 18#5 = p + BitVec.ofNat 64 j) (hr4 : r 4#5 = BitVec.ofNat 64 c)
    (rh buf : List (BitVec 8)) (hbuf : buf.length = 16) (u2 u3 : BitVec 64)
    (hI : Inv rh0 fin t K rh)
    (hm : m ⊨ Fields a rh pad 0#64 buf fin rest ∗ bytesIn ro p msg ∗ Cells4 T x29 x30 u2 u3 ∗ R) :
    Reach (P pl X) (mkS sb (pl.base + 828#64) r T ps m v) Q := by
  have hc64 : c < 2 ^ 64 := by omega
  -- 828: cmp x4, #15
  refine Reach.mkC hrun hCL (f_8c hP hCL) ?_
  rw [ex_cmp_imm 4#5 (by decide), hr4, pc_add]
  intro hCL1
  -- 832: b.hi 904
  refine Reach.mkC hrun hCL1 (f_90 hP hCL1) ?_
  rw [ex_bcond, hi15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc64]
  intro hCL2
  simp only [mkS_mem] at hCL1 hCL2
  by_cases hc15 : 15 < c
  swap
  · -- c ≤ 15
    simp only [hc15, decide_false, Bool.false_eq_true, if_false, pc_add]
    -- 836: cbz x4, 784
    refine Reach.mkC hrun hCL2 (f_94 hP hCL2) ?_
    rw [ex_cbz 4#5 (by decide), hr4]
    by_cases hc0 : c = 0
    · have e0 : BitVec.ofNat 64 c = 0#64 := by rw [hc0]
      simp only [e0, if_true]
      intro hCL3
      simp only [mkS_mem] at hCL3
      rw [show pl.base + BitVec.ofNat 64 (828 + 4 + 4) + 0xffffffffffffffcc#64 = pl.base + 784#64
        by bv_omega]
      exact K784 sb r _ m v rh buf 0#64 u2 u3 hrun hCL3 hkept hr0 hv
        (good_exit0 (by omega) hK hbuf hI) hm
    · have e0 : BitVec.ofNat 64 c ≠ 0#64 := fun e => hc0 ((ofNat_eq_zero c hc64).mp e)
      simp only [e0, if_false, pc_add]
      intro hCL3
      simp only [mkS_mem] at hCL3
      exact seg_copy hP K892 hrun hCL3 hkept hr0 hv j c (by omega) (by omega) hlen hr18 hr4
        rh buf hbuf u2 u3
        (good_copy (K := K) (c := c) ht hK (by omega) htd (by simp; omega) hbuf hI) hm
  · -- c > 15
    simp only [hc15, decide_true, if_true]
    rw [show pl.base + BitVec.ofNat 64 (828 + 4) + 0x0000000000000048#64 = pl.base + 904#64
      by bv_omega]
    set B := 16 * (c / 16) with hBdef
    have hB16 : 16 ≤ B := by omega
    -- 904: and x2, x4, #~15
    refine Reach.mkC hrun hCL2 (f_d8 hP hCL2) ?_
    rw [ex_and_imm 2#5 4#5 (by decide) (by decide), hr4, and_mask_hi c hc64, pc_add]
    intro hCL3
    -- 908: mov x1, x18
    refine Reach.mkC hrun hCL3 (f_dc hP hCL3) ?_
    rw [ex_mov 1#5 18#5 (by decide) (by decide), pc_add]
    intro hCL4
    simp only [mkS_mem] at hCL3 hCL4
    generalize hr3 : upd (upd r 2#5 (BitVec.ofNat 64 B)) 1#5 (upd r 2#5 (BitVec.ofNat 64 B) 18#5)
      = r3
    have h32 : r3 2#5 = BitVec.ofNat 64 B := by rw [← hr3]; simp [upd_apply]
    have h34 : r3 4#5 = BitVec.ofNat 64 c := by rw [← hr3]; simp [upd_apply, hr4]
    have h30 : r3 0#5 = a := by rw [← hr3]; simp [upd_apply, hr0]
    have h31 : r3 1#5 = p + BitVec.ofNat 64 j := by rw [← hr3]; simp [upd_apply, hr18]
    have h318 : r3 18#5 = p + BitVec.ofNat 64 j := by rw [← hr3]; simp [upd_apply, hr18]
    have hk3 : Kept r3 r0 := by
      rw [← hr3]; exact (hkept.upd 2#5 (by decide) _).upd 1#5 (by decide) _
    -- 912: stp x2, x4, [sp, #16]
    generalize hW : Fields a rh pad 0#64 buf fin rest ∗ bytesIn ro p msg ∗ R = W
    have hm1 : m ⊨ ((T + 0x10#64) ↦₆₄ u2) ∗ (((T + 0x10#64 + 8#64) ↦₆₄ u3) ∗
        (T ↦₆₄ x29) ∗ ((T + 8#64) ↦₆₄ x30) ∗ W) :=
      Satisfies.of_eq hm (by rw [← hW]; simp only [Cells4]; ac_rfl)
    have c2 := sat64_read hm1
    have hm1' : m ⊨ ((T + 0x10#64 + 8#64) ↦₆₄ u3) ∗ (((T + 0x10#64) ↦₆₄ u2) ∗
        (T ↦₆₄ x29) ∗ ((T + 8#64) ↦₆₄ x30) ∗ W) := Satisfies.of_eq hm1
    have c3 := sat64_read hm1'
    refine Reach.mkC hrun hCL4 (f_e0 hP hCL4) ?_
    rw [ex_stp64_sp 2#5 4#5 (by decide) (by decide) 0x10#64 hTal c2.2.2 c3.2.2, h32, h34, pc_add]
    intro hCL5
    simp only [mkS_mem] at hCL5
    have hm2 := sat64_write (Satisfies.of_eq (sat64_write hm1 (BitVec.ofNat 64 B))
      (Q := ((T + 0x10#64 + 8#64) ↦₆₄ u3) ∗ (((T + 0x10#64) ↦₆₄ BitVec.ofNat 64 B) ∗
        (T ↦₆₄ x29) ∗ ((T + 8#64) ↦₆₄ x30) ∗ W))) (BitVec.ofNat 64 c)
    generalize hm5 : (m.write64 (T + 0x10#64) (BitVec.ofNat 64 B)).write64 (T + 0x10#64 + 8#64)
      (BitVec.ofNat 64 c) = m5 at hm2 hCL5 ⊢
    rw [← hW, bytesIn_three ro p msg j B (by omega)] at hm2
    simp only [Fields] at hm2
    have hm3 : m5 ⊨ (a ↦ₛ rh) ∗ ((a + 88#64) ↦ₛ [fin]) ∗
        bytesIn ro (p + BitVec.ofNat 64 j) ((msg.drop j).take B) ∗
        (((a + 72#64) ↦ₛ buf) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗ ((a + 48#64) ↦ₛ pad) ∗
          ((a + 89#64) ↦ₛ rest) ∗ bytesIn ro p (msg.take j) ∗
          bytesIn ro (p + BitVec.ofNat 64 j + BitVec.ofNat 64 B) ((msg.drop j).drop B) ∗
          Cells4 T x29 x30 (BitVec.ofNat 64 B) (BitVec.ofNat 64 c) ∗ R) :=
      Satisfies.of_eq hm2 (by simp only [Cells4]; ac_rfl)
    -- 916: bl poly1305_blocks
    have hBl : ((msg.drop j).take B).length = B := by simp; omega
    refine call_blocks hB hrun (f_e4 hP hCL5) (by bv_omega) hTal hCL5 h30 h31
      (by rw [h32, hBl, BitVec.toNat_ofNat]; omega) (by omega) (by omega) hI.1 hm3 ?_
    intro sf hrunf hpcf hspf hkr hvf hCLf hx0 hx18 rh2 hok2 ht2 hh2 hmf
    rw [← mkS_self sf, hpcf, hspf]
    have hkf : Kept sf.regs.regs r0 := hk3.keptRegs hkr
    have hI2 : Inv rh0 fin t (K + B) rh2 :=
      inv_step hK (by omega) (by omega) hI hok2 ht2 (by rw [htd]; exact hh2)
    have hvf' : VRegFile.calleeSaved sf.vregs = VRegFile.calleeSaved ⟨v0⟩ := by
      rw [← hv]; exact hvf
    -- 920: ldp x2, x4, [sp, #16]
    have hmf1 : sf.mem ⊨ ((T + 0x10#64) ↦₆₄ BitVec.ofNat 64 B) ∗
        (((T + 0x10#64 + 8#64) ↦₆₄ BitVec.ofNat 64 c) ∗ (T ↦₆₄ x29) ∗ ((T + 8#64) ↦₆₄ x30) ∗
        ((a ↦ₛ rh2) ∗ ((a + 88#64) ↦ₛ [fin]) ∗
        bytesIn ro (p + BitVec.ofNat 64 j) ((msg.drop j).take B) ∗
        ((a + 72#64) ↦ₛ buf) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗ ((a + 48#64) ↦ₛ pad) ∗
          ((a + 89#64) ↦ₛ rest) ∗ bytesIn ro p (msg.take j) ∗
          bytesIn ro (p + BitVec.ofNat 64 j + BitVec.ofNat 64 B) ((msg.drop j).drop B) ∗ R)) :=
      Satisfies.of_eq hmf (by simp only [Cells4]; ac_rfl)
    have d2 := sat64_read hmf1
    have d3 := sat64_read (Satisfies.of_eq hmf1 (Q := ((T + 0x10#64 + 8#64) ↦₆₄ BitVec.ofNat 64 c) ∗
      (((T + 0x10#64) ↦₆₄ BitVec.ofNat 64 B) ∗ (T ↦₆₄ x29) ∗ ((T + 8#64) ↦₆₄ x30) ∗
        ((a ↦ₛ rh2) ∗ ((a + 88#64) ↦ₛ [fin]) ∗
        bytesIn ro (p + BitVec.ofNat 64 j) ((msg.drop j).take B) ∗
        ((a + 72#64) ↦ₛ buf) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗ ((a + 48#64) ↦ₛ pad) ∗
          ((a + 89#64) ↦ₛ rest) ∗ bytesIn ro p (msg.take j) ∗
          bytesIn ro (p + BitVec.ofNat 64 j + BitVec.ofNat 64 B) ((msg.drop j).drop B) ∗ R))))
    rw [pc_add]
    refine Reach.mkC hrunf hCLf (f_e8 hP hCLf) ?_
    rw [ex_ldp64_sp 2#5 4#5 (by decide) (by decide) 0x10#64 hTal d2.2.1 d3.2.1, d2.1, d3.1, pc_add]
    intro hCL6
    -- 924: add x18, x18, x2
    refine Reach.mkC hrunf hCL6 (f_ec hP hCL6) ?_
    rw [ex_add_shift0 18#5 18#5 2#5 (by decide) (by decide) (by decide), pc_add]
    intro hCL7
    -- 928: sub x4, x4, x2
    refine Reach.mkC hrunf hCL7 (f_f0 hP hCL7) ?_
    rw [ex_sub_shift0 4#5 4#5 2#5 (by decide) (by decide) (by decide), pc_add]
    intro hCL8
    simp only [mkS_mem] at hCL6 hCL7 hCL8
    generalize hr9 : upd (upd (upd (upd sf.regs.regs 2#5 (BitVec.ofNat 64 B)) 4#5
      (BitVec.ofNat 64 c)) 18#5 (upd (upd sf.regs.regs 2#5 (BitVec.ofNat 64 B)) 4#5
      (BitVec.ofNat 64 c) 18#5 + upd (upd sf.regs.regs 2#5 (BitVec.ofNat 64 B)) 4#5
      (BitVec.ofNat 64 c) 2#5)) 4#5 (upd (upd (upd sf.regs.regs 2#5 (BitVec.ofNat 64 B)) 4#5
      (BitVec.ofNat 64 c)) 18#5 (upd (upd sf.regs.regs 2#5 (BitVec.ofNat 64 B)) 4#5
      (BitVec.ofNat 64 c) 18#5 + upd (upd sf.regs.regs 2#5 (BitVec.ofNat 64 B)) 4#5
      (BitVec.ofNat 64 c) 2#5) 4#5 - upd (upd (upd sf.regs.regs 2#5 (BitVec.ofNat 64 B)) 4#5
      (BitVec.ofNat 64 c)) 18#5 (upd (upd sf.regs.regs 2#5 (BitVec.ofNat 64 B)) 4#5
      (BitVec.ofNat 64 c) 18#5 + upd (upd sf.regs.regs 2#5 (BitVec.ofNat 64 B)) 4#5
      (BitVec.ofNat 64 c) 2#5) 2#5) = r9
    have h94 : r9 4#5 = BitVec.ofNat 64 (c - B) := by
      rw [← hr9]; simp [upd_apply]; exact ofNat_sub_ofNat c B hc64 (by omega)
    have h918 : r9 18#5 = p + BitVec.ofNat 64 (j + B) := by
      rw [← hr9]; simp [upd_apply, hx18, h318, pc_add]
    have h90 : r9 0#5 = a := by rw [← hr9]; simp [upd_apply, hx0]
    have hk9 : Kept r9 r0 := by
      rw [← hr9]
      exact (((hkf.upd 2#5 (by decide) _).upd 4#5 (by decide) _).upd 18#5 (by decide) _).upd 4#5
        (by decide) _
    have hmf2 : sf.mem ⊨ Fields a rh2 pad 0#64 buf fin rest ∗ bytesIn ro p msg ∗
        Cells4 T x29 x30 (BitVec.ofNat 64 B) (BitVec.ofNat 64 c) ∗ R := by
      rw [bytesIn_three ro p msg j B (by omega)]
      simp only [Fields]
      exact Satisfies.of_eq hmf
    -- 932: cbz x4, 784
    refine Reach.mkC hrunf hCL8 (f_f4 hP hCL8) ?_
    rw [ex_cbz 4#5 (by decide), h94]
    by_cases hcB : c - B = 0
    · have e0 : BitVec.ofNat 64 (c - B) = 0#64 := by rw [hcB]
      simp only [e0, if_true]
      intro hCL9
      simp only [mkS_mem] at hCL9
      rw [show pl.base + BitVec.ofNat 64 (916 + 4 + 4 + 4 + 4) + 0xffffffffffffff6c#64 =
        pl.base + 784#64 by bv_omega]
      exact K784 sf r9 _ sf.mem _ rh2 buf 0#64 _ _ hrunf hCL9 hk9 h90 hvf'
        (good_exit0 (by omega) (by omega) hbuf hI2) hmf2
    · have e0 : BitVec.ofNat 64 (c - B) ≠ 0#64 := fun e => hcB ((ofNat_eq_zero _ (by omega)).mp e)
      simp only [e0, if_false, pc_add]
      intro hCL9
      simp only [mkS_mem] at hCL9
      -- 936: b 840
      refine Reach.mkC hrunf hCL9 (f_f8 hP hCL9) ?_
      rw [ex_b, show pl.base + BitVec.ofNat 64 (916 + 4 + 4 + 4 + 4 + 4) + 0xffffffffffffffa0#64 =
        pl.base + 840#64 by bv_omega]
      intro hCL10
      simp only [mkS_mem] at hCL10
      have htd2 : t.drop (K + B) = msg.drop (j + B) := by
        rw [← List.drop_drop, htd, List.drop_drop]
      exact seg_copy hP K892 hrunf hCL10 hk9 h90 hvf' (j + B) (c - B) (by omega) (by omega)
        (by omega) h918 h94 rh2 buf hbuf _ _
        (good_copy (K := K + B) (c := c - B) (by omega) (by omega) (by omega) htd2
          (by simp; omega) hbuf hI2) hmf2

end Poly1305Debian.UD

end
end

section
section
/-! # `poly1305_update`, text offsets 716–824: "handle leftover"

With `L = leftover` in `1..15`: `w = min (16 - L, n)` bytes of the message go into the buffer at
`L`; if the buffer is then full (`L + w = 16`) `poly1305_blocks` absorbs it, `leftover` becomes `0`
and the rest of the message goes on at 828 (`seg_tail`); otherwise `leftover = L + n` and the
function returns (epilogue at 784). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.UD

open Arm64 Arm64.Obj Poly1305Boringssl
open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

theorem ls_cmp (x y : BitVec 64) :
    ConditionHolds .LS (AddWithCarry64 x (~~~y) true).2 = decide (x.toNat ≤ y.toNat) := by
  simp only [ConditionHolds, c_eq, res_eq]
  rcases Nat.lt_or_ge x.toNat y.toNat with h | h
  · have h1 : ¬ y.toNat ≤ x.toNat := by omega
    simp [h1, Nat.le_of_lt h]
  · by_cases he : x = y
    · subst he; simp
    · have hlt : y.toNat < x.toNat :=
        lt_of_le_of_ne h (fun e => he (BitVec.eq_of_toNat_eq e.symm))
      have h2 : ¬ x.toNat ≤ y.toNat := by omega
      simp [h, he, h2]

theorem copyInto_take (buf d : List (BitVec 8)) (L : Nat) (hL : L + d.length ≤ buf.length) :
    (copyInto buf L d).take (L + d.length) = buf.take L ++ d := by
  unfold copyInto
  have h1 : (buf.take L).length = L := by simp; omega
  rw [List.append_assoc, List.take_append, h1, Nat.add_sub_cancel_left,
    List.take_of_length_le (by omega : (buf.take L).length ≤ L + d.length), List.take_left' rfl]

theorem inv_zero (rh0 : List (BitVec 8)) (fin : BitVec 8) (t : List (BitVec 8))
    (h : StateOk rh0) : Inv rh0 fin t 0 rh0 := by
  refine ⟨h, rfl, ?_⟩
  rw [List.take_zero, blocksAcc_short _ _ _ _ (by simp)]

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_sub_shift0' (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (z : BitVec 64) (hz : r n - r k = z) :
    execInstWithSvc svc (.addSubShift .W64 .SUB (.gpr d) (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) (upd r d z) sp ps m v := by
  rw [ex_sub_shift0 d n k hd hn hk, hz]

theorem ex_add_shift0' (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (z : BitVec 64) (hz : r n + r k = z) :
    execInstWithSvc svc (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) (upd r d z) sp ps m v := by
  rw [ex_add_shift0 d n k hd hn hk, hz]

theorem ex_add_imm' (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (imm : BitVec 12)
    (z : BitVec 64) (hz : r n + imm.zeroExtend 64 = z) :
    execInstWithSvc svc (.addSubImm .W64 .ADD (.gpr d) (.gpr n) imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d z) sp ps m v := by
  rw [ex_add_imm d n hd hn imm, hz]

theorem ex_movz64' (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 16) (z : BitVec 64)
    (hz : imm.zeroExtend 64 = z) :
    execInstWithSvc svc (.moveWide .W64 .MOVZ (.gpr d) imm 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d z) sp ps m v := by
  rw [ex_movz64 d hd imm, hz]

end exec

set_option maxHeartbeats 8000000 in
/-- From offset 768 (`add x6, x6, x1`), with `w` bytes copied into the buffer at `L`. -/
theorem seg_768 {pl : Placement} (hP : libsodiumDebianOnetimeauthLib.Placeable pl)
    {X : String → Option (State → State)} (hB : BlocksOk16 pl X) {Q : State → Prop}
    {T a p : BitVec 64} {ro : Bool} {msg pad rest rh0 : List (BitVec 8)} {fin : BitVec 8}
    {r0 : BitVec 5 → BitVec 64} {v0 : BitVec 5 → BitVec 128} {x29 x30 : BitVec 64} {R : SepProp}
    {buf0 : List (BitVec 8)} {L : Nat}
    (K784 : ExitK pl X Q (pl.base + 784#64) T a p ro msg pad rest rh0 (buf0.take L ++ msg) fin r0
      v0 x29 x30 R)
    (K892 : ExitK pl X Q (pl.base + 892#64) T a p ro msg pad rest rh0 (buf0.take L ++ msg) fin r0
      v0 x29 x30 R)
    (hTal : T &&& 0b1111#64 = 0#64)
    {sb : State} {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128}
    (hrun : sb.status = .Running) (hCL : (P pl X).CodeLoaded m) (hkept : Kept r r0)
    (hr0 : r 0#5 = a) (hv : VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨v0⟩)
    (hml : msg.length < 2 ^ 64) (hL0 : 0 < L) (hL16 : L < 16) (hbuf : buf0.length = 16)
    (hok : StateOk rh0) (w : Nat) (hw : w = min (16 - L) msg.length)
    (hr1 : r 1#5 = BitVec.ofNat 64 w) (hr6 : r 6#5 = BitVec.ofNat 64 L)
    (hr18 : r 18#5 = p) (hr4 : r 4#5 = BitVec.ofNat 64 msg.length) (u2 u3 : BitVec 64)
    (hm : m ⊨ Fields a rh0 pad (BitVec.ofNat 64 L) (copyInto buf0 L (msg.take w)) fin rest ∗
      bytesIn ro p msg ∗ Cells4 T x29 x30 u2 u3 ∗ R) :
    Reach (P pl X) (mkS sb (pl.base + 768#64) r T ps m v) Q := by
  have hwl : (msg.take w).length = w := by simp; omega
  have hb1 : (copyInto buf0 L (msg.take w)).length = 16 := by simp [copyInto, hbuf]; omega
  -- 768: add x6, x6, x1
  refine Reach.mkC hrun hCL (f_50 hP hCL) ?_
  rw [ex_add_shift0 6#5 6#5 1#5 (by decide) (by decide) (by decide), hr6, hr1, ← BitVec.ofNat_add,
    pc_add]
  intro hCL1
  simp only [mkS_mem] at hCL1
  -- 772: str x6, [x0, #0x40]
  generalize hW : (a ↦ₛ rh0) ∗ ((a + 88#64) ↦ₛ [fin]) ∗ ((a + 48#64) ↦ₛ pad) ∗
    ((a + 89#64) ↦ₛ rest) ∗ bytesIn ro p msg ∗ Cells4 T x29 x30 u2 u3 ∗ R = W
  have hm1 : m ⊨ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 L) ∗
      (((a + 72#64) ↦ₛ copyInto buf0 L (msg.take w)) ∗ W) :=
    Satisfies.of_eq hm (by rw [← hW]; simp only [Fields]; ac_rfl)
  have c0 := sat64_read hm1
  refine Reach.mkC hrun hCL1 (f_54 hP hCL1) ?_
  rw [ex_str64_gpr 6#5 0#5 (by decide) (by decide) _
    (by rw [upd_ne _ _ (by decide), hr0]; exact c0.2.2), upd_same, upd_ne _ _ (by decide), hr0,
    pc_add]
  intro hCL2
  simp only [mkS_mem] at hCL2
  have hm2 := sat64_write hm1 (BitVec.ofNat 64 (L + w))
  generalize hm3 : m.write64 (a + 64#64) (BitVec.ofNat 64 (L + w)) = m3 at hm2 hCL2 ⊢
  -- 776: cmp x6, #15
  refine Reach.mkC hrun hCL2 (f_58 hP hCL2) ?_
  rw [ex_cmp_imm 6#5 (by decide), upd_same, pc_add]
  intro hCL3
  -- 780: b.hi 796
  refine Reach.mkC hrun hCL3 (f_5c hP hCL3) ?_
  rw [ex_bcond, hi15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  intro hCL4
  simp only [mkS_mem] at hCL3 hCL4
  have hk1 : Kept (upd r 6#5 (BitVec.ofNat 64 (L + w))) r0 := hkept.upd 6#5 (by decide) _
  by_cases hfull : 15 < L + w
  swap
  · -- the buffer is not full: return
    simp only [hfull, decide_false, Bool.false_eq_true, if_false, pc_add]
    have hwn : w = msg.length := by omega
    refine K784 sb _ _ m3 v rh0 (copyInto buf0 L (msg.take w)) (BitVec.ofNat 64 (L + w)) u2 u3
      hrun hCL4 hk1 (by rw [upd_ne _ _ (by decide), hr0]) hv ?_ ?_
    · have htl : (buf0.take L ++ msg).length = L + w := by simp; omega
      have hk0 : 16 * ((buf0.take L ++ msg).length / 16) = 0 := by rw [htl]; omega
      refine ⟨hok.1, hb1, hok, rfl, ?_, ?_, ?_⟩
      · rw [hk0, htl]; simp; omega
      · rw [hk0, htl, Nat.sub_zero, List.drop_zero]
        have := copyInto_take buf0 (msg.take w) L (by rw [hwl, hbuf]; omega)
        rw [hwl] at this
        rw [this, hwn, List.take_length]
      · rw [hk0, List.take_zero, blocksAcc_short _ _ _ _ (by simp)]
    · rw [← hW] at hm2
      simp only [Fields]
      exact Satisfies.of_eq hm2
  · -- the buffer is full: absorb it
    simp only [hfull, decide_true, if_true]
    rw [show pl.base + BitVec.ofNat 64 (768 + 4 + 4 + 4) + 0x0000000000000010#64 =
      pl.base + 796#64 by bv_omega]
    have hw16 : L + w = 16 := by omega
    have hwn : w ≤ msg.length := by omega
    have hn64 : msg.length < 2 ^ 64 := hml
    -- 796: sub x4, x4, x1
    refine Reach.mkC hrun hCL4 (f_6c hP hCL4) ?_
    rw [ex_sub_shift0' 4#5 4#5 1#5 (by decide) (by decide) (by decide)
      (BitVec.ofNat 64 (msg.length - w))
      (by simp only [upd_apply]; simp; rw [hr4, hr1]; exact ofNat_sub_ofNat _ _ hml hwn), pc_add]
    intro hCL5
    -- 800: add x18, x18, x1
    refine Reach.mkC hrun hCL5 (f_70 hP hCL5) ?_
    rw [ex_add_shift0' 18#5 18#5 1#5 (by decide) (by decide) (by decide) (p + BitVec.ofNat 64 w)
      (by simp only [upd_apply]; simp; rw [hr18, hr1]), pc_add]
    intro hCL6
    -- 804: mov x2, #16
    refine Reach.mkC hrun hCL6 (f_74 hP hCL6) ?_
    rw [ex_movz64' 2#5 (by decide) _ 16#64 rfl, pc_add]
    intro hCL7
    -- 808: add x1, x0, #0x48
    refine Reach.mkC hrun hCL7 (f_78 hP hCL7) ?_
    rw [ex_add_imm' 1#5 0#5 (by decide) (by decide) _ (a + 72#64)
      (by simp only [upd_apply]; simp; rw [hr0]), pc_add]
    intro hCL8
    simp only [mkS_mem] at hCL5 hCL6 hCL7 hCL8
    generalize hrc : upd (upd (upd (upd (upd r 6#5 (BitVec.ofNat 64 (L + w))) 4#5
      (BitVec.ofNat 64 (msg.length - w))) 18#5 (p + BitVec.ofNat 64 w)) 2#5 16#64) 1#5
      (a + 72#64) = rc
    have hc0 : rc 0#5 = a := by rw [← hrc]; simp [upd_apply, hr0]
    have hc1 : rc 1#5 = a + 72#64 := by rw [← hrc]; simp [upd_apply]
    have hc2 : rc 2#5 = 16#64 := by rw [← hrc]; simp [upd_apply]
    have hc4 : rc 4#5 = BitVec.ofNat 64 (msg.length - w) := by rw [← hrc]; simp [upd_apply]
    have hc18 : rc 18#5 = p + BitVec.ofNat 64 w := by rw [← hrc]; simp [upd_apply]
    have hkc : Kept rc r0 := by
      rw [← hrc]
      exact ((((hk1.upd 4#5 (by decide) _).upd 18#5 (by decide) _).upd 2#5 (by decide) _).upd 1#5
        (by decide) _)
    show Reach (P pl X) (mkS sb _ rc T _ m3 v) Q
    -- 812: str x4, [sp, #16]
    generalize hbuf1 : copyInto buf0 L (msg.take w) = buf1 at hm2 hb1
    rw [← hW] at hm2
    have hm4 : m3 ⊨ ((T + 0x10#64) ↦₆₄ u2) ∗ ((a ↦ₛ rh0) ∗ ((a + 88#64) ↦ₛ [fin]) ∗
        bytesIn false (a + 72#64) buf1 ∗
        (((a + 64#64) ↦₆₄ BitVec.ofNat 64 (L + w)) ∗ ((a + 48#64) ↦ₛ pad) ∗ ((a + 89#64) ↦ₛ rest) ∗
          bytesIn ro p msg ∗ (T ↦₆₄ x29) ∗ ((T + 8#64) ↦₆₄ x30) ∗ ((T + 0x10#64 + 8#64) ↦₆₄ u3) ∗
          R)) :=
      Satisfies.of_eq hm2 (by simp only [Cells4, bytesIn, Bool.false_eq_true, if_false]; ac_rfl)
    have c4 := sat64_read hm4
    refine Reach.mkC hrun hCL8 (f_7c hP hCL8) ?_
    rw [ex_str64_sp 4#5 (by decide) 0x10#64 hTal c4.2.2, hc4, pc_add]
    intro hCL9
    simp only [mkS_mem] at hCL9
    have hm5 := sat64_write hm4 (BitVec.ofNat 64 (msg.length - w))
    generalize hm6 : m3.write64 (T + 0x10#64) (BitVec.ofNat 64 (msg.length - w)) = m6 at hm5 hCL9 ⊢
    have hm7 : m6 ⊨ (a ↦ₛ rh0) ∗ ((a + 88#64) ↦ₛ [fin]) ∗ bytesIn false (a + 72#64) buf1 ∗
        (((a + 64#64) ↦₆₄ BitVec.ofNat 64 (L + w)) ∗ ((a + 48#64) ↦ₛ pad) ∗ ((a + 89#64) ↦ₛ rest) ∗
          bytesIn ro p msg ∗ Cells4 T x29 x30 (BitVec.ofNat 64 (msg.length - w)) u3 ∗ R) :=
      Satisfies.of_eq hm5 (by simp only [Cells4]; ac_rfl)
    -- 816: bl poly1305_blocks
    refine call_blocks hB hrun (f_80 hP hCL9) (by bv_omega) hTal hCL9 hc0 hc1
      (by rw [hc2, hb1]; rfl) (by omega) (by omega) hok hm7 ?_
    intro sf hrunf hpcf hspf hkr hvf hCLf hx0 hx18 rh1 hok1 ht1 hh1 hmf
    rw [← mkS_self sf, hpcf, hspf, pc_add]
    have hkf : Kept sf.regs.regs r0 := hkc.keptRegs hkr
    have hvf' : VRegFile.calleeSaved sf.vregs = VRegFile.calleeSaved ⟨v0⟩ := by
      rw [← hv]; exact hvf
    -- 820: str xzr, [x0, #0x40]
    generalize hG : ((a + 48#64) ↦ₛ pad) ∗ ((a + 89#64) ↦ₛ rest) ∗ bytesIn ro p msg ∗
      Cells4 T x29 x30 (BitVec.ofNat 64 (msg.length - w)) u3 ∗ R = G at hmf
    have hmf1 : sf.mem ⊨ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (L + w)) ∗
        ((a ↦ₛ rh1) ∗ ((a + 88#64) ↦ₛ [fin]) ∗ bytesIn false (a + 72#64) buf1 ∗ G) :=
      Satisfies.of_eq hmf
    have d0 := sat64_read hmf1
    refine Reach.mkC hrunf hCLf (f_84 hP hCLf) ?_
    rw [ex_str64_xzr 0#5 (by decide) _ (by rw [hx0]; exact d0.2.2), hx0, pc_add]
    intro hCL10
    simp only [mkS_mem] at hCL10
    have hmf2 := sat64_write hmf1 0#64
    generalize hm8 : sf.mem.write64 (a + 64#64) 0#64 = m8 at hmf2 hCL10 ⊢
    -- 824: ldr x4, [sp, #16]
    rw [← hG] at hmf2
    have hmf3 : m8 ⊨ ((T + 0x10#64) ↦₆₄ BitVec.ofNat 64 (msg.length - w)) ∗
        (Fields a rh1 pad 0#64 buf1 fin rest ∗ bytesIn ro p msg ∗ (T ↦₆₄ x29) ∗
          ((T + 8#64) ↦₆₄ x30) ∗ ((T + 0x10#64 + 8#64) ↦₆₄ u3) ∗ R) :=
      Satisfies.of_eq hmf2 (by simp only [Fields, Cells4, bytesIn, Bool.false_eq_true, if_false]; ac_rfl)
    have d1 := sat64_read hmf3
    refine Reach.mkC hrunf hCL10 (f_88 hP hCL10) ?_
    rw [ex_ldr64_sp 4#5 (by decide) 0x10#64 hTal d1.2.1, d1.1, pc_add]
    intro hCL11
    simp only [mkS_mem] at hCL11
    -- 828: the whole blocks of the rest
    have hb1eq : buf1 = (buf0.take L ++ msg).take 16 := by
      rw [← hbuf1]
      unfold copyInto
      have e1 : (buf0.take L).length = L := by simp; omega
      rw [hwl, hw16, List.drop_eq_nil_of_le (by omega), List.append_nil, List.take_append, e1]
      congr 1
      · rw [List.take_take]; congr 1; omega
      · congr 1; omega
    have htd : (buf0.take L ++ msg).drop 16 = msg.drop w := by
      rw [List.drop_append, List.drop_eq_nil_of_le (by simp; omega), List.nil_append,
        List.length_take, Nat.min_eq_left (by omega), show 16 - L = w by omega]
    have hI1 : Inv rh0 fin (buf0.take L ++ msg) 16 rh1 :=
      inv_step (K := 0) (B := 16) rfl rfl (Nat.zero_le _) (inv_zero rh0 fin _ hok) hok1 ht1
        (by rw [List.drop_zero, ← hb1eq]; exact hh1)
    exact seg_tail hP hB K784 K892 hTal hrunf hCL11 (hkf.upd 4#5 (by decide) _)
      (by rw [upd_ne _ _ (by decide), hx0]) hvf' w (msg.length - w) 16 (by omega) hml
      (by simp; omega) htd rfl (by rw [upd_ne _ _ (by decide), hx18, hc18])
      (by rw [upd_same]) rh1 buf1 hb1 _ u3 hI1
      (Satisfies.of_eq hmf3 (by simp only [Cells4]; ac_rfl))

end Poly1305Debian.UD

end
end

section
section
/-! # `poly1305_update` (text offset 0x2b0, 63 instructions) under `updateIntSpec`

The prologue (688–712) signs the return address (`paciasp`, a hint), saves `x29, x30` in a 32-byte
frame, keeps the message pointer in `x18` and its length in `x4`, loads `leftover` and branches: to
"handle leftover" (`seg_lo`, 716) when it is nonzero, else to the whole-block path (`seg_tail`,
828). Every path ends in one of the two epilogues (784, 892), whose continuation `exit_ok` checks
the postcondition. The calls go through `BlocksOk16`, which the block routine's contract gives. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.UD

open Arm64 Arm64.Obj Poly1305Boringssl
open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk)

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_mov' (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (x : BitVec 64) (hx : r n = x) :
    execInstWithSvc svc (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr n) .LSL 0)
        (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) (upd r d x) sp ps m v := by
  rw [ex_mov d n hd hn, hx]

theorem ex_sub_shift0'' (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (z : BitVec 64) (hz : r n - r k = z) :
    execInstWithSvc svc (.addSubShift .W64 .SUB (.gpr d) (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) (upd r d z) sp ps m v := by
  rw [ex_sub_shift0 d n k hd hn hk, hz]

theorem ex_csel' (c : CondCode) (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5)
    (hk : k ≠ 31#5) (z : BitVec 64) (hz : (if ConditionHolds c ps = true then r n else r k) = z) :
    execInstWithSvc svc (.condSelect .W64 .CSEL (.gpr d) (.gpr n) (.gpr k) c)
        (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) (upd r d z) sp ps m v := by
  rw [ex_csel c d n k hd hn hk, hz]

end exec

set_option maxHeartbeats 8000000 in
/-- "handle leftover", offsets 716–764: `w = min (16 - L, n)` bytes into the buffer at `L`. -/
theorem seg_lo {pl : Placement} (hP : libsodiumDebianOnetimeauthLib.Placeable pl)
    {X : String → Option (State → State)} (hB : BlocksOk16 pl X) {Q : State → Prop}
    {T a p : BitVec 64} {ro : Bool} {msg pad rest rh0 : List (BitVec 8)} {fin : BitVec 8}
    {r0 : BitVec 5 → BitVec 64} {v0 : BitVec 5 → BitVec 128} {x29 x30 : BitVec 64} {R : SepProp}
    {buf0 : List (BitVec 8)} {L : Nat}
    (K784 : ExitK pl X Q (pl.base + 784#64) T a p ro msg pad rest rh0 (buf0.take L ++ msg) fin r0
      v0 x29 x30 R)
    (K892 : ExitK pl X Q (pl.base + 892#64) T a p ro msg pad rest rh0 (buf0.take L ++ msg) fin r0
      v0 x29 x30 R)
    (hTal : T &&& 0b1111#64 = 0#64)
    {sb : State} {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128}
    (hrun : sb.status = .Running) (hCL : (P pl X).CodeLoaded m) (hkept : Kept r r0)
    (hr0 : r 0#5 = a) (hv : VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨v0⟩)
    (hml : msg.length < 2 ^ 64) (hL0 : 0 < L) (hL16 : L < 16) (hbuf : buf0.length = 16)
    (hok : StateOk rh0)
    (hr6 : r 6#5 = BitVec.ofNat 64 L) (hr2 : r 2#5 = BitVec.ofNat 64 msg.length)
    (hr18 : r 18#5 = p) (hr4 : r 4#5 = BitVec.ofNat 64 msg.length) (u2 u3 : BitVec 64)
    (hm : m ⊨ Fields a rh0 pad (BitVec.ofNat 64 L) buf0 fin rest ∗
      bytesIn ro p msg ∗ Cells4 T x29 x30 u2 u3 ∗ R) :
    Reach (P pl X) (mkS sb (pl.base + 716#64) r T ps m v) Q := by
  set w := min (16 - L) msg.length with hw
  -- 716: mov x1, #16
  refine Reach.mkC hrun hCL (f_1c hP hCL) ?_
  rw [ex_movz64 1#5 (by decide), pc_add]
  intro hCL1
  -- 720: sub x1, x1, x6
  refine Reach.mkC hrun hCL1 (f_20 hP hCL1) ?_
  rw [ex_sub_shift0'' 1#5 1#5 6#5 (by decide) (by decide) (by decide) (BitVec.ofNat 64 (16 - L))
    (by simp only [upd_same]; rw [upd_ne _ _ (by decide), hr6]
        exact ofNat_sub_ofNat 16 L (by norm_num) (by omega)), pc_add]
  intro hCL2
  -- 724: cmp x1, x2
  refine Reach.mkC hrun hCL2 (f_24 hP hCL2) ?_
  rw [ex_cmp_reg 1#5 2#5 (by decide) (by decide), upd_same, upd_ne _ _ (by decide),
    upd_ne _ _ (by decide), hr2, pc_add]
  intro hCL3
  -- 728: csel x1, x1, x2, ls
  refine Reach.mkC hrun hCL3 (f_28 hP hCL3) ?_
  rw [ex_csel' .LS 1#5 1#5 2#5 (by decide) (by decide) (by decide) (BitVec.ofNat 64 w) ?hz, pc_add]
  case hz =>
    rw [ls_cmp, upd_same, upd_ne _ _ (by decide), upd_ne _ _ (by decide), hr2,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 16 - L < 2 ^ 64),
      Nat.mod_eq_of_lt hml]
    by_cases h : 16 - L ≤ msg.length
    · simp only [h, decide_true, if_true, hw, Nat.min_eq_left h]
    · simp only [h, decide_false, Bool.false_eq_true, if_false, hw,
        Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))]
  intro hCL4
  simp only [mkS_mem] at hCL1 hCL2 hCL3 hCL4
  generalize hr4' : upd (upd r 1#5 (BitVec.zeroExtend 64 0x0010#16)) 1#5 (BitVec.ofNat 64 (16 - L))
    = r4' at *
  have hk4 : Kept (upd r4' 1#5 (BitVec.ofNat 64 w)) r0 := by
    rw [← hr4']; exact ((hkept.upd 1#5 (by decide) _).upd 1#5 (by decide) _).upd 1#5 (by decide) _
  have g0 : upd r4' 1#5 (BitVec.ofNat 64 w) 0#5 = a := by rw [← hr4']; simp [upd_apply, hr0]
  have g1 : upd r4' 1#5 (BitVec.ofNat 64 w) 1#5 = BitVec.ofNat 64 w := by simp
  have g4 : upd r4' 1#5 (BitVec.ofNat 64 w) 4#5 = BitVec.ofNat 64 msg.length := by
    rw [← hr4']; simp [upd_apply, hr4]
  have g6 : upd r4' 1#5 (BitVec.ofNat 64 w) 6#5 = BitVec.ofNat 64 L := by
    rw [← hr4']; simp [upd_apply, hr6]
  have g18 : upd r4' 1#5 (BitVec.ofNat 64 w) 18#5 = p := by rw [← hr4']; simp [upd_apply, hr18]
  have g0' : r4' 0#5 = a := by rw [← hr4']; simp [upd_apply, hr0]
  have g6' : r4' 6#5 = BitVec.ofNat 64 L := by rw [← hr4']; simp [upd_apply, hr6]
  have g18' : r4' 18#5 = p := by rw [← hr4']; simp [upd_apply, hr18]
  -- 732: cbz x1, 768
  refine Reach.mkC hrun hCL4 (f_2c hP hCL4) ?_
  rw [ex_cbz 1#5 (by decide), g1]
  by_cases hw0 : w = 0
  · have e0 : BitVec.ofNat 64 w = 0#64 := by rw [hw0]
    rw [if_pos e0]
    intro hCL5
    simp only [mkS_mem] at hCL5
    rw [show pl.base + BitVec.ofNat 64 (716 + 4 + 4 + 4 + 4) + 0x0000000000000024#64 =
      pl.base + 768#64 by bv_omega]
    refine seg_768 hP hB K784 K892 hTal hrun hCL5 hk4 g0 hv hml hL0 hL16 hbuf hok w rfl g1 g6 g18
      g4 u2 u3 ?_
    rw [hw0, List.take_zero, copyInto_nil _ _ (by omega)]
    exact hm
  · have e0 : BitVec.ofNat 64 w ≠ 0#64 := fun e => hw0 ((ofNat_eq_zero _ (by omega)).mp e)
    simp only [e0, if_false, pc_add]
    intro hCL5
    simp only [mkS_mem] at hCL5
    -- 736: add x5, x6, #0x48
    refine Reach.mkC hrun hCL5 (f_30 hP hCL5) ?_
    rw [ex_add_imm 5#5 6#5 (by decide) (by decide), g6, pc_add]
    intro hCL6
    -- 740: mov x3, #0
    refine Reach.mkC hrun hCL6 (f_34 hP hCL6) ?_
    rw [ex_movz64 3#5 (by decide), pc_add]
    intro hCL7
    -- 744: add x5, x0, x5
    refine Reach.mkC hrun hCL7 (f_38 hP hCL7) ?_
    rw [ex_add_shift0 5#5 0#5 5#5 (by decide) (by decide) (by decide), pc_add]
    intro hCL8
    simp only [mkS_mem] at hCL6 hCL7 hCL8
    -- 748: the loop
    generalize hW : ((a + 64#64) ↦₆₄ BitVec.ofNat 64 L) ∗ (a ↦ₛ rh0) ∗ ((a + 88#64) ↦ₛ [fin]) ∗
      ((a + 48#64) ↦ₛ pad) ∗ ((a + 89#64) ↦ₛ rest) ∗ Cells4 T x29 x30 u2 u3 ∗ R = W
    have hm2 : m ⊨ bytesIn ro p msg ∗ ((a + 72#64) ↦ₛ buf0) ∗ W :=
      Satisfies.of_eq hm (by rw [← hW]; simp only [Fields]; ac_rfl)
    refine copyLoop (P pl X) (pl.base + BitVec.ofNat 64 (716 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4))
      18#5 2#5 5#5 1#5 3#5 Q sb T v ro p (a + 72#64) msg W 0 L w
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hrun
      (fun m' h => f_3c hP h) (fun m' h => by rw [pc_add]; exact f_40 hP h)
      (fun m' h => by rw [pc_add]; exact f_44 hP h)
      (fun m' h => by rw [pc_add]; exact f_48 hP h) (fun m' h => by rw [pc_add]; exact f_4c hP h)
      (by omega) (by omega)
      w (by omega) 0 _ _ _ buf0 (by omega) (by omega) hCL8 ?_ ?_ ?_ ?_ hm2 ?_
    · simp [upd_apply, g18']
    · simp only [upd_apply]; simp [g0', g6']
      rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 L)]
    · simp [upd_apply]
    · simp [upd_apply]
    intro r' ps' m' hCL9 hother hr3 hm3
    rw [pc_add]
    have hk' : Kept r' r0 := by
      intro k h1 h2
      have e2 : k ≠ 2#5 := by rintro rfl; revert h1; decide
      have e3 : k ≠ 3#5 := by rintro rfl; revert h1; decide
      have e5 : k ≠ 5#5 := by rintro rfl; revert h1; decide
      rw [hother k e2 e3]
      simp only [upd_apply, e5, e3, if_false]
      exact hk4 k h1 h2
    have q : ∀ k : BitVec 5, k ≠ 2#5 → k ≠ 3#5 → k ≠ 5#5 →
        r' k = upd r4' 1#5 (BitVec.ofNat 64 w) k := by
      intro k a2 a3 a5
      rw [hother k a2 a3]; simp [upd_apply, a3, a5]
    refine seg_768 hP hB K784 K892 hTal hrun hCL9 hk' (by rw [q 0#5 (by decide) (by decide)
        (by decide), g0]) hv hml hL0 hL16 hbuf hok w rfl
      (by rw [q 1#5 (by decide) (by decide) (by decide), g1])
      (by rw [q 6#5 (by decide) (by decide) (by decide), g6])
      (by rw [q 18#5 (by decide) (by decide) (by decide), g18])
      (by rw [q 4#5 (by decide) (by decide) (by decide), g4]) u2 u3 ?_
    rw [← hW] at hm3
    simp only [Fields, Nat.add_zero, List.drop_zero]
    exact Satisfies.of_eq hm3

end Poly1305Debian.UD

end
end

section
section
/-! # `poly1305_update` meets `updateIntSpec`, given `blocksSpec` for multiples of 16 -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.UD

open Arm64 Arm64.Obj Poly1305Boringssl
open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk)

theorem split96 (st : List (BitVec 8)) (h : st.length = 96) :
    st = st.take 48 ++ (st.drop 48).take 16 ++ (st.drop 64).take 8 ++ (st.drop 72).take 16 ++
      st.getD 88 0#8 :: st.drop 89 := by
  have d1 : (st.drop 48).take 16 ++ st.drop 64 = st.drop 48 := by
    have := List.take_append_drop 16 (st.drop 48)
    rw [List.drop_drop] at this; simpa using this
  have d2 : (st.drop 64).take 8 ++ st.drop 72 = st.drop 64 := by
    have := List.take_append_drop 8 (st.drop 64)
    rw [List.drop_drop] at this; simpa using this
  have d3 : (st.drop 72).take 16 ++ st.drop 88 = st.drop 72 := by
    have := List.take_append_drop 16 (st.drop 72)
    rw [List.drop_drop] at this; simpa using this
  have h88 : 88 < st.length := by omega
  have d4 : st.getD 88 0#8 :: st.drop 89 = st.drop 88 := by
    rw [List.drop_eq_getElem_cons h88]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h88]
  symm
  simp only [List.append_assoc]
  rw [d4, d3, d2, d1, List.take_append_drop]

set_option maxHeartbeats 8000000 in
theorem update_core
    (hBall : ∀ pl : Placement, libsodiumDebianOnetimeauthLib.Placeable pl → GuardUniform pl →
      ∀ X : String → Option (State → State), MemzeroOk X → MemsetOk X →
        Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthLib pl X → BlocksOk16 pl X) :
    internalOk "poly1305_update [libsodium_la_poly1305_donna]" (fun _ => updateIntSpec) := by
  refine ⟨by decide, fun pl hP hG X hMz hMs hLk => ?_⟩
  have hB := hBall pl hP hG X hMz hMs hLk
  intro x R s0 hpc hrun hpre hal hCL
  obtain ⟨ro, st, msg⟩ := x
  have hfa : libsodiumDebianOnetimeauthLib.fnAddr pl "poly1305_update [libsodium_la_poly1305_donna]" =
      pl.base + BitVec.ofNat 64 688 := rfl
  rw [hfa] at hpc
  show Reach (P pl X) s0 (fun sf => SubroutineOutcome updateIntSpec (ro, st, msg) R s0 sf)
  simp only [updateIntSpec] at hpre
  rw [sepConj_assoc, sat_pure_sep] at hpre
  obtain ⟨⟨hlen, hok, hL16, hn⟩, hpre⟩ := hpre
  set a := s0.readReg64 Reg.x0 with ha
  set p := s0.readReg64 Reg.x1 with hp
  have hal0 : s0.sp &&& 0b1111#64 = 0#64 := by simpa [State.spAligned] using hal
  set T := s0.sp - 32#64 with hT
  have hTal : T &&& 0b1111#64 = 0#64 := al16_sub _ 32 (by norm_num) (by norm_num) hal0
  have har : s0.regs.regs 0#5 = a := by rw [ha]; simp [readGpr_unfold, Reg.x0]
  have hpr : s0.regs.regs 1#5 = p := by rw [hp]; simp [readGpr_unfold, Reg.x1]
  have hml : msg.length < 2 ^ 64 := by rw [← hn]; exact BitVec.isLt _
  have hnr : s0.regs.regs 2#5 = BitVec.ofNat 64 msg.length := by
    rw [← hn]; simp [readGpr_unfold, Reg.x2]
  -- the state as fields
  have hsplit := split96 st hlen
  have l1 : (st.take 48).length = 48 := by simp; omega
  have l2 : ((st.drop 48).take 16).length = 16 := by simp; omega
  have l3 : ((st.drop 64).take 8).length = 8 := by simp; omega
  have l4 : ((st.drop 72).take 16).length = 16 := by simp; omega
  have l5 : (st.drop 89).length = 7 := by simp; omega
  generalize st.take 48 = rh0 at hsplit hok l1
  generalize (st.drop 48).take 16 = pad at hsplit l2
  generalize (st.drop 64).take 8 = w0 at hsplit l3
  generalize (st.drop 72).take 16 = buf0 at hsplit l4
  generalize st.getD 88 0#8 = fin at hsplit
  generalize st.drop 89 = rest at hsplit l5
  subst hsplit
  have L0 := layout (fin := fin) (rest := rest) l1 l2 l3 l4
  have hLw : u64At (rh0 ++ pad ++ w0 ++ buf0 ++ fin :: rest) 64 = leBytesToNum w0 := by
    unfold u64At; rw [L0.2.2.1]
  rw [hLw] at hL16
  have hpk : (pack64 w0).toNat = leBytesToNum w0 := pack64_toNat w0 l3
  -- the exits
  have K784 := exit_ok (pl := pl) (X := X) s0 ro rh0 pad w0 buf0 rest msg fin R l1 l2 l3 l4 l5
    hL16 hal0 (pl.base + 784#64) (fun m' h => f_60 hP h)
    (fun m' h => by rw [pc_add]; exact f_64 hP h)
    (fun m' h => by rw [pc_add, pc_add]; exact f_68 hP h)
  have K892 := exit_ok (pl := pl) (X := X) s0 ro rh0 pad w0 buf0 rest msg fin R l1 l2 l3 l4 l5
    hL16 hal0 (pl.base + 892#64) (fun m' h => f_cc hP h)
    (fun m' h => by rw [pc_add]; exact f_d0 hP h)
    (fun m' h => by rw [pc_add, pc_add]; exact f_d4 hP h)
  -- the memory
  have hfe : (a ↦ₛ (rh0 ++ pad ++ w0 ++ buf0 ++ fin :: rest)) =
      Fields a rh0 pad (pack64 w0) buf0 fin rest := by
    rw [← fields_eq a rh0 pad buf0 rest (pack64 w0) fin l1 l2 l4, unpack64_pack64 w0 l3]
  rw [hfe] at hpre
  have hsf : stackFrame s0 32 = memRegion T 32 := rfl
  rw [hsf] at hpre
  have h1 := Satisfies.of_eq hpre (Q := memRegion T 32 ∗
    (Fields a rh0 pad (pack64 w0) buf0 fin rest ∗ bytesIn ro p msg ∗ R))
  obtain ⟨u0, u1, u2, u3, h2⟩ := cells4_of_region h1
  clear h1 hpre
  simp only [Cells4, sepConj_assoc] at h2
  generalize hG : Fields a rh0 pad (pack64 w0) buf0 fin rest ∗ bytesIn ro p msg ∗ R = G at h2
  -- the run
  refine reach_congr (s' := mkS s0 (pl.base + BitVec.ofNat 64 688) s0.regs.regs s0.sp s0.pstate
    s0.mem s0.vregs.regs) (by rw [← hpc]; rfl) ?_
  -- 688: paciasp
  refine Reach.mkC hrun hCL (f_0 hP hCL) ?_
  rw [ex_hint, pc_add]
  intro hCL1
  -- 692: stp x29, x30, [sp, #-32]!
  have eT' : s0.sp + 0xffffffffffffffe0#64 = T := by rw [hT]; bv_omega
  have c0 := sat64_read h2
  have h2' := Satisfies.of_eq h2 (Q := ((T + 8#64) ↦₆₄ u1) ∗ (T ↦₆₄ u0) ∗
    ((T + 0x10#64) ↦₆₄ u2) ∗ ((T + 0x10#64 + 8#64) ↦₆₄ u3) ∗ G)
  have c1 := sat64_read h2'
  refine Reach.mkC hrun hCL1 (f_4 hP hCL1) ?_
  rw [ex_stp64_pre_sp _ _ (by decide) (by decide) _ hal0 (by rw [eT']; exact c0.2.2)
    (by rw [eT']; exact c1.2.2), eT', pc_add]
  intro hCL2
  have w1 := sat64_write (Satisfies.of_eq (sat64_write h2 (s0.regs.regs 29#5))
    (Q := ((T + 8#64) ↦₆₄ u1) ∗ (T ↦₆₄ s0.regs.regs 29#5) ∗
    ((T + 0x10#64) ↦₆₄ u2) ∗ ((T + 0x10#64 + 8#64) ↦₆₄ u3) ∗ G)) (s0.regs.regs 30#5)
  generalize hm1 : (s0.mem.write64 T (s0.regs.regs 29#5)).write64 (T + 8#64) (s0.regs.regs 30#5)
    = m1 at w1 hCL2 ⊢
  -- 696: mov x18, x1
  refine Reach.mkC hrun hCL2 (f_8 hP hCL2) ?_
  rw [ex_mov' 18#5 1#5 (by decide) (by decide) p hpr, pc_add]
  intro hCL3
  -- 700: mov x4, x2
  refine Reach.mkC hrun hCL3 (f_c hP hCL3) ?_
  rw [ex_mov' 4#5 2#5 (by decide) (by decide) (BitVec.ofNat 64 msg.length)
    (by rw [upd_ne _ _ (by decide), hnr]), pc_add]
  intro hCL4
  -- 704: mov x29, sp
  refine Reach.mkC hrun hCL4 (f_10 hP hCL4) ?_
  rw [ex_add_gpr_sp 29#5 (by decide), pc_add]
  intro hCL5
  -- 708: ldr x6, [x0, #0x40]
  rw [← hG] at w1
  have hw1 : m1 ⊨ ((a + 64#64) ↦₆₄ pack64 w0) ∗ (((a + 72#64) ↦ₛ buf0) ∗ (a ↦ₛ rh0) ∗
      ((a + 88#64) ↦ₛ [fin]) ∗ ((a + 48#64) ↦ₛ pad) ∗ ((a + 89#64) ↦ₛ rest) ∗ bytesIn ro p msg ∗
      Cells4 T (s0.regs.regs 29#5) (s0.regs.regs 30#5) u2 u3 ∗ R) :=
    Satisfies.of_eq w1 (by simp only [Fields, Cells4]; ac_rfl)
  have c2 := sat64_read hw1
  have hr0' : (upd (upd (upd s0.regs.regs 18#5 p) 4#5 (BitVec.ofNat 64 msg.length)) 29#5
      (T + BitVec.zeroExtend 64 0x000#12)) 0#5 = a := by simp [upd_apply, har]
  refine Reach.mkC hrun hCL5 (f_14 hP hCL5) ?_
  rw [ex_ldr64_gpr 6#5 0#5 (by decide) (by decide) _ (by rw [hr0']; exact c2.2.1), hr0', c2.1,
    pc_add]
  intro hCL6
  simp only [mkS_mem] at hCL1 hCL2 hCL3 hCL4 hCL5 hCL6
  generalize hr6 : upd (upd (upd (upd s0.regs.regs 18#5 p) 4#5 (BitVec.ofNat 64 msg.length)) 29#5
      (T + BitVec.zeroExtend 64 0x000#12)) 6#5 (pack64 w0) = r6
  have hk6 : Kept r6 s0.regs.regs := by
    rw [← hr6]
    have k0 : Kept s0.regs.regs s0.regs.regs := fun _ _ _ => rfl
    exact (((k0.upd 18#5 (by decide) _).upd 4#5 (by decide) _).upd 29#5 (by decide) _).upd 6#5
      (by decide) _
  have q0 : r6 0#5 = a := by rw [← hr6]; simp [upd_apply, har]
  have q2 : r6 2#5 = BitVec.ofNat 64 msg.length := by rw [← hr6]; simp [upd_apply, hnr]
  have q4 : r6 4#5 = BitVec.ofNat 64 msg.length := by rw [← hr6]; simp [upd_apply]
  have q6 : r6 6#5 = pack64 w0 := by rw [← hr6]; simp [upd_apply]
  have q18 : r6 18#5 = p := by rw [← hr6]; simp [upd_apply]
  have hm6 : m1 ⊨ Fields a rh0 pad (pack64 w0) buf0 fin rest ∗ bytesIn ro p msg ∗
      Cells4 T (s0.regs.regs 29#5) (s0.regs.regs 30#5) u2 u3 ∗ R :=
    Satisfies.of_eq hw1 (by simp only [Fields]; ac_rfl)
  -- 712: cbz x6, 828
  refine Reach.mkC hrun hCL6 (f_18 hP hCL6) ?_
  rw [ex_cbz 6#5 (by decide), q6]
  by_cases hL0 : leBytesToNum w0 = 0
  · have e0 : pack64 w0 = 0#64 := BitVec.eq_of_toNat_eq (by rw [hpk, hL0]; rfl)
    rw [if_pos e0]
    intro hCL7
    simp only [mkS_mem] at hCL7
    rw [show pl.base + BitVec.ofNat 64 (688 + 4 + 4 + 4 + 4 + 4 + 4) + 0x0000000000000074#64 =
      pl.base + 828#64 by bv_omega]
    rw [e0] at hm6
    refine seg_tail hP hB K784 K892 hTal hrun hCL7 hk6 q0 rfl 0 msg.length 0 (by omega) hml
      (by simp [hL0]) (by simp [hL0]) rfl (by rw [q18]; exact (BitVec.add_zero p).symm) q4 rh0 buf0 l4 u2 u3
      (inv_zero rh0 fin _ hok) hm6
  · have e0 : pack64 w0 ≠ 0#64 := fun e => hL0 (by rw [← hpk, e]; rfl)
    rw [if_neg e0, pc_add]
    intro hCL7
    simp only [mkS_mem] at hCL7
    have e6 : pack64 w0 = BitVec.ofNat 64 (leBytesToNum w0) :=
      BitVec.eq_of_toNat_eq (by rw [hpk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    rw [e6] at hm6 q6
    exact seg_lo hP hB K784 K892 hTal hrun hCL7 hk6 q0 rfl hml (by omega) hL16 l4 hok q6 q2 q18 q4
      u2 u3 hm6

end Poly1305Debian.UD

end
end

section
section
/-! # `poly1305_update` from the whole-block contract of `poly1305_blocks` -/

set_option autoImplicit false

namespace Poly1305Debian.UD

open Arm64 Arm64.Obj

theorem internalOk_poly1305_update_of_blocks_whole_dev :
    internalOk "poly1305_blocks [libsodium_la_poly1305_donna]"
        (fun _ => { blocksSpec with
          pre := fun g s0 =>
            match g with
            | (_, _, _, m) => ⌜m.length % 16 = 0⌝ ∗ blocksSpec.pre g s0 }) →
      internalOk "poly1305_update [libsodium_la_poly1305_donna]" (fun _ => updateIntSpec) := by
  intro h
  refine update_core (fun pl hP hG X hMz hMs hLk => ?_)
  intro ro rh fin msg hmod R s0 hpc hrun hpre hal
  exact h.2 pl hP hG X hMz hMs hLk (ro, rh, fin, msg) R s0 (by rw [hpc]; rfl) hrun
    (by rw [sepConj_assoc]; exact sat_pure_sep.mpr ⟨hmod, hpre⟩) hal

end Poly1305Debian.UD

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
      internalOk "poly1305_update [libsodium_la_poly1305_donna]" (fun _ => updateIntSpec) := by
  apply Poly1305Debian.UD.internalOk_poly1305_update_of_blocks_whole_dev <;> assumption

end
