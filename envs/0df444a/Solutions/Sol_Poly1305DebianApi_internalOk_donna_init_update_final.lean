-- Prove2me | solution 1 for Poly1305DebianApi.internalOk_donna_init_update_final
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-26T12:11:30.741687+00:00
-- url     : https://prove2.me/submissions/00fc5116-7a24-43cb-91f7-a9f5480d5f5b

import Definitions.Def_Poly1305DebianApi_Spec
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_X25519Dalek_steps_keepsFrozen_v2
import Theorems.Thm_Poly1305DebianApi_internalOk_poly1305_update
import Theorems.Thm_Poly1305DebianApi_internalOk_poly1305_finish
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
/-! # Instruction fetch for the placed `libsodiumPoly1305` text block -/

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- The placed program the goal talks about, with extern hooks `X`. -/
def prog (pl : Placement) (X : String → Option (State → State)) : Program :=
  Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.program pl X

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
theorem code_length : Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedCode.length = 2324 := by rfl

theorem patched_length (pl : Placement) : (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patched pl).length = 2324 := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE]
  show (List.map (fun _ => 4) (List.range (Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedCode.length / 4))).sum = 2324
  rw [code_length]; rfl

theorem stub_far {pl : Placement} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl) (e : String)
    (he : e ∈ Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text.externs) : 2324 ≤ (pl.ρ e - pl.base).toNat := by
  have := (hP.text.externs_ok e he).2
  rwa [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text.code.length = 2324 from code_length] at this

/-- No hook has its entry point inside the text block. -/
theorem hook_none {pl : Placement} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)
    (ex : String → Option (State → State)) {off : Nat} (hoff : off < 2324) :
    (prog pl ex).externAt? (pl.base + BitVec.ofNat 64 off) = none := by
  have e : (pl.base + BitVec.ofNat 64 off - pl.base).toNat = off := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  simp only [Program.externAt?, Program.hookAtOff?, prog, PlacedLib.program, e]
  have h1 : (Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text.externs.map fun e => (e, (pl.ρ e - pl.base).toNat)).findSome?
      (fun (n, o) => if o == off then ex n else none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro x hx
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
    have := stub_far hP e' he'
    have hne : ((pl.ρ e' - pl.base).toNat == off) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp only [hne, Bool.false_eq_true, ite_false]
  have h2 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text.symbols.findSome?
      (fun (n, o) => if o == off then (fun _ => (none : Option (State → State))) n else none) = none := by
    rw [List.findSome?_eq_none_iff]; intro x _; simp
  rw [h1]; simpa using h2

/-- Byte `k < 4` of the word at aligned offset `off` of the placed code. -/
theorem read8_code {pl : Placement} {m : Memory} {X : String → Option (State → State)} (hCL : (prog pl X).CodeLoaded m) {off k : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324) (hk : k < 4) :
    m.read8 (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off).extractLsb' (8 * k) 8 ∧
    m.perm (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (prog pl X).code.length = 2324 := patched_length pl
  have h := codeLoaded_cell hCL (off + k) (by omega)
  have ha : pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
      (prog pl X).base + BitVec.ofNat 64 (off + k) := by
    show _ = pl.base + _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  refine ⟨?_, h.2⟩
  rw [h.1]
  have ht := take4_drop_patched (blk := Poly1305DebianCt.libsodiumDebianOnetimeauthCtText) (pl := pl) hal
    (by rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.code = Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedCode from rfl, code_length]; exact hlen)
  have e1 : (prog pl X).code[off + k]'(by omega) =
      (((Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patched pl).drop off).take 4)[k]'(by
        simp [List.length_take, List.length_drop, patched_length]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + i < 32 := by omega
  simp [hi, this]; omega

theorem fetch_word {pl : Placement} {m : Memory} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {X : String → Option (State → State)} (hCL : (prog pl X).CodeLoaded m) {off : Nat} (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324) :
    (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off) := by
  have hb4 : pl.base.toNat % 4 = 0 := by
    have := hP.text.base_aligned
    simp [Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib, Poly1305DebianCt.libsodiumDebianOnetimeauthCtText] at this; omega
  have hnw : pl.base.toNat + 2324 ≤ 2 ^ 64 := by
    have := hP.text.no_wrap
    have hl : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.code.length = 2324 := code_length
    rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text = Poly1305DebianCt.libsodiumDebianOnetimeauthCtText from rfl, hl] at this
    exact this
  have hpc : (pl.base + BitVec.ofNat 64 off).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
    have h2 : (pl.base.toNat + off) % 2 ^ 64 = pl.base.toNat + off := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]; omega
  have hlen' : off < 2324 := by omega
  have r0 := read8_code hCL hal hlen (k := 0) (by omega)
  have r1 := read8_code hCL hal hlen (k := 1) (by omega)
  have r2 := read8_code hCL hal hlen (k := 2) (by omega)
  have r3 := read8_code hCL hal hlen (k := 3) (by omega)
  simp only [Program.fetchMem, hook_none hP X hlen', Option.isSome_none, Bool.false_eq_true, if_false, hpc,
    ne_eq, not_true_eq_false]
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
    (h : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocAt? off = none) :
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off = Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.wordAt off := by
  simp [CodeBlock.patchedWord, h]

theorem Steps.trans' {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Steps p b c) :
    Steps p a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

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


end Poly1305DebianApi.Donna

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

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

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

end Poly1305DebianApi.Donna

end
end

section
section
/-! # Code stays loaded; stepping on abstract states; small stack frames -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

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



/-- Fetch at a plain (unrelocated) offset from any memory that kept the frozen bytes of `m0`. -/
theorem fetch_at {pl : Placement} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {X : String → Option (State → State)} {m0 m : Memory} (hCL : (prog pl X).CodeLoaded m0)
    (hk : m0.KeepsFrozen m) {off : Nat} {inst : Instr}
    (h : (off % 4 = 0 ∧ off + 4 ≤ 2324) ∧ Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocAt? off = none ∧
      decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.wordAt off) = some inst) :
    (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 off) = some inst := by
  rw [fetch_word hP (codeLoaded_keepsFrozen hCL hk) h.1.1 h.1.2, patchedWord_plain _ h.2.1]
  exact h.2.2

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

end Poly1305DebianApi.Donna

end
end

section
section
/-! # Decoding a relocated cross-block `BL`

Adapted from the sibling batch q445-xd-edwards (`Solutions/X25519DalekEdwards/Reloc.lean`), which
follows the zlib CRC-32 mission's proofs (`ZlibCrc32.Small.RelocBase`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

open Arm64 Arm64.Obj

end Poly1305DebianApi.Donna

end
end

section
section
/-! # 128-bit loads and stores, 32-byte buffers as 64-bit cells, stack regions -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

open Arm64 Arm64.Obj

/-! ## 32-byte buffers -/

theorem bytes8_cell (a : BitVec 64) (l : List (BitVec 8)) (h : l.length = 8) :
    (a ↦ₛ l) = (a ↦₆₄ pack64 l) := by
  rw [pointsTo64_eq_bytes, unpack64_pack64 _ h]

/-! ## Stack regions -/

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

/-! ## Runs of 64-bit cells -/

/-- Owned 64-bit cells holding `l` at `a`, `a + 8`, … -/
def cellsFrom : BitVec 64 → List (BitVec 64) → SepProp
  | _, [] => emp
  | a, v :: l => (a ↦₆₄ v) ∗ cellsFrom (a + 8#64) l

theorem cellsFrom_cons (a v : BitVec 64) (l : List (BitVec 64)) :
    cellsFrom a (v :: l) = (a ↦₆₄ v) ∗ cellsFrom (a + 8#64) l := rfl

theorem addr_succ (a : BitVec 64) (k : Nat) :
    a + 8#64 + BitVec.ofNat 64 (8 * k) = a + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem cells_read : ∀ (l : List (BitVec 64)) (a : BitVec 64) (F : SepProp) (m : Memory),
    (m ⊨ cellsFrom a l ∗ F) → ∀ k (hk : k < l.length),
      m.read64 (a + BitVec.ofNat 64 (8 * k)) = l[k] ∧
      m.canRead (a + BitVec.ofNat 64 (8 * k)) 8 = true ∧
      m.canWrite (a + BitVec.ofNat 64 (8 * k)) 8 = true
  | [], _, _, _, _, k, hk => by simp at hk
  | v :: l, a, F, m, hs, 0, _ => by
    rw [cellsFrom_cons, sepConj_assoc] at hs
    simpa using sat64_read hs
  | v :: l, a, F, m, hs, k + 1, hk => by
    rw [cellsFrom_cons, sepConj_assoc, sepConj_left_comm] at hs
    have := cells_read l (a + 8#64) _ m hs k (by simpa using hk)
    rw [addr_succ] at this
    simpa using this

theorem cells_write : ∀ (l : List (BitVec 64)) (a : BitVec 64) (F : SepProp) (m : Memory),
    (m ⊨ cellsFrom a l ∗ F) → ∀ k, k < l.length → ∀ w : BitVec 64,
      (m.write64 (a + BitVec.ofNat 64 (8 * k)) w ⊨ cellsFrom a (l.set k w) ∗ F)
  | [], _, _, _, _, k, hk, _ => by simp at hk
  | v :: l, a, F, m, hs, 0, _, w => by
    rw [cellsFrom_cons, sepConj_assoc] at hs
    rw [List.set_cons_zero, cellsFrom_cons, sepConj_assoc]
    simpa using sat64_write hs w
  | v :: l, a, F, m, hs, k + 1, hk, w => by
    rw [cellsFrom_cons, sepConj_assoc, sepConj_left_comm] at hs
    have := cells_write l (a + 8#64) _ m hs k (by simpa using hk) w
    rw [List.set_cons_succ, cellsFrom_cons, sepConj_assoc, sepConj_left_comm]
    rw [addr_succ] at this
    exact this

/-! ## Frame permutations -/




end Poly1305DebianApi.Donna

end
end

section
section
/-! # One lemma per instruction shape on abstract states `mkS`

The instructions of the two entry blocks (17 and 18). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

open Arm64 Arm64.Obj

theorem awc_false_fst (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]
  omega

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_add_gpr_sp (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD (.gpr d) .sp imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (sp + imm.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_false_fst, hd]

theorem ex_bl (off : BitVec 64) :
    execInstWithSvc svc (.bl off) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + off) (upd r 30#5 (pc + 4#64)) sp ps m v := by
  simp [execInstWithSvc]

theorem ex_ret :
    execInstWithSvc svc (.ret (.gpr 30#5)) (mkS s0 pc r sp ps m v) = mkS s0 (r 30#5) r sp ps m v := by
  simp [execInstWithSvc]

end exec

end Poly1305DebianApi.Donna

end
end

section
section
/-! # Small facts shared by the two entry-block proofs -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

open Arm64 Arm64.Obj

/-! ## Small facts -/

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

theorem z12 (k : Nat) (hk : k < 2 ^ 12) :
    (BitVec.ofNat 12 k).zeroExtend 64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq; simp; omega


end Poly1305DebianApi.Donna

end
end

section
section
/-! # More instruction shapes, and calling a function through its contract -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

open Arm64 Arm64.Obj

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_stp64_pre_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw1 : m.canWrite (sp + off) 8 = true)
    (hw2 : m.canWrite (sp + off + 8#64) 8 = true) :
    execInstWithSvc svc (.stp .W64 (.gpr a) (.gpr b) (.PreIndex .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r (sp + off) ps ((m.write64 (sp + off) (r a)).write64 (sp + off + 8#64) (r b)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hw1, hw2, ha, hb,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_ldp64_post_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr1 : m.canRead sp 8 = true)
    (hr2 : m.canRead (sp + 8#64) 8 = true) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.PostIndex .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a (m.read64 sp)) b (m.read64 (sp + 8#64))) (sp + off) ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hr1, hr2, ha, hb,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_movz32 (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 16) :
    execInstWithSvc svc (.moveWide .W32 .MOVZ (.gpr d) imm 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (imm.zeroExtend 64)) sp ps m v := by
  simp only [execInstWithSvc, execMoveWide, State.writeReg, mkS_writeGpr, hd, if_false,
    mkS_advancePC]
  congr 2
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem ex_hint (imm : BitVec 7) :
    execInstWithSvc svc (.hint imm) (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) r sp ps m v := by
  simp [execInstWithSvc]

end exec

theorem KeepsFrozen_refl (m : Memory) : m.KeepsFrozen m := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

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
    {tgt : BitVec 64} (hOk : subroutine_ok (prog pl X) tgt spec)
    (hpan : ∀ x s s', spec.onPanic x s s' = ⌜False⌝)
    (hexit : ∀ x c s s', spec.onExit x c s s' = ⌜False⌝)
    (hoom : ∀ x s s', spec.onOom x s s' = ⌜False⌝)
    {sb : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState}
    {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop} (x : α) (F : SepProp)
    (hrun : sb.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bl (tgt - pc)))
    (hal : sp &&& 0b1111#64 = 0#64)
    (hCL : (prog pl X).CodeLoaded m)
    (hpre : m ⊨ spec.pre x (mkS sb tgt (upd r 30#5 (pc + 4#64)) sp ps m v) ∗ F)
    (hcont : ∀ sf : State, sf.status = .Running → sf.pc = pc + 4#64 → sf.sp = sp →
      KeptRegs sf r → calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ → m.KeepsFrozen sf.mem →
      (sf.mem ⊨ spec.post x (mkS sb tgt (upd r 30#5 (pc + 4#64)) sp ps m v) sf ∗ F) →
      Reach (prog pl X) sf Q) :
    Reach (prog pl X) (mkS sb pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  rw [ex_bl]
  have epc : pc + (tgt - pc) = tgt := by bv_omega
  rw [epc]
  set s1 := mkS sb tgt (upd r 30#5 (pc + 4#64)) sp ps m v with hs1
  obtain ⟨sf, hsteps, hout⟩ := hOk x F s1 rfl hrun hpre (by simp [hs1, hal]) hCL
  refine Reach.steps hsteps ?_
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨_, hpanc⟩ | ⟨code, _, hex⟩ | ⟨_, hoomc⟩
  rotate_left
  · rw [hpan] at hpanc; exact (sat_false hpanc).elim
  · rw [hexit] at hex; exact (sat_false hex).elim
  · rw [hoom] at hoomc; exact (sat_false hoomc).elim
  have hpc' : sf.pc = pc + 4#64 := by rw [hpcf]; simp [hs1, upd_apply]
  have hsp' : sf.sp = sp := by rw [hspf]; rfl
  have kf : m.KeepsFrozen sf.mem := X25519Dalek.steps_keepsFrozen_v2 hsteps
  refine hcont sf hrunf hpc' hsp' ?_ ?_ kf hpost
  · intro k hk1 hk2
    have := kept_of_cs hcs k hk1 hk2
    rw [this, upd_apply, if_neg]
    intro e; subst e; simp at hk2
  · have := hcs.2.2.2.2.2.2.2.2.2.2.2
    rw [this]; rfl

/-! ## The two milestones as contracts at their addresses -/

/-- The hypotheses of `internalOk` on a placement and hook table. -/
structure Hyps (pl : Placement) (X : String → Option (State → State)) : Prop where
  hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl
  hG : GuardUniform pl
  hZ : MemzeroOk X
  hM : MemsetOk X
  hD : Link.PlacedLib.LinkOk Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib pl X

theorem update_ok {pl : Placement} {X : String → Option (State → State)} (h : Hyps pl X) :
    subroutine_ok (prog pl X) (pl.base + BitVec.ofNat 64 688) updateIntSpec :=
  internalOk_poly1305_update.2 pl h.hP h.hG X h.hZ h.hM h.hD

theorem finish_ok {pl : Placement} {X : String → Option (State → State)} (h : Hyps pl X) :
    subroutine_ok (prog pl X) (pl.base + BitVec.ofNat 64 1056) finishSpec :=
  internalOk_poly1305_finish.2 pl h.hP h.hG X h.hZ h.hM h.hD

end Poly1305DebianApi.Donna

end
end

section
section
/-! # More instruction shapes (general-register bases, bitfield, extract, logical immediate),
reads of owned-or-read-only byte lists, and byte lists as runs of 64-bit cells -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

open Arm64 Arm64.Obj Poly1305Boringssl

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_ldp64_gpr (a b n : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hn : n ≠ 31#5)
    (base off x1 x2 : BitVec 64) (hbase : r n = base) (hr1 : m.canRead (base + off) 8 = true)
    (hr2 : m.canRead (base + off + 8#64) 8 = true) (hv1 : m.read64 (base + off) = x1)
    (hv2 : m.read64 (base + off + 8#64) = x2) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.Offset (.gpr n) off))
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a x1) b x2) sp ps m v := by
  subst hbase hv1 hv2
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hr1, hr2, ha, hb, hn,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_ldr64_gpr (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (base off x : BitVec 64)
    (hbase : r n = base) (hr : m.canRead (base + off) 8 = true) (hv : m.read64 (base + off) = x) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.Offset (.gpr n) off))
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a x) sp ps m v := by
  subst hbase hv
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hr, ha, hn,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

/-- `stp` of two registers (general or `xzr`), given their values `x1`, `x2`. -/
theorem ex_stp64_gpr (rt1 rt2 : Reg) (n : BitVec 5) (hn : n ≠ 31#5) (base off x1 x2 : BitVec 64)
    (hbase : r n = base)
    (h1 : (mkS s0 pc r sp ps m v).readReg64 rt1 = x1)
    (h2 : (mkS s0 pc r sp ps m v).readReg64 rt2 = x2)
    (hw1 : m.canWrite (base + off) 8 = true) (hw2 : m.canWrite (base + off + 8#64) 8 = true) :
    execInstWithSvc svc (.stp .W64 rt1 rt2 (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps ((m.write64 (base + off) x1).write64 (base + off + 8#64) x2) v := by
  subst hbase
  simp only [execInstWithSvc, execStp, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg,
    evalAddrMode, h1, h2, mkS_readGpr, hn, if_false, mkS_mem, hw1, hw2, Bool.and_self,
    Bool.not_true, MemWidth.bytes, Memory.writeSized, mkS_setMem, mkS_advancePC]
  rfl

theorem ex_strb_xzr (n : BitVec 5) (hn : n ≠ 31#5) (base off : BitVec 64) (hbase : r n = base)
    (hw : m.canWrite (base + off) 1 = true) :
    execInstWithSvc svc (.str .B8 .xzr (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write8 (base + off) 0#8) v := by
  subst hbase
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw, hn,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_str64_gpr' (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (base off x : BitVec 64)
    (hbase : r n = base) (hx : r a = x) (hw : m.canWrite (base + off) 8 = true) :
    execInstWithSvc svc (.str .X64 (.gpr a) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 (base + off) x) v := by
  subst hbase hx
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw, ha, hn,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_extr64 (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) (lsb : Nat)
    (x y : BitVec 64) (hx : r n = x) (hy : r k = y) :
    execInstWithSvc svc (.extr .W64 (.gpr d) (.gpr n) (.gpr k) lsb) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (((x ++ y) >>> (lsb % 64)).truncate 64)) sp ps m v := by
  subst hx hy
  simp [execInstWithSvc, State.writeReg, hd, hn, hk]

theorem ex_and_imm (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (mask x : BitVec 64)
    (hx : r n = x) :
    execInstWithSvc svc (.logicalImm .W64 .AND (.gpr d) (.gpr n) mask) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (x &&& mask)) sp ps m v := by
  subst hx
  simp [execInstWithSvc, evalLogical, State.readReg, State.writeReg, hd, hn]

end exec

/-! ## Reads of owned or read-only byte lists -/

theorem bytesIn_byte {m : Memory} {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ bytesIn ro p bs ∗ F) (j : Nat) (hj : j < bs.length) :
    m.read8 (p + BitVec.ofNat 64 j) = bs[j] ∧ (m.perm (p + BitVec.ofNat 64 j)).r = true ∧
      m.isLazyFree (p + BitVec.ofNat 64 j) = false := by
  cases ro
  · have := sat_bytes_read (by simpa [bytesIn] using hs) j hj
    refine ⟨this.1, ?_, this.2.2⟩
    rw [this.2.1]; rfl
  · exact sat_bytesRO_read (by simpa [bytesIn] using hs) j hj

theorem bytesIn_read64 {m : Memory} {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} (hs : m ⊨ bytesIn ro p bs ∗ F) (off : Nat) (hoff : off + 8 ≤ bs.length) :
    m.read64 (p + BitVec.ofNat 64 off) = pack64 ((bs.drop off).take 8) ∧
      m.canRead (p + BitVec.ofNat 64 off) 8 = true := by
  have hb : ∀ i, i < 8 → m.read8 (p + BitVec.ofNat 64 off + BitVec.ofNat 64 i) =
      ((bs.drop off).take 8).getD i 0 ∧
      (m.perm (p + BitVec.ofNat 64 off + BitVec.ofNat 64 i)).r = true ∧
      m.isLazyFree (p + BitVec.ofNat 64 off + BitVec.ofNat 64 i) = false := by
    intro i hi
    have e : p + BitVec.ofNat 64 off + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (off + i) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add]
    rw [e]
    have := bytesIn_byte hs (off + i) (by omega)
    refine ⟨?_, this.2⟩
    rw [this.1]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    rw [if_pos hi, List.getElem?_eq_getElem (by omega)]
    rfl
  refine ⟨?_, canRead_of (fun i hi => (hb i hi).2)⟩
  have h0 := (hb 0 (by omega)).1
  have h1 := (hb 1 (by omega)).1
  have h2 := (hb 2 (by omega)).1
  have h3 := (hb 3 (by omega)).1
  have h4 := (hb 4 (by omega)).1
  have h5 := (hb 5 (by omega)).1
  have h6 := (hb 6 (by omega)).1
  have h7 := (hb 7 (by omega)).1
  simp only [Memory.read64]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  rfl

/-! ## Byte lists as runs of 64-bit cells -/

/-- The first `k` little-endian 64-bit words of a byte list. -/
def chunks : Nat → List (BitVec 8) → List (BitVec 64)
  | 0, _ => []
  | k + 1, bs => pack64 (bs.take 8) :: chunks k (bs.drop 8)

theorem bytes_eq_cellsFrom : ∀ (k : Nat) (a : BitVec 64) (bs : List (BitVec 8)),
    bs.length = 8 * k → (a ↦ₛ bs) = cellsFrom a (chunks k bs)
  | 0, a, bs, h => by
    have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | k + 1, a, bs, h => by
    rw [pointsToBytes_split a bs 8 (by omega), bytes8_cell _ _ (by simp; omega),
      bytes_eq_cellsFrom k _ (bs.drop 8) (by simp; omega)]
    rfl

theorem cellsFrom_eq_bytes : ∀ (a : BitVec 64) (l : List (BitVec 64)),
    cellsFrom a l = (a ↦ₛ (l.map unpack64).flatten)
  | a, [] => rfl
  | a, x :: l => by
    rw [cellsFrom_cons, cellsFrom_eq_bytes (a + 8#64) l, List.map_cons, List.flatten_cons,
      pointsToBytes_append, pointsTo64_eq_bytes, unpack64_length]

/-! ## Little-endian numbers -/

theorem leBytesToNum_append_x (l1 l2 : List (BitVec 8)) :
    leBytesToNum (l1 ++ l2) = leBytesToNum l1 + 256 ^ l1.length * leBytesToNum l2 := by
  induction l1 with
  | nil => simp [leBytesToNum]
  | cons b l ih =>
    simp only [leBytesToNum, List.cons_append, List.foldr_cons, List.length_cons] at ih ⊢
    rw [ih, pow_succ, Nat.mul_add, Nat.add_assoc, ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ l.length)]

theorem leBytesToNum_unpack64_x (v : BitVec 64) : leBytesToNum (unpack64 v) = v.toNat := by
  simp only [leBytesToNum, unpack64, List.foldr_cons, List.foldr_nil, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  have := v.isLt
  omega

theorem leBytesToNum_eight (l : List (BitVec 8)) (h : l.length = 8) :
    leBytesToNum l = (pack64 l).toNat := by
  conv_lhs => rw [← unpack64_pack64 l h]
  exact leBytesToNum_unpack64_x _

/-! ## Writes into runs of cells and single bytes, at a given address -/

theorem cellW {l : List (BitVec 64)} {a : BitVec 64} {F : SepProp} {m : Memory}
    (hs : m ⊨ cellsFrom a l ∗ F) (k : Nat) (hk : k < l.length) (addr : BitVec 64)
    (h : addr = a + BitVec.ofNat 64 (8 * k)) (w : BitVec 64) :
    m.write64 addr w ⊨ cellsFrom a (l.set k w) ∗ F := by
  subst h; exact cells_write l a F m hs k hk w

theorem cellCW {l : List (BitVec 64)} {a : BitVec 64} {F : SepProp} {m : Memory}
    (hs : m ⊨ cellsFrom a l ∗ F) (k : Nat) (hk : k < l.length) (addr : BitVec 64)
    (h : addr = a + BitVec.ofNat 64 (8 * k)) : m.canWrite addr 8 = true := by
  subst h; exact (cells_read l a F m hs k hk).2.2

theorem byteW {m : Memory} {p : BitVec 64} {b : BitVec 8} {F : SepProp}
    (hs : m ⊨ (p ↦ₛ [b]) ∗ F) (w : BitVec 8) : m.write8 p w ⊨ (p ↦ₛ [w]) ∗ F := by
  have := sat_bytes_write hs 0 (by simp) w
  simpa using this

theorem byteCW {m : Memory} {p : BitVec 64} {b : BitVec 8} {F : SepProp}
    (hs : m ⊨ (p ↦ₛ [b]) ∗ F) : m.canWrite p 1 = true := by
  refine canWrite_of (fun i hi => ?_)
  have : i = 0 := by omega
  subst this
  have := (sat_bytes_read hs 0 (by simp)).2.1
  simpa using this

/-- The layout of the first 89 bytes of the state and the rest. -/
theorem bytes_layout (a : BitVec 64) (L buf : List (BitVec 8)) (x : BitVec 8)
    (rest : List (BitVec 8)) (hL : L.length = 72) (hb : buf.length = 16) :
    (a ↦ₛ (L ++ buf ++ x :: rest)) = (a ↦ₛ L) ∗ ((a + BitVec.ofNat 64 72) ↦ₛ buf) ∗
      ((a + BitVec.ofNat 64 88) ↦ₛ [x]) ∗ ((a + BitVec.ofNat 64 89) ↦ₛ rest) := by
  rw [List.append_assoc, show x :: rest = [x] ++ rest from rfl, pointsToBytes_append,
    pointsToBytes_append, pointsToBytes_append, hL, hb, List.length_singleton, pc_add, pc_add]

/-! ## Words of byte lists -/

theorem u64At_zero (v : BitVec 64) (l : List (BitVec 8)) : u64At (unpack64 v ++ l) 0 = v.toNat := by
  simp only [u64At, List.drop_zero]
  rw [List.take_left' (unpack64_length v), leBytesToNum_unpack64_x]

theorem u64At_single (v : BitVec 64) : u64At (unpack64 v) 0 = v.toNat := by
  simp only [u64At, List.drop_zero]
  rw [List.take_of_length_le (by simp), leBytesToNum_unpack64_x]

theorem u64At_ge8 (v : BitVec 64) (l : List (BitVec 8)) (off : Nat) (h : 8 ≤ off) :
    u64At (unpack64 v ++ l) off = u64At l (off - 8) := by
  obtain ⟨k, rfl⟩ : ∃ k, off = 8 + k := ⟨off - 8, by omega⟩
  simp only [u64At, Nat.add_sub_cancel_left]
  rw [← List.drop_drop, List.drop_left' (unpack64_length v)]

end Poly1305DebianApi.Donna

end
end

section
section
/-! # The instruction shapes GCC uses in `crypto_onetimeauth_poly1305_donna_init` beyond MemX -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Arm64 Arm64.Obj

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_str64_xzr (n : BitVec 5) (hn : n ≠ 31#5) (base off : BitVec 64)
    (hbase : r n = base) (hw : m.canWrite (base + off) 8 = true) :
    execInstWithSvc svc (.str .X64 .xzr (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 (base + off) 0#64) v := by
  subst hbase
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw, hn,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_orr_imm_xzr (d : BitVec 5) (hd : d ≠ 31#5) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm .W64 .ORR (.gpr d) .xzr mask) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d mask) sp ps m v := by
  simp [execInstWithSvc, evalLogical, State.readReg, State.writeReg, hd]

theorem ex_movk_fc0f (d : BitVec 5) (hd : d ≠ 31#5) (hx : r d = 0x0000000fffff0000#64) :
    execInstWithSvc svc (.moveWide .W64 .MOVK (.gpr d) 0xfc0f#16 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d 0x0000000ffffffc0f#64) sp ps m v := by
  simp [execInstWithSvc, execMoveWide, State.readReg, State.writeReg, hd, hx]

theorem ex_and_lsr (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (x y : BitVec 64) (hx : r n = x) (hy : r k = y) :
    execInstWithSvc svc (.logicalShift .W64 .AND (.gpr d) (.gpr n) (.gpr k) .LSR 24)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (x &&& y >>> 24)) sp ps m v := by
  subst hx hy
  simp [execInstWithSvc, execLogicalShift, evalLogical, State.readReg, State.writeReg, shiftVal,
    shift64, hd, hn, hk]

end exec

theorem mask_r2 (t1 : BitVec 64) :
    0x0000000ffffffc0f#64 &&& t1 >>> 24 = t1 >>> 24 &&& 0xfffffc0ffffffc0f#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp (config := { decide := true })

end Poly1305DebianApi.Donna

end
end

section
section
/-! # The representation predicate of the streaming state, and the arithmetic facts about it

`RepB st key m`: the 256 bytes `st` of a `crypto_onetimeauth_poly1305_state` hold, after absorbing
the message `m` with the key `key`, the clamped `r` of the key's first 16 bytes, `pad` = its last 16
bytes, `final = 0`, `leftover = |m| mod 16` with the last `|m| mod 16` bytes of `m` at the start of
`buffer`, and limbs `h` with `StateOk` whose value is, modulo `p`, the block loop (with the `2^128`
term) on the whole 16-byte blocks of `m`. -/

set_option autoImplicit false

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

open Poly1305Boringssl

/-- The whole 16-byte blocks of `m`. -/
def fullOf (m : List (BitVec 8)) : List (BitVec 8) := m.take (16 * (m.length / 16))

/-- The representation predicate on the state bytes. -/
def RepB (st key m : List (BitVec 8)) : Prop :=
  st.length = 256 ∧ key.length = 32 ∧ StateOk (st.take 48) ∧
  limbVal (rLimb st) = clamp (leBytesToNum (key.take 16)) ∧
  (st.drop 48).take 16 = (key.drop 16).take 16 ∧
  u64At st 64 = m.length % 16 ∧
  (st.drop 72).take (m.length % 16) = m.drop (16 * (m.length / 16)) ∧
  st.getD 88 0#8 = 0#8 ∧
  limbVal (hLimb st) % p1305 = blocksAcc (limbVal (rLimb st)) (2 ^ 128) 0 (fullOf m) % p1305

/-- The same, on the fields of the first 89 bytes: `rh` (r and h, 48 bytes), `pad` (16 bytes),
`leftover` (a 64-bit word), `buffer` (16 bytes) and `final` (one byte). -/
def RepP (rh pad : List (BitVec 8)) (lo : BitVec 64) (buf : List (BitVec 8)) (fin : BitVec 8)
    (key m : List (BitVec 8)) : Prop :=
  rh.length = 48 ∧ pad.length = 16 ∧ buf.length = 16 ∧ key.length = 32 ∧
  StateOk rh ∧ limbVal (rLimb rh) = clamp (leBytesToNum (key.take 16)) ∧
  pad = (key.drop 16).take 16 ∧ lo.toNat = m.length % 16 ∧
  buf.take (m.length % 16) = m.drop (16 * (m.length / 16)) ∧ fin = 0#8 ∧
  limbVal (hLimb rh) % p1305 = blocksAcc (limbVal (rLimb rh)) (2 ^ 128) 0 (fullOf m) % p1305

/-- The representation predicate (the address is not used). -/
def Rep : StateRep := fun _ st key m => RepB st key m

/-! ## Old-shape guard and one-shot contract (as in bundle `Poly1305Debian_Spec`), over the Ct library

The ported proof is written against these; `Bridge.lean` transfers it to `Poly1305DebianApi.guard`
and `Poly1305DebianApi.oneshotSpec`. -/

open Arm64 Arm64.Obj

def donnaInitOk (Rep : StateRep) : Prop :=
  internalOk "crypto_onetimeauth_poly1305_donna_init [libsodium_la_poly1305_donna]"
    (fun _ => initSpec Rep)

def donnaUpdateOk (Rep : StateRep) : Prop :=
  internalOk "crypto_onetimeauth_poly1305_donna_update [libsodium_la_poly1305_donna]"
    (fun _ => updateSpec Rep)

def donnaFinalOk (Rep : StateRep) : Prop :=
  internalOk "crypto_onetimeauth_poly1305_donna_final [libsodium_la_poly1305_donna]"
    (fun _ => finalSpec Rep)


end Poly1305DebianApi.Donna

end
end

section
section
/-! # `crypto_onetimeauth_poly1305_donna_init` (text offset 0x3ac = 940, 21 instructions)

`bti c; ldp x2, x3, [x1]; stp xzr, xzr, [x0, #0x18]; str xzr, [x0, #0x28];
and x4, x2, #0xfffffffffff; extr x2, x3, x2, #44; and x2, x2, #0xfffffffffff;
and x4, x4, #0xfffffffc0fffffff; and x2, x2, #0xffffffffffc0ffff; stp x4, x2, [x0];
mov x2, #0xfffff0000; movk x2, #0xfc0f; and x3, x2, x3, lsr #24; str x3, [x0, #0x10];
ldr x2, [x1, #0x10]; str x2, [x0, #0x30]; ldr x1, [x1, #0x18]; stp x1, xzr, [x0, #0x38];
strb wzr, [x0, #0x58]; mov w0, #0; ret`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

open Arm64 Arm64.Obj Poly1305Boringssl

section fetch
variable {pl : Placement} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)
  {X : String → Option (State → State)} {m0 : Memory} (hCL : (prog pl X).CodeLoaded m0)
  {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem fI_940 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 940) =
    some (.hint 0x22#7) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_944 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 944) =
    some (.ldp .W64 false (.gpr 2#5) (.gpr 3#5) (.Offset (.gpr 1#5) 0#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_948 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 948) =
    some (.stp .W64 .xzr .xzr (.Offset (.gpr 0#5) 0x18#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_952 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 952) =
    some (.str .X64 .xzr (.Offset (.gpr 0#5) 0x28#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_956 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 956) =
    some (.logicalImm .W64 .AND (.gpr 4#5) (.gpr 2#5) 0x00000fffffffffff#64) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_960 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 960) =
    some (.extr .W64 (.gpr 2#5) (.gpr 3#5) (.gpr 2#5) 44) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_964 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 964) =
    some (.logicalImm .W64 .AND (.gpr 2#5) (.gpr 2#5) 0x00000fffffffffff#64) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_968 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 968) =
    some (.logicalImm .W64 .AND (.gpr 4#5) (.gpr 4#5) 0xfffffffc0fffffff#64) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_972 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 972) =
    some (.logicalImm .W64 .AND (.gpr 2#5) (.gpr 2#5) 0xffffffffffc0ffff#64) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_976 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 976) =
    some (.stp .W64 (.gpr 4#5) (.gpr 2#5) (.Offset (.gpr 0#5) 0#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_980 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 980) =
    some (.logicalImm .W64 .ORR (.gpr 2#5) .xzr 0x0000000fffff0000#64) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_984 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 984) =
    some (.moveWide .W64 .MOVK (.gpr 2#5) 0xfc0f#16 0) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_988 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 988) =
    some (.logicalShift .W64 .AND (.gpr 3#5) (.gpr 2#5) (.gpr 3#5) .LSR 24) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_992 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 992) =
    some (.str .X64 (.gpr 3#5) (.Offset (.gpr 0#5) 0x10#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_996 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 996) =
    some (.ldr .W64 .X64 false (.gpr 2#5) (.Offset (.gpr 1#5) 0x10#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_1000 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1000) =
    some (.str .X64 (.gpr 2#5) (.Offset (.gpr 0#5) 0x30#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_1004 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1004) =
    some (.ldr .W64 .X64 false (.gpr 1#5) (.Offset (.gpr 1#5) 0x18#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_1008 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1008) =
    some (.stp .W64 (.gpr 1#5) .xzr (.Offset (.gpr 0#5) 0x38#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_1012 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1012) =
    some (.str .B8 .xzr (.Offset (.gpr 0#5) 0x58#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_1016 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1016) =
    some (.moveWide .W32 .MOVZ (.gpr 0#5) 0#16 0) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fI_1020 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1020) =
    some (.ret (.gpr 30#5)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩

end fetch

/-! ## The clamped limbs -/

theorem clamp_limbs (t0 t1 r0 r1 r2 : BitVec 64)
    (h0 : r0 = t0 &&& 0x00000fffffffffff#64 &&& 0xfffffffc0fffffff#64)
    (h1 : r1 = ((t1 ++ t0) >>> (44 % 64)).truncate 64 &&& 0x00000fffffffffff#64 &&&
      0xffffffffffc0ffff#64)
    (h2 : r2 = t1 >>> 24 &&& 0xfffffc0ffffffc0f#64) :
    r0.toNat + 2 ^ 44 * r1.toNat + 2 ^ 88 * r2.toNat = clamp (t0.toNat + 2 ^ 64 * t1.toNat) ∧
      r0.toNat ≤ 0xffc0fffffff ∧ r1.toNat ≤ 0xfffffc0ffff ∧ r2.toNat ≤ 0x00ffffffc0f := by
  simp only [Nat.reduceMod] at h1
  have b0 : r0.toNat ≤ 0xffc0fffffff := by
    rw [h0, BitVec.and_assoc, BitVec.toNat_and]
    exact le_trans Nat.and_le_right (by decide)
  have b1 : r1.toNat ≤ 0xfffffc0ffff := by
    rw [h1, BitVec.and_assoc, BitVec.toNat_and]
    exact le_trans Nat.and_le_right (by decide)
  have ht0 := t0.isLt
  have ht1 := t1.isLt
  have hr2 : r2.toNat < 2 ^ 40 := by
    rw [h2, BitVec.toNat_and]
    refine lt_of_le_of_lt Nat.and_le_left ?_
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have key : r0.toNat + 2 ^ 44 * r1.toNat + 2 ^ 88 * r2.toNat =
      (t0.toNat + 2 ^ 64 * t1.toNat) &&& 0x0ffffffc0ffffffc0ffffffc0fffffff := by
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < 128
    · rw [show r0.toNat + 2 ^ 44 * r1.toNat + 2 ^ 88 * r2.toNat =
          2 ^ 88 * r2.toNat + (2 ^ 44 * r1.toNat + r0.toNat) by omega,
        show t0.toNat + 2 ^ 64 * t1.toNat = 2 ^ 64 * t1.toNat + t0.toNat by omega,
        Nat.testBit_and, Nat.testBit_two_pow_mul_add _ (by omega : 2 ^ 44 * r1.toNat + r0.toNat < 2 ^ 88),
        Nat.testBit_two_pow_mul_add _ (by omega : r0.toNat < 2 ^ 44),
        Nat.testBit_two_pow_mul_add _ ht0]
      simp only [BitVec.testBit_toNat]
      subst h0 h1 h2
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
        BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth]
      interval_cases i <;>
        simp (config := { decide := true }) only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
          BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
          BitVec.truncate_eq_setWidth, Nat.testBit, ↓reduceIte, Nat.reduceAdd, Nat.reduceSub,
          Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, decide_true, decide_false,
          Nat.reduceShiftRight, Nat.reduceAnd, Nat.one_and_eq_mod_two, Nat.reduceMod, bne_self_eq_false,
          Bool.and_self, Nat.reduceBNe, Bool.and_true, Bool.and_false]
    · have hp : 2 ^ 128 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_and,
        Nat.testBit_lt_two_pow (x := 0x0ffffffc0ffffffc0ffffffc0fffffff) (by omega), Bool.and_false]
  have hle := (Nat.and_le_right (n := t0.toNat + 2 ^ 64 * t1.toNat)
    (m := 0x0ffffffc0ffffffc0ffffffc0fffffff))
  refine ⟨key, b0, b1, by omega⟩

theorem leBytes_key16 (key : List (BitVec 8)) (h : key.length = 32) :
    leBytesToNum (key.take 16) =
      (pack64 ((key.drop 0).take 8)).toNat + 2 ^ 64 * (pack64 ((key.drop 8).take 8)).toNat := by
  rw [show (16 : Nat) = 8 + 8 from rfl, List.take_add, leBytesToNum_append_x,
    leBytesToNum_eight _ (by simp; omega), leBytesToNum_eight _ (by simp; omega), List.drop_zero]
  simp [h]

/-! ## The contract -/

set_option maxHeartbeats 4000000 in
theorem init_dev
    (hB : ∀ {rh pad buf rest key m : List (BitVec 8)} {lo : BitVec 64} {fin : BitVec 8},
      RepP rh pad lo buf fin key m → rest.length = 167 →
      RepB (rh ++ pad ++ unpack64 lo ++ buf ++ fin :: rest) key m) :
    donnaInitOk Rep := by
  refine ⟨by decide, fun pl hP hG X hZ hM hD => ?_⟩
  intro x R s0 hpc hrun hpre hal hCL
  obtain ⟨ro, st, key⟩ := x
  have hfa : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.fnAddr pl
      "crypto_onetimeauth_poly1305_donna_init [libsodium_la_poly1305_donna]" =
      pl.base + BitVec.ofNat 64 940 := rfl
  rw [hfa] at hpc
  simp only [ToBaseSpec.toSpec, initSpec] at hpre ⊢
  rw [sepConj_assoc, sat_pure_sep] at hpre
  obtain ⟨⟨hlen, hkl⟩, hpre⟩ := hpre
  set a := s0.readReg64 Reg.x0 with ha
  set o := s0.readReg64 Reg.x1 with ho
  have har : s0.regs.regs 0#5 = a := by rw [ha]; simp [readGpr_unfold, Reg.x0]
  have hor : s0.regs.regs 1#5 = o := by rw [ho]; simp [readGpr_unfold, Reg.x1]
  -- the state bytes: nine cells, the buffer, the `final` byte, the rest
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, st.drop 88 = b :: rest := by
    cases h : st.drop 88 with
    | nil => have := congrArg List.length h; simp at this; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  have hrestl : rest.length = 167 := by
    have := congrArg List.length hbr; simp at this; omega
  set buf := (st.drop 72).take 16 with hbuf
  have hbufl : buf.length = 16 := by simp [hbuf]; omega
  have e1 : st = st.take 72 ++ buf ++ b :: rest := by
    rw [← hbr, hbuf, List.append_assoc, show 88 = 72 + 16 from rfl, ← List.drop_drop,
      List.take_append_drop, List.take_append_drop]
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, hC⟩ : ∃ c0 c1 c2 c3 c4 c5 c6 c7 c8 : BitVec 64,
      chunks 9 (st.take 72) = [c0, c1, c2, c3, c4, c5, c6, c7, c8] :=
    ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  rw [e1, bytes_layout a _ _ _ _ (by simp; omega) hbufl,
    bytes_eq_cellsFrom 9 a _ (by simp; omega), hC] at hpre
  have h0 := Satisfies.of_eq hpre (Q := cellsFrom a [c0, c1, c2, c3, c4, c5, c6, c7, c8] ∗
    ((a + BitVec.ofNat 64 88) ↦ₛ [b]) ∗ bytesIn ro o key ∗
    (((a + BitVec.ofNat 64 72) ↦ₛ buf) ∗ ((a + BitVec.ofNat 64 89) ↦ₛ rest) ∗ R))
  generalize hG : (((a + BitVec.ofNat 64 72) ↦ₛ buf) ∗ ((a + BitVec.ofNat 64 89) ↦ₛ rest) ∗ R) = G
    at h0
  clear hpre
  -- the key words
  have hk0 := Satisfies.of_eq h0 (Q := bytesIn ro o key ∗
    (cellsFrom a [c0, c1, c2, c3, c4, c5, c6, c7, c8] ∗ ((a + BitVec.ofNat 64 88) ↦ₛ [b]) ∗ G))
  have k0 := bytesIn_read64 hk0 0 (by omega)
  have k1 := bytesIn_read64 hk0 8 (by omega)
  have k2 := bytesIn_read64 hk0 16 (by omega)
  have k3 := bytesIn_read64 hk0 24 (by omega)
  generalize ht0 : pack64 ((key.drop 0).take 8) = t0 at k0
  generalize ht1 : pack64 ((key.drop 8).take 8) = t1 at k1
  generalize hp0 : pack64 ((key.drop 16).take 8) = p0 at k2
  generalize hp1 : pack64 ((key.drop 24).take 8) = p1 at k3
  -- the run
  show Reach (prog pl X) s0 _
  refine reach_congr (s' := mkS s0 (pl.base + BitVec.ofNat 64 940) s0.regs.regs s0.sp s0.pstate
    s0.mem s0.vregs.regs) (by rw [← hpc]; rfl) ?_
  -- 940: bti c
  refine Reach.mkC hrun hCL (fI_940 hP hCL (KeepsFrozen_refl _)) ?_
  rw [ex_hint, pc_add]
  intro hCL0
  -- 944: ldp x2, x3, [x1]
  refine Reach.mkC hrun hCL0 (fI_944 hP hCL0 (KeepsFrozen_refl _)) ?_
  rw [ex_ldp64_gpr 2#5 3#5 1#5 (by decide) (by decide) (by decide) o 0#64 t0 t1 hor k0.2
    (by rw [pc_add]; exact k1.2) k0.1 (by rw [pc_add]; exact k1.1), pc_add]
  intro hCL1
  -- 948: stp xzr, xzr, [x0, #0x18]
  refine Reach.mkC hrun hCL1 (fI_948 hP hCL1 (KeepsFrozen_refl _)) ?_
  rw [ex_stp64_gpr .xzr .xzr 0#5 (by decide) a 0x18#64 0#64 0#64 ?v1 ?v2 ?v3
    (cellCW h0 3 (by simp) _ rfl) (cellCW h0 4 (by simp) _ (by rw [pc_add])), pc_add]
  case v1 => simp [har]
  case v2 => simp
  case v3 => simp
  intro hCL2
  have w1 := cellW (cellW h0 3 (by simp) (a + 0x18#64) rfl 0#64) 4 (by simp)
    (a + 0x18#64 + 8#64) (by rw [pc_add]) 0#64
  simp only [List.set_cons_succ, List.set_cons_zero] at w1
  -- 952: str xzr, [x0, #0x28]
  refine Reach.mkC hrun hCL2 (fI_952 hP hCL2 (KeepsFrozen_refl _)) ?_
  rw [ex_str64_xzr 0#5 (by decide) a 0x28#64 ?v1 (cellCW w1 5 (by simp) _ rfl), pc_add]
  case v1 => simp [har]
  intro hCL3
  have w2 := cellW w1 5 (by simp) (a + 0x28#64) rfl 0#64
  simp only [List.set_cons_succ, List.set_cons_zero] at w2
  -- 956: and x4, x2, #0xfffffffffff
  refine Reach.mkC hrun hCL3 (fI_956 hP hCL3 (KeepsFrozen_refl _)) ?_
  rw [ex_and_imm 4#5 2#5 (by decide) (by decide) _ t0 ?v1, pc_add]
  case v1 => simp
  intro hCL4
  -- 960: extr x2, x3, x2, #44
  refine Reach.mkC hrun hCL4 (fI_960 hP hCL4 (KeepsFrozen_refl _)) ?_
  rw [ex_extr64 2#5 3#5 2#5 (by decide) (by decide) (by decide) 44 t1 t0 ?v1 ?v2, pc_add]
  case v1 => simp
  case v2 => simp
  intro hCL5
  generalize he : ((t1 ++ t0) >>> (44 % 64)).truncate 64 = e44
  -- 964: and x2, x2, #0xfffffffffff
  refine Reach.mkC hrun hCL5 (fI_964 hP hCL5 (KeepsFrozen_refl _)) ?_
  rw [ex_and_imm 2#5 2#5 (by decide) (by decide) _ e44 ?v1, pc_add]
  case v1 => simp
  intro hCL6
  -- 968: and x4, x4, #0xfffffffc0fffffff
  refine Reach.mkC hrun hCL6 (fI_968 hP hCL6 (KeepsFrozen_refl _)) ?_
  rw [ex_and_imm 4#5 4#5 (by decide) (by decide) _ (t0 &&& 0x00000fffffffffff#64) ?v1, pc_add]
  case v1 => simp
  intro hCL7
  generalize hr0 : t0 &&& 0x00000fffffffffff#64 &&& 0xfffffffc0fffffff#64 = r0v
  -- 972: and x2, x2, #0xffffffffffc0ffff
  refine Reach.mkC hrun hCL7 (fI_972 hP hCL7 (KeepsFrozen_refl _)) ?_
  rw [ex_and_imm 2#5 2#5 (by decide) (by decide) _ (e44 &&& 0x00000fffffffffff#64) ?v1, pc_add]
  case v1 => simp
  intro hCL8
  generalize hr1 : e44 &&& 0x00000fffffffffff#64 &&& 0xffffffffffc0ffff#64 = r1v
  -- 976: stp x4, x2, [x0]
  refine Reach.mkC hrun hCL8 (fI_976 hP hCL8 (KeepsFrozen_refl _)) ?_
  rw [ex_stp64_gpr (.gpr 4#5) (.gpr 2#5) 0#5 (by decide) a 0#64 r0v r1v ?v1 ?v2 ?v3
    (cellCW w2 0 (by simp) _ rfl) (cellCW w2 1 (by simp) _ (by rw [pc_add])), pc_add]
  case v1 => simp [har]
  case v2 => simp
  case v3 => simp
  intro hCL9
  have w3 := cellW (cellW w2 0 (by simp) (a + 0#64) rfl r0v) 1 (by simp)
    (a + 0#64 + 8#64) (by rw [pc_add]) r1v
  simp only [List.set_cons_succ, List.set_cons_zero] at w3
  -- 980: mov x2, #0xfffff0000
  refine Reach.mkC hrun hCL9 (fI_980 hP hCL9 (KeepsFrozen_refl _)) ?_
  rw [ex_orr_imm_xzr 2#5 (by decide), pc_add]
  intro hCL10
  -- 984: movk x2, #0xfc0f
  refine Reach.mkC hrun hCL10 (fI_984 hP hCL10 (KeepsFrozen_refl _)) ?_
  rw [ex_movk_fc0f 2#5 (by decide) ?v1, pc_add]
  case v1 => simp
  intro hCL11
  -- 988: and x3, x2, x3, lsr #24
  refine Reach.mkC hrun hCL11 (fI_988 hP hCL11 (KeepsFrozen_refl _)) ?_
  rw [ex_and_lsr 3#5 2#5 3#5 (by decide) (by decide) (by decide) 0x0000000ffffffc0f#64 t1 ?v1 ?v2, pc_add]
  case v1 => simp
  case v2 => simp
  intro hCL12
  rw [mask_r2]
  generalize hr2 : t1 >>> 24 &&& 0xfffffc0ffffffc0f#64 = r2v
  -- 992: str x3, [x0, #0x10]
  refine Reach.mkC hrun hCL12 (fI_992 hP hCL12 (KeepsFrozen_refl _)) ?_
  rw [ex_str64_gpr' 3#5 0#5 (by decide) (by decide) a 0x10#64 r2v ?v1 ?v2
    (cellCW w3 2 (by simp) _ rfl), pc_add]
  case v1 => simp [har]
  case v2 => simp
  intro hCL13
  have w4 := cellW w3 2 (by simp) (a + 0x10#64) rfl r2v
  simp only [List.set_cons_succ, List.set_cons_zero] at w4
  -- 996: ldr x2, [x1, #0x10]
  have k2' := bytesIn_read64 (Satisfies.of_eq w4 (Q := bytesIn ro o key ∗
    (cellsFrom a [r0v, r1v, r2v, 0#64, 0#64, 0#64, c6, c7, c8] ∗
      ((a + BitVec.ofNat 64 88) ↦ₛ [b]) ∗ G))) 16 (by omega)
  rw [hp0] at k2'
  refine Reach.mkC hrun hCL13 (fI_996 hP hCL13 (KeepsFrozen_refl _)) ?_
  rw [ex_ldr64_gpr 2#5 1#5 (by decide) (by decide) o 0x10#64 p0 ?v1 k2'.2 k2'.1, pc_add]
  case v1 => simp [hor]
  intro hCL14
  -- 1000: str x2, [x0, #0x30]
  refine Reach.mkC hrun hCL14 (fI_1000 hP hCL14 (KeepsFrozen_refl _)) ?_
  rw [ex_str64_gpr' 2#5 0#5 (by decide) (by decide) a 0x30#64 p0 ?v1 ?v2
    (cellCW w4 6 (by simp) _ rfl), pc_add]
  case v1 => simp [har]
  case v2 => simp
  intro hCL15
  have w5 := cellW w4 6 (by simp) (a + 0x30#64) rfl p0
  simp only [List.set_cons_succ, List.set_cons_zero] at w5
  -- 1004: ldr x1, [x1, #0x18]
  have k3' := bytesIn_read64 (Satisfies.of_eq w5 (Q := bytesIn ro o key ∗
    (cellsFrom a [r0v, r1v, r2v, 0#64, 0#64, 0#64, p0, c7, c8] ∗
      ((a + BitVec.ofNat 64 88) ↦ₛ [b]) ∗ G))) 24 (by omega)
  rw [hp1] at k3'
  refine Reach.mkC hrun hCL15 (fI_1004 hP hCL15 (KeepsFrozen_refl _)) ?_
  rw [ex_ldr64_gpr 1#5 1#5 (by decide) (by decide) o 0x18#64 p1 ?v1 k3'.2 k3'.1, pc_add]
  case v1 => simp [hor]
  intro hCL16
  -- 1008: stp x1, xzr, [x0, #0x38]
  refine Reach.mkC hrun hCL16 (fI_1008 hP hCL16 (KeepsFrozen_refl _)) ?_
  rw [ex_stp64_gpr (.gpr 1#5) .xzr 0#5 (by decide) a 0x38#64 p1 0#64 ?v1 ?v2 ?v3
    (cellCW w5 7 (by simp) _ rfl) (cellCW w5 8 (by simp) _ (by rw [pc_add])), pc_add]
  case v1 => simp [har]
  case v2 => simp
  case v3 => simp
  intro hCL17
  have w6 := cellW (cellW w5 7 (by simp) (a + 0x38#64) rfl p1) 8 (by simp)
    (a + 0x38#64 + 8#64) (by rw [pc_add]) 0#64
  simp only [List.set_cons_succ, List.set_cons_zero] at w6
  -- 1012: strb wzr, [x0, #0x58]
  have wb := Satisfies.of_eq w6 (Q := ((a + BitVec.ofNat 64 88) ↦ₛ [b]) ∗
    (cellsFrom a [r0v, r1v, r2v, 0#64, 0#64, 0#64, p0, p1, 0#64] ∗ bytesIn ro o key ∗ G))
  refine Reach.mkC hrun hCL17 (fI_1012 hP hCL17 (KeepsFrozen_refl _)) ?_
  rw [ex_strb_xzr 0#5 (by decide) a 0x58#64 ?v1 (byteCW wb), pc_add]
  case v1 => simp [har]
  intro hCL18
  have w7 := Satisfies.of_eq (byteW wb 0#8) (Q := cellsFrom a [r0v, r1v, r2v, 0#64, 0#64, 0#64, p0, p1, 0#64] ∗
    ((a + BitVec.ofNat 64 88) ↦ₛ [0#8]) ∗ bytesIn ro o key ∗ G)
  -- 1016: mov w0, #0
  refine Reach.mkC hrun hCL18 (fI_1016 hP hCL18 (KeepsFrozen_refl _)) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  intro hCL19
  -- 1020: ret
  refine Reach.mkC hrun hCL19 (fI_1020 hP hCL19 (KeepsFrozen_refl _)) ?_
  rw [ex_ret]
  intro _
  refine Reach.done ?_
  left
  refine ⟨⟨?_, rfl, hrun⟩, ⟨rfl, ?_⟩, ?_⟩
  · simp [readGpr_unfold, Reg.lr]
  · simp (config := { decide := true }) [CalleeSavedPreserved, readGpr_unfold, mkS_regs', Reg.fp]
    rfl
  · -- the arithmetic
    obtain ⟨hval, hb0, hb1, hb2⟩ := clamp_limbs t0 t1 r0v r1v r2v hr0.symm
      (by rw [← hr1, ← he]) hr2.symm
    have hkey := leBytes_key16 key hkl
    rw [ht0, ht1] at hkey
    set rh := unpack64 r0v ++ unpack64 r1v ++ unpack64 r2v ++ unpack64 0#64 ++ unpack64 0#64 ++
      unpack64 0#64 with hrh
    set pad := unpack64 p0 ++ unpack64 p1 with hpad
    have hl : rLimb rh 0 = r0v.toNat ∧ rLimb rh 1 = r1v.toNat ∧ rLimb rh 2 = r2v.toNat ∧
        hLimb rh 0 = 0 ∧ hLimb rh 1 = 0 ∧ hLimb rh 2 = 0 := by
      simp only [rLimb, hLimb, hrh, List.append_assoc]
      simp [u64At_zero, u64At_ge8, u64At_single]
    obtain ⟨l0, l1, l2, l3, l4, l5⟩ := hl
    have hrhl : rh.length = 48 := by simp [hrh]
    have hpadv : pad = (key.drop 16).take 16 := by
      rw [hpad, ← hp0, ← hp1, unpack64_pack64 _ (by simp; omega),
        unpack64_pack64 _ (by simp; omega), show (16 : Nat) = 8 + 8 from rfl, List.take_add,
        List.drop_drop]
    have hRP : RepP rh pad 0#64 buf 0#8 key [] := by
      refine ⟨hrhl, by simp [hpad], hbufl, hkl, ⟨hrhl, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hpadv,
        by simp, by simp, rfl, ?_⟩
      · rw [l0]; exact hb0
      · rw [l1]; exact hb1
      · rw [l2]; exact hb2
      · rw [l3]; norm_num
      · rw [l4]; norm_num
      · rw [l5]; norm_num
      · simp only [limbVal, l0, l1, l2]; rw [hval, hkey]
      · simp [limbVal, l3, l4, l5, blocksAcc, fullOf]
    simp only [mkS_mem]
    show _ ⊨ (⌜_⌝ ∗ (∃∗ st' : List (BitVec 8), ⌜st'.length = 256 ∧ Rep a st' key []⌝ ∗
      (a ↦ₛ st')) ∗ bytesIn ro o key) ∗ R
    rw [sepConj_assoc, sat_pure_sep]
    refine ⟨by simp [State.readReg32, Reg.x0, mkS_readGpr], ?_⟩
    rw [sepConj_assoc, sepExists_sepConj, sat_sepExists]
    refine ⟨rh ++ pad ++ unpack64 0#64 ++ buf ++ 0#8 :: rest, ?_⟩
    rw [sepConj_assoc, sat_pure_sep]
    refine ⟨⟨by simp [hrhl, hpad, hbufl, hrestl], hB hRP hrestl⟩, ?_⟩
    rw [bytes_layout a _ buf _ rest (by simp [hrhl, hpad]) hbufl]
    have eL : rh ++ pad ++ unpack64 0#64 =
        ([r0v, r1v, r2v, 0#64, 0#64, 0#64, p0, p1, 0#64].map unpack64).flatten := by
      simp [hrh, hpad, List.append_assoc]
    rw [eL, ← cellsFrom_eq_bytes]
    rw [← hG] at w7
    exact Satisfies.of_eq w7

end Poly1305DebianApi.Donna

end
end

section
section
/-! # `crypto_onetimeauth_poly1305_donna_final` (text offset 0x564 = 1380, 8 instructions)

`paciasp; stp x29, x30, [sp, #-16]!; mov x29, sp; bl poly1305_finish; ldp x29, x30, [sp], #16;
autiasp; mov w0, #0; ret`. The call goes through `poly1305_finish`'s contract (milestone M3). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

open Arm64 Arm64.Obj Poly1305Boringssl

section fetch
variable {pl : Placement} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)
  {X : String → Option (State → State)} {m0 : Memory} (hCL : (prog pl X).CodeLoaded m0)
  {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem fF_1380 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1380) = some (.hint 0x19#7) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fF_1384 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1384) =
    some (.stp .W64 (.gpr 29#5) (.gpr 30#5) (.PreIndex .sp 0xfffffffffffffff0#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fF_1388 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1388) =
    some (.addSubImm .W64 .ADD (.gpr 29#5) .sp 0#12 false) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fF_1392 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1392) =
    some (.bl (pl.base + BitVec.ofNat 64 1056 - (pl.base + BitVec.ofNat 64 1392))) := by
  rw [show pl.base + BitVec.ofNat 64 1056 - (pl.base + BitVec.ofNat 64 1392) = 0xfffffffffffffeb0#64
    by bv_omega]
  exact fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fF_1396 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1396) =
    some (.ldp .W64 false (.gpr 29#5) (.gpr 30#5) (.PostIndex .sp 0x10#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fF_1400 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1400) = some (.hint 0x1d#7) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fF_1404 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1404) =
    some (.moveWide .W32 .MOVZ (.gpr 0#5) 0#16 0) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fF_1408 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1408) =
    some (.ret (.gpr 30#5)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩

end fetch

/-! ## The contract -/

theorem take96_facts {st key m : List (BitVec 8)} (h : RepB st key m) :
    (st.take 96).length = 96 ∧ StateOk ((st.take 96).take 48) ∧ u64At (st.take 96) 64 < 16 := by
  obtain ⟨hl, -, hok, -, -, hlo, -⟩ := h
  refine ⟨by simp [hl], ?_, ?_⟩
  · rw [List.take_take, show min 48 96 = 48 from rfl]; exact hok
  · have : u64At (st.take 96) 64 = u64At st 64 := by
      simp only [u64At, List.drop_take, List.take_take, show min 8 (96 - 64) = 8 from rfl]
    rw [this, hlo]; exact Nat.mod_lt _ (by omega)

set_option maxHeartbeats 4000000 in
theorem final_dev
    (hTag : ∀ st key m : List (BitVec 8), RepB st key m → finishTag (st.take 96) = poly1305Mac m key) :
    donnaFinalOk Rep := by
  refine ⟨by decide, fun pl hP hG X hZ hM hD => ?_⟩
  intro x R s0 hpc hrun hpre hal hCL
  obtain ⟨st, key, msg, mac⟩ := x
  have hfa : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.fnAddr pl
      "crypto_onetimeauth_poly1305_donna_final [libsodium_la_poly1305_donna]" =
      pl.base + BitVec.ofNat 64 1380 := rfl
  rw [hfa] at hpc
  simp only [ToBaseSpec.toSpec, finalSpec] at hpre ⊢
  rw [sepConj_assoc, sat_pure_sep] at hpre
  obtain ⟨⟨hlen, hrep, hmac⟩, hpre⟩ := hpre
  have hrep' : RepB st key msg := hrep
  obtain ⟨h96, hok96, hlo96⟩ := take96_facts hrep'
  set a := s0.readReg64 Reg.x0 with ha
  set o := s0.readReg64 Reg.x1 with ho
  set sp0 := s0.sp with hsp0
  have hal0 : sp0 &&& 0b1111#64 = 0#64 := by simpa [State.spAligned] using hal
  set T := sp0 - 16#64 with hT
  -- the stack frame: 4128 bytes for finish, then two cells for x29, x30
  have hsf : stackFrame s0 4144 =
      memRegion (sp0 - BitVec.ofNat 64 4144) (4128 + 16) := rfl
  have eT : sp0 - BitVec.ofNat 64 4144 + BitVec.ofNat 64 4128 = T := by rw [hT]; bv_omega
  rw [hsf] at hpre
  have h1 := Satisfies.of_eq hpre (Q := memRegion (sp0 - BitVec.ofNat 64 4144) (4128 + 16) ∗
    ((a ↦ₛ st) ∗ (o ↦ₛ mac) ∗ R))
  have h2 := sat_sep_mono h1 (memRegion_split _ 4128 16 (by norm_num))
  rw [eT, sepConj_assoc] at h2
  have h3 := sat_sep_mono (Satisfies.of_eq h2 (Q := memRegion T 16 ∗
    (memRegion (sp0 - BitVec.ofNat 64 4144) 4128 ∗ (a ↦ₛ st) ∗ (o ↦ₛ mac) ∗ R)))
    (memRegion_eq_cells T)
  rw [sepExists_sepConj, sat_sepExists] at h3
  obtain ⟨u0, h3⟩ := h3
  rw [sepExists_sepConj, sat_sepExists] at h3
  obtain ⟨u1, h3⟩ := h3
  clear h1 h2 hpre
  -- the run
  show Reach (prog pl X) s0 _
  refine reach_congr (s' := mkS s0 (pl.base + BitVec.ofNat 64 1380) s0.regs.regs sp0 s0.pstate
    s0.mem s0.vregs.regs) (by rw [← hpc]; rfl) ?_
  -- 1380: paciasp
  refine Reach.mkC hrun hCL (fF_1380 hP hCL (KeepsFrozen_refl _)) ?_
  rw [ex_hint, pc_add]
  intro hCL0
  -- 1384: stp x29, x30, [sp, #-16]!
  have eT' : sp0 + 0xfffffffffffffff0#64 = T := by rw [hT]; bv_omega
  rw [sepConj_assoc] at h3
  have c0 := sat64_read h3
  have h3' := Satisfies.of_eq h3 (Q := ((T + 8#64) ↦₆₄ u1) ∗ (T ↦₆₄ u0) ∗
    (memRegion (sp0 - BitVec.ofNat 64 4144) 4128 ∗ (a ↦ₛ st) ∗ (o ↦ₛ mac) ∗ R))
  have c1 := sat64_read h3'
  refine Reach.mkC hrun hCL0 (fF_1384 hP hCL0 (KeepsFrozen_refl _)) ?_
  rw [ex_stp64_pre_sp _ _ (by decide) (by decide) _ hal0 (by rw [eT']; exact c0.2.2)
    (by rw [eT']; exact c1.2.2), eT', pc_add]
  intro hCL1
  have w0 := sat64_write h3 (s0.regs.regs 29#5)
  have w1 := sat64_write (Satisfies.of_eq w0 (Q := ((T + 8#64) ↦₆₄ u1) ∗ (T ↦₆₄ s0.regs.regs 29#5) ∗
    (memRegion (sp0 - BitVec.ofNat 64 4144) 4128 ∗ (a ↦ₛ st) ∗ (o ↦ₛ mac) ∗ R)))
    (s0.regs.regs 30#5)
  generalize hm1 : (s0.mem.write64 T (s0.regs.regs 29#5)).write64 (T + 8#64) (s0.regs.regs 30#5) = m1
    at w1 hCL1 ⊢
  clear w0 h3 h3' c0 c1
  -- 1388: mov x29, sp
  refine Reach.mkC hrun hCL1 (fF_1388 hP hCL1 (KeepsFrozen_refl _)) ?_
  rw [ex_add_gpr_sp _ (by decide), z12 _ (by norm_num), pc_add]
  intro hCL2
  -- 1392: bl poly1305_finish
  have hTal : T &&& 0b1111#64 = 0#64 := by rw [hT]; exact al16_sub _ 16 (by norm_num) (by norm_num) hal0
  rw [show (1380 + 4 + 4 + 4 : Nat) = 1392 from rfl]
  set r2 := upd s0.regs.regs 29#5 (T + BitVec.ofNat 64 0) with hr2
  set s1 := mkS s0 (pl.base + BitVec.ofNat 64 1056)
    (upd r2 30#5 (pl.base + BitVec.ofNat 64 1392 + 4#64)) T s0.pstate m1 s0.vregs.regs with hs1
  have e0 : s1.readReg64 Reg.x0 = a := by
    simp only [hs1, hr2, ha, mkS_readGpr, readGpr_unfold, upd_apply]; simp [Reg.x0, mkS, upd_apply]
  have e1 : s1.readReg64 Reg.x1 = o := by
    simp only [hs1, hr2, ho, mkS_readGpr, readGpr_unfold, upd_apply]; simp [Reg.x1, mkS, upd_apply]
  have estk : stackFrame s1 4128 = memRegion (sp0 - BitVec.ofNat 64 4144) 4128 := by
    show memRegion (T - BitVec.ofNat 64 4128) 4128 = _
    rw [show T - BitVec.ofNat 64 4128 = sp0 - BitVec.ofNat 64 4144 by rw [hT]; bv_omega]
  have hsplit := pointsToBytes_split a st 96 (by omega)
  have hpre : m1 ⊨ finishSpec.pre (st.take 96, mac) s1 ∗ (((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96) ∗ ((T + 8#64) ↦₆₄ s0.regs.regs 30#5) ∗
    (T ↦₆₄ s0.regs.regs 29#5) ∗ R) := by
    show m1 ⊨ (⌜(st.take 96).length = 96 ∧ StateOk ((st.take 96).take 48) ∧
        u64At (st.take 96) 64 < 16 ∧ mac.length = 16⌝ ∗
      (s1.readReg64 Reg.x0 ↦ₛ st.take 96) ∗ (s1.readReg64 Reg.x1 ↦ₛ mac) ∗ stackFrame s1 4128) ∗ (((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96) ∗ ((T + 8#64) ↦₆₄ s0.regs.regs 30#5) ∗
    (T ↦₆₄ s0.regs.regs 29#5) ∗ R)
    rw [e0, e1, estk, sepConj_assoc, sat_pure_sep]
    refine ⟨⟨h96, hok96, hlo96, hmac⟩, ?_⟩
    rw [hsplit] at w1
    exact Satisfies.of_eq w1
  refine call_ok finishSpec (finish_ok ⟨hP, hG, hZ, hM, hD⟩) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) (st.take 96, mac) (((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96) ∗ ((T + 8#64) ↦₆₄ s0.regs.regs 30#5) ∗
    (T ↦₆₄ s0.regs.regs 29#5) ∗ R) hrun (fF_1392 hP hCL2 (KeepsFrozen_refl _)) hTal hCL2
    hpre ?_
  intro sf hrunf hpcf hspf hkept hvf hkf hpost
  have hCL3 : (prog pl X).CodeLoaded sf.mem := codeLoaded_keepsFrozen hCL2 hkf
  change sf.mem ⊨ ((s1.readReg64 Reg.x0 ↦ₛ List.replicate 96 0#8) ∗
    (s1.readReg64 Reg.x1 ↦ₛ finishTag (st.take 96)) ∗ stackFrame s1 4128) ∗ (((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96) ∗ ((T + 8#64) ↦₆₄ s0.regs.regs 30#5) ∗
    (T ↦₆₄ s0.regs.regs 29#5) ∗ R) at hpost
  rw [e0, e1, estk] at hpost
  refine reach_congr (s' := mkS sf (pl.base + BitVec.ofNat 64 1396) sf.regs.regs T sf.pstate
    sf.mem sf.vregs.regs) (by
      rw [show pl.base + BitVec.ofNat 64 1396 = sf.pc by rw [hpcf, pc_add], ← hspf]; rfl) ?_
  -- 1396: ldp x29, x30, [sp], #16
  have hq := Satisfies.of_eq hpost (Q := (T ↦₆₄ s0.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ s0.regs.regs 30#5) ∗
    ((a ↦ₛ List.replicate 96 0#8) ∗ (o ↦ₛ finishTag (st.take 96)) ∗
      memRegion (sp0 - BitVec.ofNat 64 4144) 4128 ∗ ((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96) ∗ R))
  have d0 := sat64_read hq
  have d1 := sat64_read (Satisfies.of_eq hq (Q := ((T + 8#64) ↦₆₄ s0.regs.regs 30#5) ∗ (T ↦₆₄ s0.regs.regs 29#5) ∗
    ((a ↦ₛ List.replicate 96 0#8) ∗ (o ↦ₛ finishTag (st.take 96)) ∗
      memRegion (sp0 - BitVec.ofNat 64 4144) 4128 ∗ ((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96) ∗ R)))
  refine Reach.mkC hrunf hCL3 (fF_1396 hP hCL3 (KeepsFrozen_refl _)) ?_
  rw [ex_ldp64_post_sp _ _ (by decide) (by decide) _ hTal d0.2.1 d1.2.1, pc_add, d0.1, d1.1]
  intro hCL4
  -- 1400: autiasp
  refine Reach.mkC hrunf hCL4 (fF_1400 hP hCL4 (KeepsFrozen_refl _)) ?_
  rw [ex_hint, pc_add]
  intro hCL5
  -- 1404: mov w0, #0
  refine Reach.mkC hrunf hCL5 (fF_1404 hP hCL5 (KeepsFrozen_refl _)) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  intro hCL6
  -- 1408: ret
  refine Reach.mkC hrunf hCL6 (fF_1408 hP hCL6 (KeepsFrozen_refl _)) ?_
  rw [ex_ret]
  intro _
  refine Reach.done ?_
  have hS : T + 0x10#64 = sp0 := by rw [hT]; bv_omega
  left
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · simp [upd_apply, readGpr_unfold, Reg.lr]
  · exact hS
  · exact hrunf
  · exact hS
  · have k := hkept
    simp only [KeptRegs] at k
    simp (config := { decide := true }) only [CalleeSavedPreserved, readGpr_unfold, mkS_regs',
      mkS_vregs', upd_apply, ↓reduceIte, Reg.fp, hr2]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial, ?_⟩
    all_goals first
      | (rw [k _ (by decide) (by decide)]; simp (config := { decide := true }) [hr2, upd_apply])
      | exact hvf
  · simp only [mkS_mem, mkS_sp]
    rw [sepConj_assoc, sat_pure_sep]
    refine ⟨by simp [State.readReg32, upd_apply], ?_⟩
    have hz := pointsToBytes_append a (List.replicate 96 0#8) (st.drop 96)
    rw [List.length_replicate] at hz
    have hm := Satisfies.of_eq hq (Q := ((T ↦₆₄ s0.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ s0.regs.regs 30#5)) ∗
      (((a ↦ₛ List.replicate 96 0#8) ∗ ((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96)) ∗
        (o ↦ₛ finishTag (st.take 96)) ∗ memRegion (sp0 - BitVec.ofNat 64 4144) 4128 ∗ R))
    have hm2 := sat_sep_mono hm (cells_entails_memRegion T _ _)
    rw [← hz, hTag st key msg hrep'] at hm2
    have hm3 := Satisfies.of_eq hm2 (Q := (memRegion (sp0 - BitVec.ofNat 64 4144) 4128 ∗ memRegion T 16) ∗
      ((a ↦ₛ (List.replicate 96 0#8 ++ st.drop 96)) ∗ (o ↦ₛ poly1305Mac msg key) ∗ R))
    have hm4 := sat_sep_mono hm3 (memRegion_merge _ T 4128 16 eT.symm (by norm_num) (by norm_num))
    have es : T + 0x10#64 - BitVec.ofNat 64 4144 = sp0 - BitVec.ofNat 64 4144 := by rw [hS]
    simp only [stackFrame, mkS_sp, es]
    exact Satisfies.of_eq hm4

end Poly1305DebianApi.Donna

end
end

section
section
/-! # Arithmetic and byte-list facts about the representation predicate

`pack64` (`Poly1305Libsodium.Goal.pack64`, Frame.lean) and `unpack64` (`Arm64.unpack64`,
Pieces.lean) convert between 8 bytes and a 64-bit word. -/

set_option autoImplicit false

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

open Arm64 Poly1305Boringssl

/-! ## Helper lemmas -/

theorem leBytesToNum_append (xs ys : List (BitVec 8)) :
    leBytesToNum (xs ++ ys) = leBytesToNum xs + 256 ^ xs.length * leBytesToNum ys := by
  induction xs with
  | nil => simp [leBytesToNum]
  | cons x xs ih =>
    simp only [leBytesToNum, List.foldr_cons, List.cons_append, List.length_cons] at ih ⊢
    rw [ih, Nat.pow_succ]
    simp only [Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]
    rw [Nat.mul_left_comm 256]

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

theorem p1305_pos : 0 < p1305 := by unfold p1305; decide


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

theorem foldl_lt {f : Nat → Nat → Nat} (hf : ∀ a i, f a i < p1305) (l : List Nat) (a : Nat)
    (ha : a < p1305) : l.foldl f a < p1305 := by
  induction l generalizing a with
  | nil => exact ha
  | cons i l ih => exact ih _ (hf a i)

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

theorem blocksAcc_lt (r hb a : Nat) (c : List (BitVec 8)) (ha : a < p1305) :
    blocksAcc r hb a c < p1305 :=
  foldl_lt (fun _ _ => Nat.mod_lt _ p1305_pos) _ _ ha

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

theorem leBytesToNum_one : leBytesToNum [1#8] = 1 := by decide

theorem accumulate_full (r a : Nat) (m : List (BitVec 8)) :
    (List.range (m.length / 16)).foldl
      (fun a i => r * (a + leBytesToNum ((m.drop (16 * i)).take 16 ++ [1#8])) % p1305) a =
    blocksAcc r (2 ^ 128) a (fullOf m) := by
  unfold blocksAcc fullOf
  have hl : (m.take (16 * (m.length / 16))).length / 16 = m.length / 16 := by simp; omega
  rw [hl]
  apply foldl_ext'
  intro a i hi
  rw [List.mem_range] at hi
  rw [List.drop_take, List.take_take, show min 16 (16 * (m.length / 16) - 16 * i) = 16 by omega,
    leBytesToNum_append, leBytesToNum_one, List.length_take, List.length_drop,
    show min 16 (m.length - 16 * i) = 16 by omega, Nat.add_assoc]
  rfl

theorem accumulate_eq (r : Nat) (m : List (BitVec 8)) :
    accumulate r 0 m = if m.length % 16 = 0 then blocksAcc r (2 ^ 128) 0 (fullOf m) else
      r * (blocksAcc r (2 ^ 128) 0 (fullOf m) +
        leBytesToNum (m.drop (16 * (m.length / 16)) ++ [1#8])) % p1305 := by
  unfold accumulate
  split
  · rw [show (m.length + 15) / 16 = m.length / 16 by omega, accumulate_full]
  · rw [show (m.length + 15) / 16 = m.length / 16 + 1 by omega, List.range_succ,
      List.foldl_append, accumulate_full]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [List.take_of_length_le (by simp; omega)]


/-- A state's bytes as its fields. -/
theorem repP_of_repB {st key m : List (BitVec 8)} (h : RepB st key m) :
    RepP (st.take 48) ((st.drop 48).take 16) (pack64 ((st.drop 64).take 8)) ((st.drop 72).take 16)
      (st.getD 88 0#8) key m ∧
    st = st.take 48 ++ (st.drop 48).take 16 ++ unpack64 (pack64 ((st.drop 64).take 8)) ++
      (st.drop 72).take 16 ++ st.getD 88 0#8 :: st.drop 89 := by
  obtain ⟨hlen, hkey, hok, hr, hpad, hlo, hbuf, hfin, hh⟩ := h
  have e8 : ((st.drop 64).take 8).length = 8 := by simp; omega
  refine ⟨⟨by simp; omega, by simp; omega, by simp; omega, hkey, hok,
    by rw [limbVal_rLimb_take _ _ (by omega)]; exact hr, hpad,
    by rw [pack64_toNat _ e8]; exact hlo, ?_, hfin,
    by rw [limbVal_hLimb_take _ _ (by omega), limbVal_rLimb_take _ _ (by omega)]; exact hh⟩, ?_⟩
  · rw [List.take_take, show min (m.length % 16) 16 = m.length % 16 by omega]; exact hbuf
  · have hd : st.drop 88 = st.getD 88 0#8 :: st.drop 89 := by
      rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      rfl
    have e1 : st.drop 88 = (st.drop 72).drop 16 := by rw [List.drop_drop]
    have e2 : st.drop 72 = (st.drop 64).drop 8 := by rw [List.drop_drop]
    have e3 : st.drop 64 = (st.drop 48).drop 16 := by rw [List.drop_drop]
    rw [unpack64_pack64 _ e8]
    symm
    simp only [List.append_assoc]
    rw [← hd, e1, List.take_append_drop, e2, List.take_append_drop, e3, List.take_append_drop,
      List.take_append_drop]

/-- Fields assembled into a state. -/
theorem repB_of_repP {rh pad buf rest key m : List (BitVec 8)} {lo : BitVec 64} {fin : BitVec 8}
    (h : RepP rh pad lo buf fin key m) (hr : rest.length = 167) :
    RepB (rh ++ pad ++ unpack64 lo ++ buf ++ fin :: rest) key m := by
  obtain ⟨hrh, hpad, hbuf, hkey, hok, hrr, hpadeq, hlo, hbufeq, hfin, hh⟩ := h
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ :=
    layout (rest := rest) (fin := fin) hrh hpad (unpack64_length lo) hbuf
  have hR := limbVal_rLimb_take (rh ++ pad ++ unpack64 lo ++ buf ++ fin :: rest) 48 (by omega)
  have hH := limbVal_hLimb_take (rh ++ pad ++ unpack64 lo ++ buf ++ fin :: rest) 48 (by omega)
  rw [l1] at hR hH
  refine ⟨by rw [l6, hr], hkey, by rw [l1]; exact hok, by rw [← hR]; exact hrr,
    by rw [l2, hpadeq], ?_, ?_, by rw [l5, hfin], by rw [← hR, ← hH]; exact hh⟩
  · unfold u64At; rw [l3, leBytesToNum_unpack64, hlo]
  · rw [l4, List.take_append_of_le_length (by omega)]; exact hbufeq

/-- The tag `poly1305_finish` computes from a represented state is RFC 8439's MAC. -/
theorem finishTag_repP {rh pad buf rest key m : List (BitVec 8)} {lo : BitVec 64} {fin : BitVec 8}
    (h : RepP rh pad lo buf fin key m) (hr : rest.length = 7) :
    finishTag (rh ++ pad ++ unpack64 lo ++ buf ++ fin :: rest) = poly1305Mac m key := by
  obtain ⟨hrh, hpad, hbuf, hkey, hok, hrr, hpadeq, hlo, hbufeq, hfin, hh⟩ := h
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ :=
    layout (rest := rest) (fin := fin) hrh hpad (unpack64_length lo) hbuf
  have hR := limbVal_rLimb_take (rh ++ pad ++ unpack64 lo ++ buf ++ fin :: rest) 48 (by omega)
  have hH := limbVal_hLimb_take (rh ++ pad ++ unpack64 lo ++ buf ++ fin :: rest) 48 (by omega)
  rw [l1] at hR hH
  have hL : u64At (rh ++ pad ++ unpack64 lo ++ buf ++ fin :: rest) 64 = m.length % 16 := by
    unfold u64At; rw [l3, leBytesToNum_unpack64, hlo]
  have hT : ((rh ++ pad ++ unpack64 lo ++ buf ++ fin :: rest).drop 72).take (m.length % 16) =
      m.drop (16 * (m.length / 16)) := by
    rw [l4, List.take_append_of_le_length (by omega)]; exact hbufeq
  simp only [finishTag, poly1305Mac]
  rw [hL, ← hR, ← hH, l2, hT, ← hrr, ← hpadeq, accumulate_eq]
  congr 2
  have hB := blocksAcc_lt (limbVal (rLimb rh)) (2 ^ 128) 0 (fullOf m) p1305_pos
  split
  · rw [hh, Nat.mod_eq_of_lt hB]
  · rw [Nat.mod_mod, mul_add_mod_left, hh, ← mul_add_mod_left]

theorem take_layout {rh pad w buf rest : List (BitVec 8)} {fin : BitVec 8}
    (h1 : rh.length = 48) (h2 : pad.length = 16) (h3 : w.length = 8) (h4 : buf.length = 16) :
    (rh ++ pad ++ w ++ buf ++ fin :: rest).take 96 = rh ++ pad ++ w ++ buf ++ fin :: rest.take 7 := by
  simp only [List.append_assoc]
  rw [List.take_append, List.take_of_length_le (by omega), h1, List.take_append,
    List.take_of_length_le (by omega), h2, List.take_append, List.take_of_length_le (by omega), h3,
    List.take_append, List.take_of_length_le (by omega), h4]
  rfl

theorem finishTag_rep (st key m : List (BitVec 8)) (h : RepB st key m) :
    finishTag (st.take 96) = poly1305Mac m key := by
  obtain ⟨hP, hst⟩ := repP_of_repB h
  have hlen : st.length = 256 := h.1
  have e : st.take 96 = st.take 48 ++ (st.drop 48).take 16 ++
      unpack64 (pack64 ((st.drop 64).take 8)) ++ (st.drop 72).take 16 ++
      st.getD 88 0#8 :: (st.drop 89).take 7 := by
    conv_lhs => rw [hst]
    exact take_layout hP.1 hP.2.1 (unpack64_length _) hP.2.2.1
  rw [e]
  exact finishTag_repP hP (by simp; omega)

end Poly1305DebianApi.Donna

end
end

section
section
/-! # One `poly1305_update` call is one step of the representation predicate

`Absorbs` (bundle `Poly1305Debian_Spec`, the contract of milestone M2) on the first 96 bytes of a
state that represents `m` gives a state that represents `m ++ inp`. -/

set_option autoImplicit false

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

open Arm64 Poly1305Boringssl

theorem u64At_append_left (xs ys : List (BitVec 8)) (off : Nat) (h : off + 8 ≤ xs.length) :
    u64At (xs ++ ys) off = u64At xs off := by
  have := u64At_take (xs ++ ys) xs.length off h
  rw [List.take_left' rfl] at this
  exact this.symm

theorem limbVal_rLimb_append (xs ys : List (BitVec 8)) (h : 24 ≤ xs.length) :
    limbVal (rLimb (xs ++ ys)) = limbVal (rLimb xs) := by
  have := limbVal_rLimb_take (xs ++ ys) xs.length h
  rw [List.take_left' rfl] at this
  exact this.symm

theorem limbVal_hLimb_append (xs ys : List (BitVec 8)) (h : 48 ≤ xs.length) :
    limbVal (hLimb (xs ++ ys)) = limbVal (hLimb xs) := by
  have := limbVal_hLimb_take (xs ++ ys) xs.length h
  rw [List.take_left' rfl] at this
  exact this.symm

theorem limbVal_rLimb_eq_of_take24 {xs ys : List (BitVec 8)} (h : xs.take 24 = ys.take 24) :
    limbVal (rLimb xs) = limbVal (rLimb ys) := by
  rw [← limbVal_rLimb_take xs 24 le_rfl, h, limbVal_rLimb_take ys 24 le_rfl]

theorem fullOf_append (m inp : List (BitVec 8)) :
    let t := m.drop (16 * (m.length / 16)) ++ inp
    fullOf (m ++ inp) = fullOf m ++ t.take (16 * (t.length / 16)) := by
  intro t
  have hq : 16 * (m.length / 16) ≤ m.length := Nat.mul_div_le _ _
  have ht : t.length = m.length % 16 + inp.length := by
    simp only [t, List.length_append, List.length_drop]; omega
  have hk : 16 * ((m ++ inp).length / 16) = 16 * (m.length / 16) + 16 * (t.length / 16) := by
    rw [ht, List.length_append]; omega
  unfold fullOf
  rw [hk, List.take_add, List.take_append_of_le_length hq, List.drop_append_of_le_length hq]

theorem repB_absorbs {st key m inp st' : List (BitVec 8)} (hr : RepB st key m)
    (ha : Absorbs (st.take 96) inp st') : RepB (st' ++ st.drop 96) key (m ++ inp) := by
  obtain ⟨hl, hk, hok, hrv, hpad, hlo, hbuf, hfin, hh⟩ := hr
  obtain ⟨hl', hr', hpad', hfin', hok', hlo', hbuf', hh'⟩ := ha
  have hlt : m.length % 16 < 16 := Nat.mod_lt _ (by omega)
  have hL : u64At (st.take 96) 64 = m.length % 16 := by rw [u64At_take _ _ _ (by omega), hlo]
  have hbuf0 : ((st.take 96).drop 72).take (m.length % 16) = m.drop (16 * (m.length / 16)) := by
    rw [List.drop_take, List.take_take, show min (m.length % 16) (96 - 72) = m.length % 16 by omega,
      hbuf]
  simp only [hL, hbuf0] at hlo' hbuf' hh'
  generalize htdef : m.drop (16 * (m.length / 16)) ++ inp = t at hlo' hbuf' hh'
  have ht : t.length = m.length % 16 + inp.length := by
    rw [← htdef]; simp only [List.length_append, List.length_drop]
    have : 16 * (m.length / 16) ≤ m.length := Nat.mul_div_le _ _
    omega
  have hfull := fullOf_append m inp
  simp only [htdef] at hfull
  have hlenN : (st' ++ st.drop 96).length = 256 := by simp [hl', hl]
  have e96 : (st' ++ st.drop 96).take 96 = st' := List.take_left' hl'
  have hrst : limbVal (rLimb st') = limbVal (rLimb st) := by
    rw [limbVal_rLimb_eq_of_take24 hr', limbVal_rLimb_take st 96 (by omega)]
  have hmod : t.length - 16 * (t.length / 16) = (m ++ inp).length % 16 := by
    rw [ht, List.length_append]; omega
  have hmod16 : t.length - 16 * (t.length / 16) < 16 := by omega
  refine ⟨hlenN, hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.take_append_of_le_length (by omega)]; exact hok'
  · rw [limbVal_rLimb_append _ _ (by omega), hrst]; exact hrv
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega),
      hpad', List.drop_take, List.take_take, show min 16 (96 - 48) = 16 from rfl]
    exact hpad
  · rw [u64At_append_left _ _ _ (by omega), hlo', hmod]
  · rw [List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by simp; omega), ← hmod, hbuf']
    have hk' : 16 * ((m ++ inp).length / 16) = 16 * (m.length / 16) + 16 * (t.length / 16) := by
      rw [ht, List.length_append]; omega
    rw [hk', ← List.drop_drop, List.drop_append_of_le_length (Nat.mul_div_le _ _), htdef]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD, hfin', List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
      ← List.getD_eq_getElem?_getD, hfin]
  · rw [limbVal_hLimb_append _ _ (by omega), limbVal_rLimb_append _ _ (by omega), hrst, hh',
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), ← List.getD_eq_getElem?_getD,
      hfin, limbVal_rLimb_take st 96 (by omega), limbVal_hLimb_take st 96 (by omega), hfull,
      blocksAcc_mod, hh, ← blocksAcc_mod, blocksAcc_append _ _ _ _ _ (by unfold fullOf; simp; omega)]
    simp [hibit]

end Poly1305DebianApi.Donna

end
end

section
section
/-! # `crypto_onetimeauth_poly1305_donna_update` (text offset 0x400 = 1024, 8 instructions)

`paciasp; stp x29, x30, [sp, #-16]!; mov x29, sp; bl poly1305_update; ldp x29, x30, [sp], #16;
autiasp; mov w0, #0; ret`. The call goes through `poly1305_update`'s contract (milestone M2), and
`repB_absorbs` turns its `Absorbs` into the representation of the longer message. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Donna
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag StateRep)

open Arm64 Arm64.Obj Poly1305Boringssl

section fetch
variable {pl : Placement} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)
  {X : String → Option (State → State)} {m0 : Memory} (hCL : (prog pl X).CodeLoaded m0)
  {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem fU_1024 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1024) = some (.hint 0x19#7) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fU_1028 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1028) =
    some (.stp .W64 (.gpr 29#5) (.gpr 30#5) (.PreIndex .sp 0xfffffffffffffff0#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fU_1032 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1032) =
    some (.addSubImm .W64 .ADD (.gpr 29#5) .sp 0#12 false) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fU_1036 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1036) =
    some (.bl (pl.base + BitVec.ofNat 64 688 - (pl.base + BitVec.ofNat 64 1036))) := by
  rw [show pl.base + BitVec.ofNat 64 688 - (pl.base + BitVec.ofNat 64 1036) = 0xfffffffffffffea4#64
    by bv_omega]
  exact fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fU_1040 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1040) =
    some (.ldp .W64 false (.gpr 29#5) (.gpr 30#5) (.PostIndex .sp 0x10#64)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fU_1044 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1044) = some (.hint 0x1d#7) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fU_1048 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1048) =
    some (.moveWide .W32 .MOVZ (.gpr 0#5) 0#16 0) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩
theorem fU_1052 : (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 1052) =
    some (.ret (.gpr 30#5)) :=
  fetch_at hP hCL hk ⟨⟨by decide, by decide⟩, by decide, by rfl⟩

end fetch

/-! ## The contract -/

set_option maxHeartbeats 4000000 in
theorem update_dev : donnaUpdateOk Rep := by
  refine ⟨by decide, fun pl hP hG X hZ hM hD => ?_⟩
  intro x R s0 hpc hrun hpre hal hCL
  obtain ⟨ro, st, key, msg, inp⟩ := x
  have hfa : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.fnAddr pl
      "crypto_onetimeauth_poly1305_donna_update [libsodium_la_poly1305_donna]" =
      pl.base + BitVec.ofNat 64 1024 := rfl
  rw [hfa] at hpc
  simp only [ToBaseSpec.toSpec, updateSpec] at hpre ⊢
  rw [sepConj_assoc, sat_pure_sep] at hpre
  obtain ⟨⟨hlen, hrep, hx2⟩, hpre⟩ := hpre
  have hrep' : RepB st key msg := hrep
  obtain ⟨h96, hok96, hlo96⟩ := take96_facts hrep'
  set a := s0.readReg64 Reg.x0 with ha
  set o := s0.readReg64 Reg.x1 with ho
  set sp0 := s0.sp with hsp0
  have hal0 : sp0 &&& 0b1111#64 = 0#64 := by simpa [State.spAligned] using hal
  set T := sp0 - 16#64 with hT
  -- the stack frame: 32 bytes for finish, then two cells for x29, x30
  have hsf : stackFrame s0 48 =
      memRegion (sp0 - BitVec.ofNat 64 48) (32 + 16) := rfl
  have eT : sp0 - BitVec.ofNat 64 48 + BitVec.ofNat 64 32 = T := by rw [hT]; bv_omega
  rw [hsf] at hpre
  have h1 := Satisfies.of_eq hpre (Q := memRegion (sp0 - BitVec.ofNat 64 48) (32 + 16) ∗
    ((a ↦ₛ st) ∗ bytesIn ro o inp ∗ R))
  have h2 := sat_sep_mono h1 (memRegion_split _ 32 16 (by norm_num))
  rw [eT, sepConj_assoc] at h2
  have h3 := sat_sep_mono (Satisfies.of_eq h2 (Q := memRegion T 16 ∗
    (memRegion (sp0 - BitVec.ofNat 64 48) 32 ∗ (a ↦ₛ st) ∗ bytesIn ro o inp ∗ R)))
    (memRegion_eq_cells T)
  rw [sepExists_sepConj, sat_sepExists] at h3
  obtain ⟨u0, h3⟩ := h3
  rw [sepExists_sepConj, sat_sepExists] at h3
  obtain ⟨u1, h3⟩ := h3
  clear h1 h2 hpre
  -- the run
  show Reach (prog pl X) s0 _
  refine reach_congr (s' := mkS s0 (pl.base + BitVec.ofNat 64 1024) s0.regs.regs sp0 s0.pstate
    s0.mem s0.vregs.regs) (by rw [← hpc]; rfl) ?_
  -- 1380: paciasp
  refine Reach.mkC hrun hCL (fU_1024 hP hCL (KeepsFrozen_refl _)) ?_
  rw [ex_hint, pc_add]
  intro hCL0
  -- 1384: stp x29, x30, [sp, #-16]!
  have eT' : sp0 + 0xfffffffffffffff0#64 = T := by rw [hT]; bv_omega
  rw [sepConj_assoc] at h3
  have c0 := sat64_read h3
  have h3' := Satisfies.of_eq h3 (Q := ((T + 8#64) ↦₆₄ u1) ∗ (T ↦₆₄ u0) ∗
    (memRegion (sp0 - BitVec.ofNat 64 48) 32 ∗ (a ↦ₛ st) ∗ bytesIn ro o inp ∗ R))
  have c1 := sat64_read h3'
  refine Reach.mkC hrun hCL0 (fU_1028 hP hCL0 (KeepsFrozen_refl _)) ?_
  rw [ex_stp64_pre_sp _ _ (by decide) (by decide) _ hal0 (by rw [eT']; exact c0.2.2)
    (by rw [eT']; exact c1.2.2), eT', pc_add]
  intro hCL1
  have w0 := sat64_write h3 (s0.regs.regs 29#5)
  have w1 := sat64_write (Satisfies.of_eq w0 (Q := ((T + 8#64) ↦₆₄ u1) ∗ (T ↦₆₄ s0.regs.regs 29#5) ∗
    (memRegion (sp0 - BitVec.ofNat 64 48) 32 ∗ (a ↦ₛ st) ∗ bytesIn ro o inp ∗ R)))
    (s0.regs.regs 30#5)
  generalize hm1 : (s0.mem.write64 T (s0.regs.regs 29#5)).write64 (T + 8#64) (s0.regs.regs 30#5) = m1
    at w1 hCL1 ⊢
  clear w0 h3 h3' c0 c1
  -- 1388: mov x29, sp
  refine Reach.mkC hrun hCL1 (fU_1032 hP hCL1 (KeepsFrozen_refl _)) ?_
  rw [ex_add_gpr_sp _ (by decide), z12 _ (by norm_num), pc_add]
  intro hCL2
  -- 1036: bl poly1305_update
  have hTal : T &&& 0b1111#64 = 0#64 := by rw [hT]; exact al16_sub _ 16 (by norm_num) (by norm_num) hal0
  rw [show (1024 + 4 + 4 + 4 : Nat) = 1036 from rfl]
  set r2 := upd s0.regs.regs 29#5 (T + BitVec.ofNat 64 0) with hr2
  set s1 := mkS s0 (pl.base + BitVec.ofNat 64 688)
    (upd r2 30#5 (pl.base + BitVec.ofNat 64 1036 + 4#64)) T s0.pstate m1 s0.vregs.regs with hs1
  have e0 : s1.readReg64 Reg.x0 = a := by
    simp only [hs1, hr2, ha, mkS_readGpr, readGpr_unfold, upd_apply]; simp [Reg.x0, mkS, upd_apply]
  have e1 : s1.readReg64 Reg.x1 = o := by
    simp only [hs1, hr2, ho, mkS_readGpr, readGpr_unfold, upd_apply]; simp [Reg.x1, mkS, upd_apply]
  have e2 : s1.readReg64 Reg.x2 = s0.readReg64 Reg.x2 := by
    simp only [hs1, hr2, mkS_readGpr, readGpr_unfold, upd_apply]; simp [Reg.x2, mkS, upd_apply]
  have estk : stackFrame s1 32 = memRegion (sp0 - BitVec.ofNat 64 48) 32 := by
    show memRegion (T - BitVec.ofNat 64 32) 32 = _
    rw [show T - BitVec.ofNat 64 32 = sp0 - BitVec.ofNat 64 48 by rw [hT]; bv_omega]
  have hsplit := pointsToBytes_split a st 96 (by omega)
  have hpre : m1 ⊨ updateIntSpec.pre (ro, st.take 96, inp) s1 ∗ (((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96) ∗ ((T + 8#64) ↦₆₄ s0.regs.regs 30#5) ∗
    (T ↦₆₄ s0.regs.regs 29#5) ∗ R) := by
    show m1 ⊨ (⌜(st.take 96).length = 96 ∧ StateOk ((st.take 96).take 48) ∧
        u64At (st.take 96) 64 < 16 ∧ (s1.readReg64 Reg.x2).toNat = inp.length⌝ ∗
      (s1.readReg64 Reg.x0 ↦ₛ st.take 96) ∗ bytesIn ro (s1.readReg64 Reg.x1) inp ∗ stackFrame s1 32) ∗ (((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96) ∗ ((T + 8#64) ↦₆₄ s0.regs.regs 30#5) ∗
    (T ↦₆₄ s0.regs.regs 29#5) ∗ R)
    rw [e0, e1, e2, estk, sepConj_assoc, sat_pure_sep]
    refine ⟨⟨h96, hok96, hlo96, hx2⟩, ?_⟩
    rw [hsplit] at w1
    exact Satisfies.of_eq w1
  refine call_ok updateIntSpec (update_ok ⟨hP, hG, hZ, hM, hD⟩) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) (ro, st.take 96, inp) (((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96) ∗ ((T + 8#64) ↦₆₄ s0.regs.regs 30#5) ∗
    (T ↦₆₄ s0.regs.regs 29#5) ∗ R) hrun (fU_1036 hP hCL2 (KeepsFrozen_refl _)) hTal hCL2
    hpre ?_
  intro sf hrunf hpcf hspf hkept hvf hkf hpost
  have hCL3 : (prog pl X).CodeLoaded sf.mem := codeLoaded_keepsFrozen hCL2 hkf
  change sf.mem ⊨ (⌜sf.readReg64 Reg.x0 = s1.readReg64 Reg.x0⌝ ∗
      (∃∗ st' : List (BitVec 8), ⌜Absorbs (st.take 96) inp st'⌝ ∗ (s1.readReg64 Reg.x0 ↦ₛ st')) ∗
      bytesIn ro (s1.readReg64 Reg.x1) inp ∗ stackFrame s1 32) ∗
    (((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96) ∗ ((T + 8#64) ↦₆₄ s0.regs.regs 30#5) ∗
      (T ↦₆₄ s0.regs.regs 29#5) ∗ R) at hpost
  rw [e0, e1, estk, sepConj_assoc, sat_pure_sep] at hpost
  obtain ⟨-, hpost⟩ := hpost
  rw [sepConj_assoc, sepExists_sepConj, sat_sepExists] at hpost
  obtain ⟨st', hpost⟩ := hpost
  rw [sepConj_assoc, sat_pure_sep] at hpost
  obtain ⟨habs, hpost⟩ := hpost
  have hnew : RepB (st' ++ st.drop 96) key (msg ++ inp) := repB_absorbs hrep' habs
  have hl' : st'.length = 96 := habs.1
  refine reach_congr (s' := mkS sf (pl.base + BitVec.ofNat 64 1040) sf.regs.regs T sf.pstate
    sf.mem sf.vregs.regs) (by
      rw [show pl.base + BitVec.ofNat 64 1040 = sf.pc by rw [hpcf, pc_add], ← hspf]; rfl) ?_
  -- 1040: ldp x29, x30, [sp], #16
  have hq := Satisfies.of_eq hpost (Q := (T ↦₆₄ s0.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ s0.regs.regs 30#5) ∗
    ((a ↦ₛ st') ∗ bytesIn ro o inp ∗
      memRegion (sp0 - BitVec.ofNat 64 48) 32 ∗ ((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96) ∗ R))
  have d0 := sat64_read hq
  have d1 := sat64_read (Satisfies.of_eq hq (Q := ((T + 8#64) ↦₆₄ s0.regs.regs 30#5) ∗ (T ↦₆₄ s0.regs.regs 29#5) ∗
    ((a ↦ₛ st') ∗ bytesIn ro o inp ∗
      memRegion (sp0 - BitVec.ofNat 64 48) 32 ∗ ((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96) ∗ R)))
  refine Reach.mkC hrunf hCL3 (fU_1040 hP hCL3 (KeepsFrozen_refl _)) ?_
  rw [ex_ldp64_post_sp _ _ (by decide) (by decide) _ hTal d0.2.1 d1.2.1, pc_add, d0.1, d1.1]
  intro hCL4
  -- 1044: autiasp
  refine Reach.mkC hrunf hCL4 (fU_1044 hP hCL4 (KeepsFrozen_refl _)) ?_
  rw [ex_hint, pc_add]
  intro hCL5
  -- 1048: mov w0, #0
  refine Reach.mkC hrunf hCL5 (fU_1048 hP hCL5 (KeepsFrozen_refl _)) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  intro hCL6
  -- 1052: ret
  refine Reach.mkC hrunf hCL6 (fU_1052 hP hCL6 (KeepsFrozen_refl _)) ?_
  rw [ex_ret]
  intro _
  refine Reach.done ?_
  have hS : T + 0x10#64 = sp0 := by rw [hT]; bv_omega
  left
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · simp [upd_apply, readGpr_unfold, Reg.lr]
  · exact hS
  · exact hrunf
  · exact hS
  · have k := hkept
    simp only [KeptRegs] at k
    simp (config := { decide := true }) only [CalleeSavedPreserved, readGpr_unfold, mkS_regs',
      mkS_vregs', upd_apply, ↓reduceIte, Reg.fp, hr2]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial, ?_⟩
    all_goals first
      | (rw [k _ (by decide) (by decide)]; simp (config := { decide := true }) [hr2, upd_apply])
      | exact hvf
  · simp only [mkS_mem, mkS_sp]
    rw [sepConj_assoc, sat_pure_sep]
    refine ⟨by simp [State.readReg32, upd_apply], ?_⟩
    rw [sepExists_sepConj, sepExists_sepConj, sat_sepExists]
    refine ⟨st' ++ st.drop 96, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sat_pure_sep]
    refine ⟨⟨hnew.1, hnew⟩, ?_⟩
    have hz := pointsToBytes_append a st' (st.drop 96)
    rw [hl'] at hz
    have hm := Satisfies.of_eq hq (Q := ((T ↦₆₄ s0.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ s0.regs.regs 30#5)) ∗
      (((a ↦ₛ st') ∗ ((a + BitVec.ofNat 64 96) ↦ₛ st.drop 96)) ∗
        bytesIn ro o inp ∗ memRegion (sp0 - BitVec.ofNat 64 48) 32 ∗ R))
    have hm2 := sat_sep_mono hm (cells_entails_memRegion T _ _)
    rw [← hz] at hm2
    have hm3 := Satisfies.of_eq hm2 (Q := (memRegion (sp0 - BitVec.ofNat 64 48) 32 ∗ memRegion T 16) ∗
      ((a ↦ₛ (st' ++ st.drop 96)) ∗ bytesIn ro o inp ∗ R))
    have hm4 := sat_sep_mono hm3 (memRegion_merge _ T 32 16 eT.symm (by norm_num) (by norm_num))
    have es : T + 0x10#64 - BitVec.ofNat 64 48 = sp0 - BitVec.ofNat 64 48 := by rw [hS]
    simp only [stackFrame, mkS_sp, es]
    exact Satisfies.of_eq hm4

end Poly1305DebianApi.Donna

end
end

section
section
namespace Poly1305DebianApi.Donna.Stream

theorem internalOk_donna_init_update_final_dev :
    ∃ Rep : Poly1305Libsodium.StateRep, donnaInitOk Rep ∧ donnaUpdateOk Rep ∧ donnaFinalOk Rep :=
  ⟨Rep, init_dev (fun h hr => repB_of_repP h hr), update_dev, final_dev finishTag_rep⟩

end Poly1305DebianApi.Donna.Stream

end
end

section
open Poly1305DebianApi

theorem solution :
    ∃ Rep : Poly1305Libsodium.StateRep,
      internalOk "crypto_onetimeauth_poly1305_donna_init [libsodium_la_poly1305_donna]"
          (fun _ => initSpec Rep) ∧
        internalOk "crypto_onetimeauth_poly1305_donna_update [libsodium_la_poly1305_donna]"
          (fun _ => updateSpec Rep) ∧
        internalOk "crypto_onetimeauth_poly1305_donna_final [libsodium_la_poly1305_donna]"
          (fun _ => finalSpec Rep) := by
  apply Poly1305DebianApi.Donna.Stream.internalOk_donna_init_update_final_dev <;> assumption

end
