-- Prove2me | solution 1 for X25519Dalek.differentialAddAndDouble_724_752
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T20:37:28.354799+00:00
-- url     : https://prove2.me/submissions/e1eceacb-e90e-4ebd-80ec-482b812a7f06

import Definitions.Def_X25519Dalek_PlacedObj
import Definitions.Def_X25519Dalek_Rfc7748
import Definitions.Def_X25519Dalek_Spec
import Theorems.Thm_X25519Dalek_steps_keepsFrozen
import Theorems.Thm_X25519Dalek_fnOk_fe51_mul
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
theorem holds_sepExists_iff {α : Sort _} {P : α → SepProp} {h : Heap} :
    (sepExists P).holds h ↔ ∃ x, (P x).holds h := Iff.rfl
end SepProp

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

end Heap

/-! ## Memory facts about `write8` -/

namespace Memory

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

end Memory

namespace Heap

end Heap

/-! ## Byte slices as heaps -/

/-! ## Satisfaction-level reads and writes -/

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

/-! ## Byte-slice heaps carry no ghost state and nothing outside the slice -/

end Arm64

end
end

section
section
/-! # 64-bit cells and byte reads: values and permissions from ownership -/

set_option autoImplicit false

namespace Arm64

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

theorem sat_pre4 {m : Memory} {φ : Prop} {A B C D F : SepProp} (hφ : φ) (hs : m ⊨ A ∗ B ∗ C ∗ D ∗ F) :
    m ⊨ (⌜φ⌝ ∗ A ∗ B ∗ C ∗ D) ∗ F := by
  rw [sepConj_assoc, sat_pure_sep]; exact ⟨hφ, by simpa only [sepConj_assoc] using hs⟩

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

theorem y_addi_sp {d : BitVec 5} {k : BitVec 12} (hd : d ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD (.gpr d) .sp k false))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (sp + k.setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, BitVec.truncate_eq_setWidth]
  exact h

theorem y_subi_r {d a : BitVec 5} {k : BitVec 12} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUB (.gpr d) (.gpr a) k false))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r a - k.setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, BitVec.truncate_eq_setWidth]
  exact h

end

theorem pc4 (b : BitVec 64) (k l : Nat) (h : k + 4 = l) :
    b + BitVec.ofNat 64 k + 4#64 = b + BitVec.ofNat 64 l := by
  subst h; rw [BitVec.add_assoc, BitVec.ofNat_add]

section
variable {p : Program} {s0 : State} {pc pc' : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

end

section
variable {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

end

section
variable {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

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

abbrev callee12_0 : String := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul"

theorem blk12 : blk 12 = x25519CliBlk12 := rfl

theorem len12 : x25519CliBlk12.code.length = 952 := by decide +kernel

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (j : Nat) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem c12_724 : (bprog mpl j).fetchMem m (mpl.base 12 + 724#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x1d#5) 0x0d0#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 724) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x1d#5) 0x0d0#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_728 : (bprog mpl j).fetchMem m (mpl.base 12 + 728#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.sp) 0x0f8#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 728) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.sp) 0x0f8#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_736 : (bprog mpl j).fetchMem m (mpl.base 12 + 736#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x1d#5) 0x0a8#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 736) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x1d#5) 0x0a8#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_740 : (bprog mpl j).fetchMem m (mpl.base 12 + 740#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x0a8#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 740) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x0a8#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_744 : (bprog mpl j).fetchMem m (mpl.base 12 + 744#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.sp) 0x0d0#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 744) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.sp) 0x0d0#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_732 {j' offj : Nat} (hlk : lookupBlockSym callee12_0 x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 12 + 732#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 12 + BitVec.ofNat 64 732))) :=
  fetch_bl hP hCL (i := 12) (by decide) j (off := 732) (name := callee12_0) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c12_748 {j' offj : Nat} (hlk : lookupBlockSym callee12_0 x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 12 + 748#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 12 + BitVec.ofNat 64 748))) :=
  fetch_bl hP hCL (i := 12) (by decide) j (off := 748) (name := callee12_0) (by decide +kernel)
    (by decide +kernel) hlk hk

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

abbrev mulName : String :=
  "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul"

theorem lk_mul : lookupBlockSym mulName x25519CliMultiLib.blocks = some (1, 0) := by decide +kernel

/-- Callee-saved registers (`x19`–`x29`) from `r`, the rest from `rf`. -/
def csMerge (r rf : BitVec 5 → BitVec 64) : BitVec 5 → BitVec 64 :=
  fun k => if 19 ≤ k.toNat ∧ k.toNat ≤ 29 then r k else rf k

theorem csMerge_eq {sf : State} {r : BitVec 5 → BitVec 64} (h : CSRegs sf r) :
    csMerge r sf.regs.regs = sf.regs.regs := by
  funext k
  unfold csMerge
  split_ifs with hk
  · obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29⟩ := h
    have e : k = BitVec.ofNat 5 k.toNat := by simp
    generalize hj : k.toNat = j at e hk
    subst e
    obtain ⟨h1, h2⟩ := hk
    interval_cases j
    all_goals first | exact c19.symm | exact c20.symm | exact c21.symm | exact c22.symm | exact c23.symm | exact c24.symm | exact c25.symm | exact c26.symm | exact c27.symm | exact c28.symm | exact c29.symm
  · rfl

/-- `bl` to the entry of block `j`. -/
theorem y_bl {p : Program} {s0 : State} {pc T : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
    {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}
    (hrun : s0.status = .Running) (hf : p.fetchMem m pc = some (.bl (T - pc)))
    (h : Reach p (mkS s0 T (upd r 30#5 (pc + 4#64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', BitVec.add_sub_cancel]
  exact h

theorem cs_of_upd30 {sf : State} {r : BitVec 5 → BitVec 64} {x : BitVec 64}
    (h : CSRegs sf (upd r 30#5 x)) : CSRegs sf r := by
  simpa only [CSRegs, upd_apply, BitVec.reduceEq, ite_false] using h

theorem sat_words3 {m : Memory} {a b o sp : BitVec 64} {A B O : List (BitVec 64)} {F : SepProp}
    (hs : m ⊨ ((a ↦₆₄* A) ∗ (b ↦₆₄* B) ∗ (o ↦₆₄* O) ∗ memRegion (sp - 224#64) 224) ∗ F) :
    m ⊨ (a ↦ₛ A.flatMap unpack64) ∗ (b ↦ₛ B.flatMap unpack64) ∗ (o ↦ₛ O.flatMap unpack64) ∗
      memRegion (sp - 224#64) 224 ∗ F := by
  simp only [words_eq_bytes, sepConj_assoc] at hs; exact hs

/-- A call to `mul` (block 1) with the operands and the output as five-word lists. -/
theorem call_mul_w {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {s0 : State} {pc pcr : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {out a b : BitVec 64} {A B O : List (BitVec 64)} {F : SepProp}
    (hrun : s0.status = .Running) (kf : m0.KeepsFrozen m) (hal : (sp &&& 15#64) = 0#64)
    (hf : (bprog mpl k).fetchMem m pc = some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - pc)))
    (hpcr : pc + 4#64 = pcr) (h8 : r 8#5 = out) (h0 : r 0#5 = a) (h1 : r 1#5 = b)
    (hs : m ⊨ ((a ↦₆₄* A) ∗ (b ↦₆₄* B) ∗ (out ↦₆₄* O) ∗ memRegion (sp - 224#64) 224) ∗ F)
    (hA : fe51LimbsBounded (A.flatMap unpack64) (2 ^ 54))
    (hB : fe51LimbsBounded (B.flatMap unpack64) (2 ^ 54)) (hO : O.length = 5)
    (hcont : ∀ (sf : State) (R : List (BitVec 64)), sf.status = .Running → m0.KeepsFrozen sf.mem →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ → R.length = 5 →
      fe51LimbsBounded (R.flatMap unpack64) (2 ^ 52) →
      fe51ValOfBytes (R.flatMap unpack64) % p25519 =
        fe51ValOfBytes (A.flatMap unpack64) * fe51ValOfBytes (B.flatMap unpack64) % p25519 →
      (sf.mem ⊨ ((a ↦₆₄* A) ∗ (b ↦₆₄* B) ∗ (out ↦₆₄* R) ∗ memRegion (sp - 224#64) 224) ∗ F) →
      Reach (bprog mpl k) (mkS sf pcr (csMerge r sf.regs.regs) sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl k) (mkS s0 pc r sp ps m v) Q := by
  refine y_bl hrun hf ?_
  have hO' : (O.flatMap unpack64).length = 40 := by rw [flatMap_unpack64_length, hO]
  have hpre := sat_pre4 (φ := (mkS s0 (mpl.base 1 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64)) sp ps m v).readReg64 Reg.x8 = out ∧
      (mkS s0 (mpl.base 1 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64)) sp ps m v).readReg64 Reg.x0 = a ∧
      (mkS s0 (mpl.base 1 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64)) sp ps m v).readReg64 Reg.x1 = b ∧
      (O.flatMap unpack64).length = 40 ∧ fe51LimbsBounded (A.flatMap unpack64) (2 ^ 54) ∧
      fe51LimbsBounded (B.flatMap unpack64) (2 ^ 54))
    ⟨by simp [h8], by simp [h0], by simp [h1], hO', hA, hB⟩ (sat_words3 hs)
  refine Reach.callS hP k fnOk_fe51_mul.1 lk_mul (by decide)
    (out, a, b, O.flatMap unpack64, A.flatMap unpack64, B.flatMap unpack64) F rfl hrun hal
    (libCodeLoaded_keepsFrozen hCL kf) hpre ?_ ?_ ?_ ?_
  · intro sf; exact not_sat_false
  · intro c sf; exact not_sat_false
  · intro sf; exact not_sat_false
  intro sf hrunf hspf hcs hv hpost hkf
  simp only [ToBaseSpec.toSpec, stackFrame, mkS_sp, hspf] at hpost
  simp only [sepConj_assoc] at hpost
  simp only [sepConj_left_comm _ (sepExists _)] at hpost
  rw [sepExists_sepConj, sat_sepExists] at hpost
  obtain ⟨res, hpost⟩ := hpost
  simp only [sepConj_assoc] at hpost
  simp only [sepConj_left_comm _ (SepProp.pure _)] at hpost
  rw [sat_pure_sep] at hpost
  obtain ⟨⟨hrb, hrv⟩, hpost⟩ := hpost
  have hrl : res.length = 40 := hrb.1
  have e30 : upd r 30#5 (pc + 4#64) 30#5 = pcr := by rw [upd_same, hpcr]
  rw [e30, ← csMerge_eq (cs_of_upd30 hcs)]
  have hflat := chunks64_flat 5 res (by rw [hrl])
  refine hcont sf (chunks64 res 5) hrunf (kf.trans hkf) hv (chunks64_length res 5) (by rw [hflat]; exact hrb)
    (by rw [hflat]; exact hrv) ?_
  rw [← hflat] at hpost
  simp only [words_eq_bytes, sepConj_assoc]
  exact Satisfies.of_eq hpost (by ac_rfl)

theorem sat_words_ro {m : Memory} {a b o sp : BitVec 64} {A : List (BitVec 8)} {B O : List (BitVec 64)}
    {F : SepProp}
    (hs : m ⊨ ((a ↦ᵣ A) ∗ (b ↦₆₄* B) ∗ (o ↦₆₄* O) ∗ memRegion (sp - 224#64) 224) ∗ F) :
    m ⊨ (a ↦ᵣ A) ∗ (b ↦ₛ B.flatMap unpack64) ∗ (o ↦ₛ O.flatMap unpack64) ∗
      memRegion (sp - 224#64) 224 ∗ F := by
  simp only [words_eq_bytes, sepConj_assoc] at hs; exact hs

/-- A call to `mul` with a read-only left operand given as bytes (`fe51MulRoLeftSpec`). -/
theorem call_mulro_w {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {s0 : State} {pc pcr : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {out a b : BitVec 64} {A : List (BitVec 8)} {B O : List (BitVec 64)} {F : SepProp}
    (hrun : s0.status = .Running) (kf : m0.KeepsFrozen m) (hal : (sp &&& 15#64) = 0#64)
    (hf : (bprog mpl k).fetchMem m pc = some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - pc)))
    (hpcr : pc + 4#64 = pcr) (h8 : r 8#5 = out) (h0 : r 0#5 = a) (h1 : r 1#5 = b)
    (hs : m ⊨ ((a ↦ᵣ A) ∗ (b ↦₆₄* B) ∗ (out ↦₆₄* O) ∗ memRegion (sp - 224#64) 224) ∗ F)
    (hA : fe51LimbsBounded A (2 ^ 54))
    (hB : fe51LimbsBounded (B.flatMap unpack64) (2 ^ 54)) (hO : O.length = 5)
    (hcont : ∀ (sf : State) (R : List (BitVec 64)), sf.status = .Running → m0.KeepsFrozen sf.mem →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ → R.length = 5 →
      fe51LimbsBounded (R.flatMap unpack64) (2 ^ 52) →
      fe51ValOfBytes (R.flatMap unpack64) % p25519 =
        fe51ValOfBytes A * fe51ValOfBytes (B.flatMap unpack64) % p25519 →
      (sf.mem ⊨ ((a ↦ᵣ A) ∗ (b ↦₆₄* B) ∗ (out ↦₆₄* R) ∗ memRegion (sp - 224#64) 224) ∗ F) →
      Reach (bprog mpl k) (mkS sf pcr (csMerge r sf.regs.regs) sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl k) (mkS s0 pc r sp ps m v) Q := by
  refine y_bl hrun hf ?_
  have hO' : (O.flatMap unpack64).length = 40 := by rw [flatMap_unpack64_length, hO]
  have hpre := sat_pre4 (φ := (mkS s0 (mpl.base 1 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64)) sp ps m v).readReg64 Reg.x8 = out ∧
      (mkS s0 (mpl.base 1 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64)) sp ps m v).readReg64 Reg.x0 = a ∧
      (mkS s0 (mpl.base 1 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64)) sp ps m v).readReg64 Reg.x1 = b ∧
      (O.flatMap unpack64).length = 40 ∧ fe51LimbsBounded A (2 ^ 54) ∧
      fe51LimbsBounded (B.flatMap unpack64) (2 ^ 54))
    ⟨by simp [h8], by simp [h0], by simp [h1], hO', hA, hB⟩ (sat_words_ro hs)
  refine Reach.callS hP k fnOk_fe51_mul.2.2 lk_mul (by decide)
    (out, a, b, O.flatMap unpack64, A, B.flatMap unpack64) F rfl hrun hal
    (libCodeLoaded_keepsFrozen hCL kf) hpre ?_ ?_ ?_ ?_
  · intro sf; exact not_sat_false
  · intro c sf; exact not_sat_false
  · intro sf; exact not_sat_false
  intro sf hrunf hspf hcs hv hpost hkf
  simp only [ToBaseSpec.toSpec, stackFrame, mkS_sp, hspf] at hpost
  simp only [sepConj_assoc] at hpost
  simp only [sepConj_left_comm _ (sepExists _)] at hpost
  rw [sepExists_sepConj, sat_sepExists] at hpost
  obtain ⟨res, hpost⟩ := hpost
  simp only [sepConj_assoc] at hpost
  simp only [sepConj_left_comm _ (SepProp.pure _)] at hpost
  rw [sat_pure_sep] at hpost
  obtain ⟨⟨hrb, hrv⟩, hpost⟩ := hpost
  have hrl : res.length = 40 := hrb.1
  have e30 : upd r 30#5 (pc + 4#64) 30#5 = pcr := by rw [upd_same, hpcr]
  rw [e30, ← csMerge_eq (cs_of_upd30 hcs)]
  have hflat := chunks64_flat 5 res (by rw [hrl])
  refine hcont sf (chunks64 res 5) hrunf (kf.trans hkf) hv (chunks64_length res 5) (by rw [hflat]; exact hrb)
    (by rw [hflat]; exact hrv) ?_
  rw [← hflat] at hpost
  simp only [words_eq_bytes, sepConj_assoc]
  exact Satisfies.of_eq hpost (by ac_rfl)

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

theorem aSk (S : BitVec 64) (a c : Nat) (k : BitVec 12)
    (h : BitVec.ofNat 64 a - k.setWidth 64 = BitVec.ofNat 64 c) :
    S - BitVec.ofNat 64 a + k.setWidth 64 = S - BitVec.ofNat 64 c := by
  rw [← h]; try abel

theorem aSmk (S : BitVec 64) (a c : Nat) (k : BitVec 12)
    (h : BitVec.ofNat 64 a + k.setWidth 64 = BitVec.ofNat 64 c) :
    S - BitVec.ofNat 64 a - k.setWidth 64 = S - BitVec.ofNat 64 c := by
  rw [← h]; try abel

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

theorem x_subi_r2 {d a : BitVec 5} {k : BitVec 12} {y x : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUB (.gpr d) (.gpr a) k false))
    (hpc : pc + 4#64 = pc') (ey : r a = y) (hx : y - k.setWidth 64 = x)
    (h : Reach p (mkS s0 pc' (upd r d x) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ey hx; exact y_subi_r hd ha hrun hf h

end


theorem reach_reg {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
    {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop} {i : BitVec 5} {x : BitVec 64}
    (h : r i = x) (hr : Reach p (mkS s0 pc (upd r i x) sp ps m v) Q) : Reach p (mkS s0 pc r sp ps m v) Q := by
  have e : upd r i x = r := by
    funext k; simp only [upd]; split_ifs with hk
    · subst hk; exact h.symm
    · rfl
  rwa [e] at hr


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

theorem pick3 (A1 A2 A3 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ R) = (A3 ∗ A1 ∗ A2 ∗ R) := by ac_rfl
theorem pick4 (A1 A2 A3 A4 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ R) = (A4 ∗ A1 ∗ A2 ∗ A3 ∗ R) := by ac_rfl
theorem pick13 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ R) = (A13 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ R) := by ac_rfl
theorem pick17 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ R) = (A17 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ R) := by ac_rfl
theorem pick19 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ R) = (A19 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ R) := by ac_rfl
theorem pick21 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ R) = (A21 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ R) := by ac_rfl
theorem pick26 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ A26 ∗ R) = (A26 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ R) := by ac_rfl
theorem group4 (A B C D F : SepProp) : (A ∗ B ∗ C ∗ D ∗ F) = ((A ∗ B ∗ C ∗ D) ∗ F) := by ac_rfl

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

theorem fe51LimbsBounded_mono {bs : List (BitVec 8)} {b1 b2 : Nat} (h : fe51LimbsBounded bs b1)
    (hb : b1 ≤ b2) : fe51LimbsBounded bs b2 := by
  obtain ⟨hl, h0, h1, h2, h3, h4⟩ := h
  exact ⟨hl, by omega, by omega, by omega, by omega, by omega⟩

/-! ## Field arithmetic -/

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem list5 {α : Type} (l : List α) (h : l.length = 5) : ∃ a b c d e, l = [a, b, c, d, e] := by
  match l, h with
  | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩

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
theorem d12_s8 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
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
    {v : BitVec 5 → BitVec 128} {t632 t644 t660 t676 t680 o166 o167 o168 o169 o170 t560 t564 t584 t588 t616 o151 o152 o153 o154 o155 o118 o119 o120 o121 o122 o103 o104 o105 o106 o107 t144 t164 t172 t180 t188 t232 t228 t248 t256 t276 t76 t96 t100 t120 t68 t316 t328 t324 t336 t348 t452 t476 t488 t492 t484 o64 o65 o66 o67 o68 o79 o80 o81 o82 o83 a24e_0 a24e_1 a24e_2 a24e_3 a24e_4 u2_0 u2_1 u2_2 u2_3 u2_4 a24epbb_0 a24epbb_1 a24epbb_2 a24epbb_3 a24epbb_4 w2_0 w2_1 w2_2 w2_3 w2_4 w3_0 w3_1 w3_2 w3_3 w3_4 g1 : BitVec 64}
    (hrun : sb.status = .Running) (kf : m0.KeepsFrozen m) (hvs : VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩) (hr0 : r 0#5 = (mpl.ρ symA24)) (hr19 : r 19#5 = Qb) (hr20 : r 20#5 = Pb) (hr21 : r 21#5 = o80) (hr22 : r 22#5 = 0x007ffffffffffff0#64) (hr23 : r 23#5 = o79) (hr24 : r 24#5 = 36028797018963664#64) (hr25 : r 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64)) (hr26 : r 26#5 = o83) (hr27 : r 27#5 = o82) (hr28 : r 28#5 = o81) (hr29 : r 29#5 = (S - 96#64)) (bd_Diff : fe51LimbsBounded ([t632, t644, t660, t676, t680].flatMap unpack64) (2 ^ 52)) (bd_Tmp : fe51LimbsBounded ([o166, o167, o168, o169, o170].flatMap unpack64) (2 ^ 52)) (bd_Sum : fe51LimbsBounded ([t560, t564, t584, t588, t616].flatMap unpack64) (2 ^ 53)) (bd_U3 : fe51LimbsBounded ([o151, o152, o153, o154, o155].flatMap unpack64) (2 ^ 52)) (bd_CB : fe51LimbsBounded ([o118, o119, o120, o121, o122].flatMap unpack64) (2 ^ 52)) (bd_DA : fe51LimbsBounded ([o103, o104, o105, o106, o107].flatMap unpack64) (2 ^ 52)) (bd_B : fe51LimbsBounded ([t144, t164, t172, t180, t188].flatMap unpack64) (2 ^ 52)) (bd_C : fe51LimbsBounded ([t232, t228, t248, t256, t276].flatMap unpack64) (2 ^ 54)) (bd_A : fe51LimbsBounded ([t76, t96, t100, t120, t68].flatMap unpack64) (2 ^ 54)) (bd_D : fe51LimbsBounded ([t316, t328, t324, t336, t348].flatMap unpack64) (2 ^ 52)) (bd_E : fe51LimbsBounded ([t452, t476, t488, t492, t484].flatMap unpack64) (2 ^ 52)) (bd_AA : fe51LimbsBounded ([o64, o65, o66, o67, o68].flatMap unpack64) (2 ^ 52)) (bd_BB : fe51LimbsBounded ([o79, o80, o81, o82, o83].flatMap unpack64) (2 ^ 52)) (hs : m ⊨ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F)
    (hcont : ∀ (sb : State) (r : BitVec 5 → BitVec 64) (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128) (o196 o197 o198 o199 o200 o181 o182 o183 o184 o185 : BitVec 64), (sb.status = .Running) → (m0.KeepsFrozen m) → (VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩) → (r 19#5 = Qb) → (r 20#5 = Pb) → (r 21#5 = o80) → (r 22#5 = 0x007ffffffffffff0#64) → (r 23#5 = o79) → (r 24#5 = 36028797018963664#64) → (r 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64)) → (r 26#5 = o83) → (r 27#5 = o82) → (r 28#5 = o81) → (r 29#5 = (S - 96#64)) → (fe51LimbsBounded ([o64, o65, o66, o67, o68].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o79, o80, o81, o82, o83].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o196, o197, o198, o199, o200].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([t452, t476, t488, t492, t484].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o181, o182, o183, o184, o185].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([t632, t644, t660, t676, t680].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o166, o167, o168, o169, o170].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([t560, t564, t584, t588, t616].flatMap unpack64) (2 ^ 53)) → (fe51LimbsBounded ([o151, o152, o153, o154, o155].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o118, o119, o120, o121, o122].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o103, o104, o105, o106, o107].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([t144, t164, t172, t180, t188].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([t232, t228, t248, t256, t276].flatMap unpack64) (2 ^ 54)) → (fe51LimbsBounded ([t76, t96, t100, t120, t68].flatMap unpack64) (2 ^ 54)) → (fe51LimbsBounded ([t316, t328, t324, t336, t348].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([o181, o182, o183, o184, o185].flatMap unpack64) (2 ^ 52)) → (fe51ValOfBytes ([o181, o182, o183, o184, o185].flatMap unpack64) % p25519 = fe51ValOfBytes fe51MontA24Bytes * fe51ValOfBytes ([t452, t476, t488, t492, t484].flatMap unpack64) % p25519) → (fe51LimbsBounded ([o196, o197, o198, o199, o200].flatMap unpack64) (2 ^ 52)) → (fe51ValOfBytes ([o196, o197, o198, o199, o200].flatMap unpack64) % p25519 = fe51ValOfBytes ([o64, o65, o66, o67, o68].flatMap unpack64) * fe51ValOfBytes ([o79, o80, o81, o82, o83].flatMap unpack64) % p25519) → (m ⊨ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ F) → Reach (bprog mpl 12) (mkS sb (mpl.base 12 + BitVec.ofNat 64 752) r (S - 832#64) ps m v) Q) :
    Reach (bprog mpl 12) (mkS sb (mpl.base 12 + BitVec.ofNat 64 724) r (S - 832#64) ps m v) Q := by
  refine reach_reg (i := 0#5) hr0 ?_
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
  refine x_subi_r2 (d := 8#5) (a := 29#5) (by decide) (by decide) hrun (c12_724 hP hCL 12 kf) (pc4 _ 724 728 rfl) rfl (aSmk S 96 304 _ (by decide)) ?_
  refine x_addi_sp2 (d := 1#5) (by decide) hrun (c12_728 hP hCL 12 kf) (pc4 _ 728 732 rfl) (aSk S 832 584 _ (by decide)) ?_
  rw [pick3] at hs
  rw [pick19] at hs
  rw [pick13] at hs
  rw [pick26] at hs
  rw [group4] at hs
  have lb_a24 : fe51LimbsBounded fe51MontA24Bytes (2 ^ 54) := by unfold fe51LimbsBounded; decide +kernel
  have lb_E : fe51LimbsBounded ([t452, t476, t488, t492, t484].flatMap unpack64) (2 ^ 54) := fe51LimbsBounded_mono (b2 := 2 ^ 54) bd_E (by norm_num)
  refine call_mulro_w hP 12 hCL hrun kf (aligned_sub hal 832 (by decide) (by decide)) (c12_732 hP hCL 12 kf lk_mul) (pc4 _ 732 736 rfl) rfl rfl rfl hs lb_a24 lb_E (by rfl) (fun sf172 R173 hrun174 kf175 hv176 hl177 hb178 hval179 hs180 => ?_)
  obtain ⟨o181, o182, o183, o184, o185, rfl⟩ := list5 R173 hl177
  have hvs186 : VRegFile.calleeSaved ⟨sf172.vregs.regs⟩ = VRegFile.calleeSaved ⟨vo⟩ := hv176.trans hvs
  rw [← group4] at hs180
  have lb_A24E := fe51LimbsBounded_mono (b2 := 2 ^ 54) hb178 (by norm_num)
  clear hs kf
  refine x_subi_r2 (d := 8#5) (a := 29#5) (by decide) (by decide) hrun174 (c12_736 hP hCL 12 kf175) (pc4 _ 736 740 rfl) rfl (aSmk S 96 264 _ (by decide)) ?_
  refine x_addi_sp2 (d := 0#5) (by decide) hrun174 (c12_740 hP hCL 12 kf175) (pc4 _ 740 744 rfl) (aSk S 832 664 _ (by decide)) ?_
  refine x_addi_sp2 (d := 1#5) (by decide) hrun174 (c12_744 hP hCL 12 kf175) (pc4 _ 744 748 rfl) (aSk S 832 624 _ (by decide)) ?_
  rw [pick4] at hs180
  rw [pick21] at hs180
  rw [pick17] at hs180
  rw [pick17] at hs180
  rw [group4] at hs180
  have lb_AA : fe51LimbsBounded ([o64, o65, o66, o67, o68].flatMap unpack64) (2 ^ 54) := fe51LimbsBounded_mono (b2 := 2 ^ 54) bd_AA (by norm_num)
  have lb_BB : fe51LimbsBounded ([o79, o80, o81, o82, o83].flatMap unpack64) (2 ^ 54) := fe51LimbsBounded_mono (b2 := 2 ^ 54) bd_BB (by norm_num)
  refine call_mul_w hP 12 hCL hrun174 kf175 (aligned_sub hal 832 (by decide) (by decide)) (c12_748 hP hCL 12 kf175 lk_mul) (pc4 _ 748 752 rfl) rfl rfl rfl hs180 lb_AA lb_BB (by rfl) (fun sf187 R188 hrun189 kf190 hv191 hl192 hb193 hval194 hs195 => ?_)
  obtain ⟨o196, o197, o198, o199, o200, rfl⟩ := list5 R188 hl192
  have hvs201 : VRegFile.calleeSaved ⟨sf187.vregs.regs⟩ = VRegFile.calleeSaved ⟨vo⟩ := hv191.trans hvs186
  rw [← group4] at hs195
  have lb_U2 := fe51LimbsBounded_mono (b2 := 2 ^ 54) hb193 (by norm_num)
  clear hs180 kf175 hrun174
  exact hcont _ _ _ _ _ o196 o197 o198 o199 o200 o181 o182 o183 o184 o185 hrun189 kf190 hvs201 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl bd_AA bd_BB hb193 bd_E hb178 bd_Diff bd_Tmp bd_Sum bd_U3 bd_CB bd_DA bd_B bd_C bd_A bd_D hb178 hval179 hb193 hval194 hs195


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
theorem differentialAddAndDouble_724_752_dev {mpl : Arm64.Obj.MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S Pb Qb u1 : BitVec 64} {F : Arm64.SepProp}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 uw0 uw1 uw2 uw3 uw4 : BitVec 64}
    {c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 : BitVec 64}
    {t632 t644 t660 t676 t680 o166 o167 o168 o169 o170 t560 t564 t584 t588 t616 o151 o152 o153 o154 o155 o118 o119 o120 o121 o122 o103 o104 o105 o106 o107 t144 t164 t172 t180 t188 t232 t228 t248 t256 t276 t76 t96 t100 t120 t68 t316 t328 t324 t336 t348 t452 t476 t488 t492 t484 o64 o65 o66 o67 o68 o79 o80 o81 o82 o83 a24e_0 a24e_1 a24e_2 a24e_3 a24e_4 u2_0 u2_1 u2_2 u2_3 u2_4 a24epbb_0 a24epbb_1 a24epbb_2 a24epbb_3 a24epbb_4 w2_0 w2_1 w2_2 w2_3 w2_4 w3_0 w3_1 w3_2 w3_3 w3_4 g1 : BitVec 64}
    (hal : (S &&& 15#64 == 0#64) = true)
    (hPU : p0.toNat < 9007199254740992 ∧ p1.toNat < 9007199254740992 ∧ p2.toNat < 9007199254740992 ∧ p3.toNat < 9007199254740992 ∧ p4.toNat < 9007199254740992)
    (hPW : p5.toNat < 9007199254740992 ∧ p6.toNat < 9007199254740992 ∧ p7.toNat < 9007199254740992 ∧ p8.toNat < 9007199254740992 ∧ p9.toNat < 9007199254740992)
    (hQU : q0.toNat < 9007199254740992 ∧ q1.toNat < 9007199254740992 ∧ q2.toNat < 9007199254740992 ∧ q3.toNat < 9007199254740992 ∧ q4.toNat < 9007199254740992)
    (hQW : q5.toNat < 9007199254740992 ∧ q6.toNat < 9007199254740992 ∧ q7.toNat < 9007199254740992 ∧ q8.toNat < 9007199254740992 ∧ q9.toNat < 9007199254740992)
    (hU1 : uw0.toNat < 18014398509481984 ∧ uw1.toNat < 18014398509481984 ∧ uw2.toNat < 18014398509481984 ∧ uw3.toNat < 18014398509481984 ∧ uw4.toNat < 18014398509481984)
    (hrun : s.status = Arm64.ExecStatus.Running) (hpc : s.pc = mpl.base 12 + BitVec.ofNat 64 724) (hsp : s.sp = S - 832#64)
    (hr0 : s.regs.regs 0#5 = (fe51_mont_a24 mpl))
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
    (bd_Diff : (t632.toNat < 4503599627370496 ∧ t644.toNat < 4503599627370496 ∧ t660.toNat < 4503599627370496 ∧ t676.toNat < 4503599627370496 ∧ t680.toNat < 4503599627370496))
    (bd_Tmp : (o166.toNat < 4503599627370496 ∧ o167.toNat < 4503599627370496 ∧ o168.toNat < 4503599627370496 ∧ o169.toNat < 4503599627370496 ∧ o170.toNat < 4503599627370496))
    (bd_Sum : (t560.toNat < 9007199254740992 ∧ t564.toNat < 9007199254740992 ∧ t584.toNat < 9007199254740992 ∧ t588.toNat < 9007199254740992 ∧ t616.toNat < 9007199254740992))
    (bd_U3 : (o151.toNat < 4503599627370496 ∧ o152.toNat < 4503599627370496 ∧ o153.toNat < 4503599627370496 ∧ o154.toNat < 4503599627370496 ∧ o155.toNat < 4503599627370496))
    (bd_CB : (o118.toNat < 4503599627370496 ∧ o119.toNat < 4503599627370496 ∧ o120.toNat < 4503599627370496 ∧ o121.toNat < 4503599627370496 ∧ o122.toNat < 4503599627370496))
    (bd_DA : (o103.toNat < 4503599627370496 ∧ o104.toNat < 4503599627370496 ∧ o105.toNat < 4503599627370496 ∧ o106.toNat < 4503599627370496 ∧ o107.toNat < 4503599627370496))
    (bd_B : (t144.toNat < 4503599627370496 ∧ t164.toNat < 4503599627370496 ∧ t172.toNat < 4503599627370496 ∧ t180.toNat < 4503599627370496 ∧ t188.toNat < 4503599627370496))
    (bd_C : (t232.toNat < 18014398509481984 ∧ t228.toNat < 18014398509481984 ∧ t248.toNat < 18014398509481984 ∧ t256.toNat < 18014398509481984 ∧ t276.toNat < 18014398509481984))
    (bd_A : (t76.toNat < 18014398509481984 ∧ t96.toNat < 18014398509481984 ∧ t100.toNat < 18014398509481984 ∧ t120.toNat < 18014398509481984 ∧ t68.toNat < 18014398509481984))
    (bd_D : (t316.toNat < 4503599627370496 ∧ t328.toNat < 4503599627370496 ∧ t324.toNat < 4503599627370496 ∧ t336.toNat < 4503599627370496 ∧ t348.toNat < 4503599627370496))
    (bd_E : (t452.toNat < 4503599627370496 ∧ t476.toNat < 4503599627370496 ∧ t488.toNat < 4503599627370496 ∧ t492.toNat < 4503599627370496 ∧ t484.toNat < 4503599627370496))
    (bd_AA : (o64.toNat < 4503599627370496 ∧ o65.toNat < 4503599627370496 ∧ o66.toNat < 4503599627370496 ∧ o67.toNat < 4503599627370496 ∧ o68.toNat < 4503599627370496))
    (bd_BB : (o79.toNat < 4503599627370496 ∧ o80.toNat < 4503599627370496 ∧ o81.toNat < 4503599627370496 ∧ o82.toNat < 4503599627370496 ∧ o83.toNat < 4503599627370496))
    (hs : s.mem ⊨ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F) :
    ∃ sf, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 12) s sf ∧
      sf.status = Arm64.ExecStatus.Running ∧
      sf.pc = mpl.base 12 + BitVec.ofNat 64 752 ∧
      sf.sp = S - 832#64 ∧
      Arm64.VRegFile.calleeSaved sf.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ o196 o197 o198 o199 o200 o181 o182 o183 o184 o185 : BitVec 64,
        sf.regs.regs 19#5 = Qb ∧
        sf.regs.regs 20#5 = Pb ∧
        sf.regs.regs 21#5 = o80 ∧
        sf.regs.regs 22#5 = 0x007ffffffffffff0#64 ∧
        sf.regs.regs 23#5 = o79 ∧
        sf.regs.regs 24#5 = 36028797018963664#64 ∧
        sf.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) ∧
        sf.regs.regs 26#5 = o83 ∧
        sf.regs.regs 27#5 = o82 ∧
        sf.regs.regs 28#5 = o81 ∧
        sf.regs.regs 29#5 = (S - 96#64) ∧
        ((o64.toNat < 4503599627370496 ∧ o65.toNat < 4503599627370496 ∧ o66.toNat < 4503599627370496 ∧ o67.toNat < 4503599627370496 ∧ o68.toNat < 4503599627370496)) ∧
        ((o79.toNat < 4503599627370496 ∧ o80.toNat < 4503599627370496 ∧ o81.toNat < 4503599627370496 ∧ o82.toNat < 4503599627370496 ∧ o83.toNat < 4503599627370496)) ∧
        ((o196.toNat < 4503599627370496 ∧ o197.toNat < 4503599627370496 ∧ o198.toNat < 4503599627370496 ∧ o199.toNat < 4503599627370496 ∧ o200.toNat < 4503599627370496)) ∧
        ((t452.toNat < 4503599627370496 ∧ t476.toNat < 4503599627370496 ∧ t488.toNat < 4503599627370496 ∧ t492.toNat < 4503599627370496 ∧ t484.toNat < 4503599627370496)) ∧
        ((o181.toNat < 4503599627370496 ∧ o182.toNat < 4503599627370496 ∧ o183.toNat < 4503599627370496 ∧ o184.toNat < 4503599627370496 ∧ o185.toNat < 4503599627370496)) ∧
        ((t632.toNat < 4503599627370496 ∧ t644.toNat < 4503599627370496 ∧ t660.toNat < 4503599627370496 ∧ t676.toNat < 4503599627370496 ∧ t680.toNat < 4503599627370496)) ∧
        ((o166.toNat < 4503599627370496 ∧ o167.toNat < 4503599627370496 ∧ o168.toNat < 4503599627370496 ∧ o169.toNat < 4503599627370496 ∧ o170.toNat < 4503599627370496)) ∧
        ((t560.toNat < 9007199254740992 ∧ t564.toNat < 9007199254740992 ∧ t584.toNat < 9007199254740992 ∧ t588.toNat < 9007199254740992 ∧ t616.toNat < 9007199254740992)) ∧
        ((o151.toNat < 4503599627370496 ∧ o152.toNat < 4503599627370496 ∧ o153.toNat < 4503599627370496 ∧ o154.toNat < 4503599627370496 ∧ o155.toNat < 4503599627370496)) ∧
        ((o118.toNat < 4503599627370496 ∧ o119.toNat < 4503599627370496 ∧ o120.toNat < 4503599627370496 ∧ o121.toNat < 4503599627370496 ∧ o122.toNat < 4503599627370496)) ∧
        ((o103.toNat < 4503599627370496 ∧ o104.toNat < 4503599627370496 ∧ o105.toNat < 4503599627370496 ∧ o106.toNat < 4503599627370496 ∧ o107.toNat < 4503599627370496)) ∧
        ((t144.toNat < 4503599627370496 ∧ t164.toNat < 4503599627370496 ∧ t172.toNat < 4503599627370496 ∧ t180.toNat < 4503599627370496 ∧ t188.toNat < 4503599627370496)) ∧
        ((t232.toNat < 18014398509481984 ∧ t228.toNat < 18014398509481984 ∧ t248.toNat < 18014398509481984 ∧ t256.toNat < 18014398509481984 ∧ t276.toNat < 18014398509481984)) ∧
        ((t76.toNat < 18014398509481984 ∧ t96.toNat < 18014398509481984 ∧ t100.toNat < 18014398509481984 ∧ t120.toNat < 18014398509481984 ∧ t68.toNat < 18014398509481984)) ∧
        ((t316.toNat < 4503599627370496 ∧ t328.toNat < 4503599627370496 ∧ t324.toNat < 4503599627370496 ∧ t336.toNat < 4503599627370496 ∧ t348.toNat < 4503599627370496)) ∧
        ((o181.toNat < 4503599627370496 ∧ o182.toNat < 4503599627370496 ∧ o183.toNat < 4503599627370496 ∧ o184.toNat < 4503599627370496 ∧ o185.toNat < 4503599627370496)) ∧
        ((fe51Val o181 o182 o183 o184 o185) % p25519 = fe51ValOfBytes fe51MontA24Bytes * (fe51Val t452 t476 t488 t492 t484) % p25519) ∧
        ((o196.toNat < 4503599627370496 ∧ o197.toNat < 4503599627370496 ∧ o198.toNat < 4503599627370496 ∧ o199.toNat < 4503599627370496 ∧ o200.toNat < 4503599627370496)) ∧
        ((fe51Val o196 o197 o198 o199 o200) % p25519 = (fe51Val o64 o65 o66 o67 o68) * (fe51Val o79 o80 o81 o82 o83) % p25519) ∧
        sf.mem ⊨ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ F := by
  have e0 : mkS s (mpl.base 12 + BitVec.ofNat 64 724) s.regs.regs (S - 832#64) s.pstate s.mem s.vregs.regs = s := by
    rw [← hpc, ← hsp]; rfl
  rw [← e0]
  show Reach (bprog mpl 12) _ _
  refine d12_s8 (S := S) (vo := s.vregs.regs) (c19 := c19) (c20 := c20) (c21 := c21) (c22 := c22) (c23 := c23) (c24 := c24) (c25 := c25) (c26 := c26) (c27 := c27) (c28 := c28) (c29 := c29) (c30 := c30) hP hCL hal (by simpa only [lbw, valw, Nat.reducePow] using hPU) (by simpa only [lbw, valw, Nat.reducePow] using hPW) (by simpa only [lbw, valw, Nat.reducePow] using hQU) (by simpa only [lbw, valw, Nat.reducePow] using hQW) (by simpa only [lbw, valw, Nat.reducePow] using hU1) hrun (Memory.KeepsFrozen.refl _) rfl hr0 hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26 hr27 hr28 hr29 (by simpa only [lbw, valw, Nat.reducePow] using bd_Diff) (by simpa only [lbw, valw, Nat.reducePow] using bd_Tmp) (by simpa only [lbw, valw, Nat.reducePow] using bd_Sum) (by simpa only [lbw, valw, Nat.reducePow] using bd_U3) (by simpa only [lbw, valw, Nat.reducePow] using bd_CB) (by simpa only [lbw, valw, Nat.reducePow] using bd_DA) (by simpa only [lbw, valw, Nat.reducePow] using bd_B) (by simpa only [lbw, valw, Nat.reducePow] using bd_C) (by simpa only [lbw, valw, Nat.reducePow] using bd_A) (by simpa only [lbw, valw, Nat.reducePow] using bd_D) (by simpa only [lbw, valw, Nat.reducePow] using bd_E) (by simpa only [lbw, valw, Nat.reducePow] using bd_AA) (by simpa only [lbw, valw, Nat.reducePow] using bd_BB) hs ?_
  intro sb r ps m v o196 o197 o198 o199 o200 o181 o182 o183 o184 o185 hrun kf hvs hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26 hr27 hr28 hr29 bd_AA bd_BB bd_U2 bd_E bd_A24E bd_Diff bd_Tmp bd_Sum bd_U3 bd_CB bd_DA bd_B bd_C bd_A bd_D hb178 hval179 hb193 hval194 hs
  apply Reach.done
  exact ⟨hrun, rfl, rfl, hvs, o196, o197, o198, o199, o200, o181, o182, o183, o184, o185, hr19, hr20, hr21, hr22, hr23, hr24, hr25, hr26, hr27, hr28, hr29, (by simpa only [lbw, valw, Nat.reducePow] using bd_AA), (by simpa only [lbw, valw, Nat.reducePow] using bd_BB), (by simpa only [lbw, valw, Nat.reducePow] using bd_U2), (by simpa only [lbw, valw, Nat.reducePow] using bd_E), (by simpa only [lbw, valw, Nat.reducePow] using bd_A24E), (by simpa only [lbw, valw, Nat.reducePow] using bd_Diff), (by simpa only [lbw, valw, Nat.reducePow] using bd_Tmp), (by simpa only [lbw, valw, Nat.reducePow] using bd_Sum), (by simpa only [lbw, valw, Nat.reducePow] using bd_U3), (by simpa only [lbw, valw, Nat.reducePow] using bd_CB), (by simpa only [lbw, valw, Nat.reducePow] using bd_DA), (by simpa only [lbw, valw, Nat.reducePow] using bd_B), (by simpa only [lbw, valw, Nat.reducePow] using bd_C), (by simpa only [lbw, valw, Nat.reducePow] using bd_A), (by simpa only [lbw, valw, Nat.reducePow] using bd_D), (by simpa only [lbw, valw, Nat.reducePow] using hb178), (by simpa only [lbw, valw, Nat.reducePow] using hval179), (by simpa only [lbw, valw, Nat.reducePow] using hb193), (by simpa only [lbw, valw, Nat.reducePow] using hval194), hs⟩

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
    {t632 t644 t660 t676 t680 o166 o167 o168 o169 o170 t560 t564 t584 t588 t616 o151 o152 o153 o154 o155 o118 o119 o120 o121 o122 o103 o104 o105 o106 o107 t144 t164 t172 t180 t188 t232 t228 t248 t256 t276 t76 t96 t100 t120 t68 t316 t328 t324 t336 t348 t452 t476 t488 t492 t484 o64 o65 o66 o67 o68 o79 o80 o81 o82 o83 a24e_0 a24e_1 a24e_2 a24e_3 a24e_4 u2_0 u2_1 u2_2 u2_3 u2_4 a24epbb_0 a24epbb_1 a24epbb_2 a24epbb_3 a24epbb_4 w2_0 w2_1 w2_2 w2_3 w2_4 w3_0 w3_1 w3_2 w3_3 w3_4 g1 : BitVec 64}
    (hal : (S &&& 15#64 == 0#64) = true)
    (hPU : p0.toNat < 9007199254740992 ∧ p1.toNat < 9007199254740992 ∧ p2.toNat < 9007199254740992 ∧ p3.toNat < 9007199254740992 ∧ p4.toNat < 9007199254740992)
    (hPW : p5.toNat < 9007199254740992 ∧ p6.toNat < 9007199254740992 ∧ p7.toNat < 9007199254740992 ∧ p8.toNat < 9007199254740992 ∧ p9.toNat < 9007199254740992)
    (hQU : q0.toNat < 9007199254740992 ∧ q1.toNat < 9007199254740992 ∧ q2.toNat < 9007199254740992 ∧ q3.toNat < 9007199254740992 ∧ q4.toNat < 9007199254740992)
    (hQW : q5.toNat < 9007199254740992 ∧ q6.toNat < 9007199254740992 ∧ q7.toNat < 9007199254740992 ∧ q8.toNat < 9007199254740992 ∧ q9.toNat < 9007199254740992)
    (hU1 : uw0.toNat < 18014398509481984 ∧ uw1.toNat < 18014398509481984 ∧ uw2.toNat < 18014398509481984 ∧ uw3.toNat < 18014398509481984 ∧ uw4.toNat < 18014398509481984)
    (hrun : s.status = Arm64.ExecStatus.Running) (hpc : s.pc = mpl.base 12 + BitVec.ofNat 64 724) (hsp : s.sp = S - 832#64)
    (hr0 : s.regs.regs 0#5 = (fe51_mont_a24 mpl))
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
    (bd_Diff : (t632.toNat < 4503599627370496 ∧ t644.toNat < 4503599627370496 ∧ t660.toNat < 4503599627370496 ∧ t676.toNat < 4503599627370496 ∧ t680.toNat < 4503599627370496))
    (bd_Tmp : (o166.toNat < 4503599627370496 ∧ o167.toNat < 4503599627370496 ∧ o168.toNat < 4503599627370496 ∧ o169.toNat < 4503599627370496 ∧ o170.toNat < 4503599627370496))
    (bd_Sum : (t560.toNat < 9007199254740992 ∧ t564.toNat < 9007199254740992 ∧ t584.toNat < 9007199254740992 ∧ t588.toNat < 9007199254740992 ∧ t616.toNat < 9007199254740992))
    (bd_U3 : (o151.toNat < 4503599627370496 ∧ o152.toNat < 4503599627370496 ∧ o153.toNat < 4503599627370496 ∧ o154.toNat < 4503599627370496 ∧ o155.toNat < 4503599627370496))
    (bd_CB : (o118.toNat < 4503599627370496 ∧ o119.toNat < 4503599627370496 ∧ o120.toNat < 4503599627370496 ∧ o121.toNat < 4503599627370496 ∧ o122.toNat < 4503599627370496))
    (bd_DA : (o103.toNat < 4503599627370496 ∧ o104.toNat < 4503599627370496 ∧ o105.toNat < 4503599627370496 ∧ o106.toNat < 4503599627370496 ∧ o107.toNat < 4503599627370496))
    (bd_B : (t144.toNat < 4503599627370496 ∧ t164.toNat < 4503599627370496 ∧ t172.toNat < 4503599627370496 ∧ t180.toNat < 4503599627370496 ∧ t188.toNat < 4503599627370496))
    (bd_C : (t232.toNat < 18014398509481984 ∧ t228.toNat < 18014398509481984 ∧ t248.toNat < 18014398509481984 ∧ t256.toNat < 18014398509481984 ∧ t276.toNat < 18014398509481984))
    (bd_A : (t76.toNat < 18014398509481984 ∧ t96.toNat < 18014398509481984 ∧ t100.toNat < 18014398509481984 ∧ t120.toNat < 18014398509481984 ∧ t68.toNat < 18014398509481984))
    (bd_D : (t316.toNat < 4503599627370496 ∧ t328.toNat < 4503599627370496 ∧ t324.toNat < 4503599627370496 ∧ t336.toNat < 4503599627370496 ∧ t348.toNat < 4503599627370496))
    (bd_E : (t452.toNat < 4503599627370496 ∧ t476.toNat < 4503599627370496 ∧ t488.toNat < 4503599627370496 ∧ t492.toNat < 4503599627370496 ∧ t484.toNat < 4503599627370496))
    (bd_AA : (o64.toNat < 4503599627370496 ∧ o65.toNat < 4503599627370496 ∧ o66.toNat < 4503599627370496 ∧ o67.toNat < 4503599627370496 ∧ o68.toNat < 4503599627370496))
    (bd_BB : (o79.toNat < 4503599627370496 ∧ o80.toNat < 4503599627370496 ∧ o81.toNat < 4503599627370496 ∧ o82.toNat < 4503599627370496 ∧ o83.toNat < 4503599627370496))
    (hs : s.mem ⊨ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F) :
    ∃ sf, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 12) s sf ∧
      sf.status = Arm64.ExecStatus.Running ∧
      sf.pc = mpl.base 12 + BitVec.ofNat 64 752 ∧
      sf.sp = S - 832#64 ∧
      Arm64.VRegFile.calleeSaved sf.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ o196 o197 o198 o199 o200 o181 o182 o183 o184 o185 : BitVec 64,
        sf.regs.regs 19#5 = Qb ∧
        sf.regs.regs 20#5 = Pb ∧
        sf.regs.regs 21#5 = o80 ∧
        sf.regs.regs 22#5 = 0x007ffffffffffff0#64 ∧
        sf.regs.regs 23#5 = o79 ∧
        sf.regs.regs 24#5 = 36028797018963664#64 ∧
        sf.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) ∧
        sf.regs.regs 26#5 = o83 ∧
        sf.regs.regs 27#5 = o82 ∧
        sf.regs.regs 28#5 = o81 ∧
        sf.regs.regs 29#5 = (S - 96#64) ∧
        ((o64.toNat < 4503599627370496 ∧ o65.toNat < 4503599627370496 ∧ o66.toNat < 4503599627370496 ∧ o67.toNat < 4503599627370496 ∧ o68.toNat < 4503599627370496)) ∧
        ((o79.toNat < 4503599627370496 ∧ o80.toNat < 4503599627370496 ∧ o81.toNat < 4503599627370496 ∧ o82.toNat < 4503599627370496 ∧ o83.toNat < 4503599627370496)) ∧
        ((o196.toNat < 4503599627370496 ∧ o197.toNat < 4503599627370496 ∧ o198.toNat < 4503599627370496 ∧ o199.toNat < 4503599627370496 ∧ o200.toNat < 4503599627370496)) ∧
        ((t452.toNat < 4503599627370496 ∧ t476.toNat < 4503599627370496 ∧ t488.toNat < 4503599627370496 ∧ t492.toNat < 4503599627370496 ∧ t484.toNat < 4503599627370496)) ∧
        ((o181.toNat < 4503599627370496 ∧ o182.toNat < 4503599627370496 ∧ o183.toNat < 4503599627370496 ∧ o184.toNat < 4503599627370496 ∧ o185.toNat < 4503599627370496)) ∧
        ((t632.toNat < 4503599627370496 ∧ t644.toNat < 4503599627370496 ∧ t660.toNat < 4503599627370496 ∧ t676.toNat < 4503599627370496 ∧ t680.toNat < 4503599627370496)) ∧
        ((o166.toNat < 4503599627370496 ∧ o167.toNat < 4503599627370496 ∧ o168.toNat < 4503599627370496 ∧ o169.toNat < 4503599627370496 ∧ o170.toNat < 4503599627370496)) ∧
        ((t560.toNat < 9007199254740992 ∧ t564.toNat < 9007199254740992 ∧ t584.toNat < 9007199254740992 ∧ t588.toNat < 9007199254740992 ∧ t616.toNat < 9007199254740992)) ∧
        ((o151.toNat < 4503599627370496 ∧ o152.toNat < 4503599627370496 ∧ o153.toNat < 4503599627370496 ∧ o154.toNat < 4503599627370496 ∧ o155.toNat < 4503599627370496)) ∧
        ((o118.toNat < 4503599627370496 ∧ o119.toNat < 4503599627370496 ∧ o120.toNat < 4503599627370496 ∧ o121.toNat < 4503599627370496 ∧ o122.toNat < 4503599627370496)) ∧
        ((o103.toNat < 4503599627370496 ∧ o104.toNat < 4503599627370496 ∧ o105.toNat < 4503599627370496 ∧ o106.toNat < 4503599627370496 ∧ o107.toNat < 4503599627370496)) ∧
        ((t144.toNat < 4503599627370496 ∧ t164.toNat < 4503599627370496 ∧ t172.toNat < 4503599627370496 ∧ t180.toNat < 4503599627370496 ∧ t188.toNat < 4503599627370496)) ∧
        ((t232.toNat < 18014398509481984 ∧ t228.toNat < 18014398509481984 ∧ t248.toNat < 18014398509481984 ∧ t256.toNat < 18014398509481984 ∧ t276.toNat < 18014398509481984)) ∧
        ((t76.toNat < 18014398509481984 ∧ t96.toNat < 18014398509481984 ∧ t100.toNat < 18014398509481984 ∧ t120.toNat < 18014398509481984 ∧ t68.toNat < 18014398509481984)) ∧
        ((t316.toNat < 4503599627370496 ∧ t328.toNat < 4503599627370496 ∧ t324.toNat < 4503599627370496 ∧ t336.toNat < 4503599627370496 ∧ t348.toNat < 4503599627370496)) ∧
        ((o181.toNat < 4503599627370496 ∧ o182.toNat < 4503599627370496 ∧ o183.toNat < 4503599627370496 ∧ o184.toNat < 4503599627370496 ∧ o185.toNat < 4503599627370496)) ∧
        ((fe51Val o181 o182 o183 o184 o185) % p25519 = fe51ValOfBytes fe51MontA24Bytes * (fe51Val t452 t476 t488 t492 t484) % p25519) ∧
        ((o196.toNat < 4503599627370496 ∧ o197.toNat < 4503599627370496 ∧ o198.toNat < 4503599627370496 ∧ o199.toNat < 4503599627370496 ∧ o200.toNat < 4503599627370496)) ∧
        ((fe51Val o196 o197 o198 o199 o200) % p25519 = (fe51Val o64 o65 o66 o67 o68) * (fe51Val o79 o80 o81 o82 o83) % p25519) ∧
        sf.mem ⊨ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ F := by
  exact X25519Dalek.differentialAddAndDouble_724_752_dev hP hCL hal hPU hPW hQU hQW hU1 hrun hpc hsp hr0 hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26 hr27 hr28 hr29 bd_Diff bd_Tmp bd_Sum bd_U3 bd_CB bd_DA bd_B bd_C bd_A bd_D bd_E bd_AA bd_BB hs

end
