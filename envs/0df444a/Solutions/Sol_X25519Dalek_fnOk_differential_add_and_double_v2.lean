-- Prove2me | solution 1 for X25519Dalek.fnOk_differential_add_and_double_v2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T21:37:55.137047+00:00
-- url     : https://prove2.me/submissions/0d41e16e-cc31-4a29-bb2d-78fbb96d9d2c

import Definitions.Def_X25519Dalek_PlacedObj
import Definitions.Def_X25519Dalek_Rfc7748
import Definitions.Def_X25519Dalek_Spec
import Theorems.Thm_X25519Dalek_steps_keepsFrozen_v2
import Theorems.Thm_X25519Dalek_differentialAddAndDouble_0_192
import Theorems.Thm_X25519Dalek_differentialAddAndDouble_192_364
import Theorems.Thm_X25519Dalek_differentialAddAndDouble_364_384
import Theorems.Thm_X25519Dalek_differentialAddAndDouble_384_532
import Theorems.Thm_X25519Dalek_differentialAddAndDouble_532_696
import Theorems.Thm_X25519Dalek_differentialAddAndDouble_696_716
import Theorems.Thm_X25519Dalek_differentialAddAndDouble_716_724
import Theorems.Thm_X25519Dalek_differentialAddAndDouble_724_752
import Theorems.Thm_X25519Dalek_differentialAddAndDouble_752_828
import Theorems.Thm_X25519Dalek_differentialAddAndDouble_828_ret
import Mathlib.Data.BitVec
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

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

end Memory

namespace Memory

end Memory

namespace Heap

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

theorem Steps.trans' {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Steps p b c) :
    Steps p a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

/-! ## Reaching a final state -/

/-! ## Fetching from the loaded code -/

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

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

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

end

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
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

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

theorem aSb (S : BitVec 64) (a b c : Nat) (h : BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 c) :
    S - BitVec.ofNat 64 a + BitVec.ofNat 64 b = S - BitVec.ofNat 64 c := by
  rw [← h]; try abel

section
variable {p : Program} {s0 : State} {pc pc' : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

end


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
theorem pick3 (A1 A2 A3 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ R) = (A3 ∗ A1 ∗ A2 ∗ R) := by ac_rfl
theorem pick4 (A1 A2 A3 A4 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ R) = (A4 ∗ A1 ∗ A2 ∗ A3 ∗ R) := by ac_rfl
theorem pick5 (A1 A2 A3 A4 A5 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ R) = (A5 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ R) := by ac_rfl
theorem pick6 (A1 A2 A3 A4 A5 A6 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ R) = (A6 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ R) := by ac_rfl
theorem pick7 (A1 A2 A3 A4 A5 A6 A7 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ R) = (A7 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ R) := by ac_rfl
theorem pick8 (A1 A2 A3 A4 A5 A6 A7 A8 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ R) = (A8 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ R) := by ac_rfl
theorem pick9 (A1 A2 A3 A4 A5 A6 A7 A8 A9 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ R) = (A9 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ R) := by ac_rfl
theorem pick10 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ R) = (A10 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ R) := by ac_rfl
theorem pick11 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ R) = (A11 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ R) := by ac_rfl
theorem pick12 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ R) = (A12 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ R) := by ac_rfl
theorem pick13 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ R) = (A13 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ R) := by ac_rfl
theorem pick14 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ R) = (A14 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ R) := by ac_rfl
theorem pick15 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ R) = (A15 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ R) := by ac_rfl
theorem pick16 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ R) = (A16 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ R) := by ac_rfl
theorem pick17 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ R) = (A17 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ R) := by ac_rfl
theorem pick18 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ R) = (A18 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ R) := by ac_rfl
theorem pick19 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ R) = (A19 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ R) := by ac_rfl
theorem pick20 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ R) = (A20 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ R) := by ac_rfl
theorem pick21 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ R) = (A21 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ R) := by ac_rfl
theorem pick25 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ R) = (A25 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ R) := by ac_rfl
theorem pick26 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ A26 ∗ R) = (A26 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ R) := by ac_rfl

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

theorem list10 {α : Type} (l : List α) (h : l.length = 10) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9, l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9], _ => exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, rfl⟩

theorem list12 {α : Type} (l : List α) (h : l.length = 12) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11, l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, rfl⟩

theorem list1 {α : Type} (l : List α) (h : l.length = 1) : ∃ a0, l = [a0] := by
  match l, h with
  | [a0], _ => exact ⟨a0, rfl⟩

/-- A byte list of length `8 k` is the flattening of its `k` words. -/
theorem bytes_words_eq (bs : List (BitVec 8)) (k : Nat) (h : bs.length = 8 * k) :
    bs = (chunks64 bs k).flatMap unpack64 := (chunks64_flat k bs h).symm

theorem flat10 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) :
    [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9].flatMap unpack64 =
      [w0, w1, w2, w3, w4].flatMap unpack64 ++ [w5, w6, w7, w8, w9].flatMap unpack64 := by
  simp [List.flatMap_cons]

theorem readLE_words10 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) (off : Nat) (h : off < 5) :
    ByteSlice.readLE ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9].flatMap unpack64) (40 + 8 * off) 8 =
      ByteSlice.readLE ([w5, w6, w7, w8, w9].flatMap unpack64) (8 * off) 8 := by
  rw [flat10, show 40 + 8 * off = ([w0, w1, w2, w3, w4].flatMap unpack64).length + 8 * off by simp,
    readLE_append_right]

theorem readLE_words10_lo (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) (off : Nat) (h : off < 5) :
    ByteSlice.readLE ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9].flatMap unpack64) (8 * off) 8 =
      ByteSlice.readLE ([w0, w1, w2, w3, w4].flatMap unpack64) (8 * off) 8 := by
  rw [flat10, readLE_append_left _ _ _ (by simp; omega)]

theorem montb_words (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) (B : Nat)
    (h : montProjBounded ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9].flatMap unpack64) B) :
    fe51LimbsBounded ([w0, w1, w2, w3, w4].flatMap unpack64) B ∧
      fe51LimbsBounded ([w5, w6, w7, w8, w9].flatMap unpack64) B := by
  obtain ⟨-, hU, hW⟩ := h
  simp only [montFe51LimbsBoundedAt, fe51LimbsBoundedAt] at hU hW
  have l0 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 0 (by decide)
  have l1 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 1 (by decide)
  have l2 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 2 (by decide)
  have l3 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 3 (by decide)
  have l4 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 4 (by decide)
  have u0 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 0 (by decide)
  have u1 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 1 (by decide)
  have u2 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 2 (by decide)
  have u3 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 3 (by decide)
  have u4 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 4 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.add_zero] at l0 l1 l2 l3 l4 u0 u1 u2 u3 u4 hU hW
  unfold fe51LimbsBounded
  refine ⟨⟨by simp, ?_⟩, ⟨by simp, ?_⟩⟩
  · rw [← l0, ← l1, ← l2, ← l3, ← l4]; exact hU
  · rw [← u0, ← u1, ← u2, ← u3, ← u4]; exact hW

theorem montProj_words (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) :
    montProjOfBytes ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9].flatMap unpack64) =
      ⟨fe51ValOfBytes ([w0, w1, w2, w3, w4].flatMap unpack64) % p25519,
        fe51ValOfBytes ([w5, w6, w7, w8, w9].flatMap unpack64) % p25519⟩ := by
  have l0 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 0 (by decide)
  have l1 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 1 (by decide)
  have l2 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 2 (by decide)
  have l3 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 3 (by decide)
  have l4 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 4 (by decide)
  have u0 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 0 (by decide)
  have u1 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 1 (by decide)
  have u2 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 2 (by decide)
  have u3 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 3 (by decide)
  have u4 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 4 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.add_zero] at l0 l1 l2 l3 l4 u0 u1 u2 u3 u4
  simp only [montProjOfBytes, montFe51ValAt, fe51ValAt, fe51ValOfBytes, Nat.reduceAdd]
  rw [l0, l1, l2, l3, l4, u0, u1, u2, u3, u4]

theorem a24_val : fe51ValOfBytes fe51MontA24Bytes = 121666 := by decide +kernel

theorem zc {a b : Nat} : (a : ZMod p25519) = (b : ZMod p25519) ↔ a % p25519 = b % p25519 :=
  ZMod.natCast_eq_natCast_iff' a b p25519

theorem z_mod (a : Nat) : ((a % p25519 : Nat) : ZMod p25519) = a := ZMod.natCast_mod a p25519

theorem z_add (a b : Nat) : ((fpAdd a b : Nat) : ZMod p25519) = a + b := by
  rw [fpAdd, z_mod]; push_cast; ring

theorem z_sub (a b : Nat) : ((fpSub a b : Nat) : ZMod p25519) = a - b := by
  rw [fpSub, z_mod]
  have h : b % p25519 ≤ a + p25519 := le_trans (Nat.mod_lt _ (by decide)).le (by omega)
  rw [Nat.cast_sub h, Nat.cast_add, z_mod, ZMod.natCast_self]; ring

theorem z_mul (a b : Nat) : ((fpMul a b : Nat) : ZMod p25519) = a * b := by
  rw [fpMul, z_mod]; push_cast; rw [z_mod, z_mod]

theorem z_sq2 (a : Nat) : ((fpPow a (2 ^ (1#32 : BitVec 32).toNat) : Nat) : ZMod p25519) = a * a := by
  rw [show 2 ^ (1#32 : BitVec 32).toNat = 2 by decide, fpPow_eq_pow_mod _ _ (by decide), z_mod]; push_cast; ring

theorem z_sq (a : Nat) : ((fpSq a : Nat) : ZMod p25519) = a * a := by
  rw [fpSq, z_mul]

theorem lt_p_mod (a : Nat) : a % p25519 < p25519 := Nat.mod_lt _ (by decide)

theorem eq_of_z {a b : Nat} (ha : a < p25519) (hb : b < p25519) (h : (a : ZMod p25519) = b) : a = b := by
  rw [zc, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h; exact h

theorem fpMul_lt (a b : Nat) : fpMul a b < p25519 := lt_p_mod _
theorem fpSq_lt (a : Nat) : fpSq a < p25519 := lt_p_mod _

/-- The field identity of the ladder step: what the compiled code computes is RFC 7748's
`montDiffAddAndDouble` (with `a24 = 121665` there and the constant `121666` in the code, via
`E = AA − BB`). -/
theorem dad_math (PU PW QU QW U1 vA vB vC vD vAA vBB vDA vCB vE vSum vDiff vU3 vTmp vA24E vU2 vA24EpBB vW2
      vW3 : Nat)
    (hA : vA % p25519 = fpAdd (PW % p25519) (PU % p25519))
    (hB : vB % p25519 = fpSub (PU % p25519) (PW % p25519))
    (hC : vC % p25519 = fpAdd (QW % p25519) (QU % p25519))
    (hD : vD % p25519 = fpSub (QU % p25519) (QW % p25519))
    (hAA : vAA % p25519 = fpPow (vA % p25519) (2 ^ (1#32 : BitVec 32).toNat))
    (hBB : vBB % p25519 = fpPow (vB % p25519) (2 ^ (1#32 : BitVec 32).toNat))
    (hDA : vDA % p25519 = vA * vD % p25519) (hCB : vCB % p25519 = vB * vC % p25519)
    (hE : vE % p25519 = fpSub (vAA % p25519) (vBB % p25519))
    (hSum : vSum % p25519 = fpAdd (vCB % p25519) (vDA % p25519))
    (hDiff : vDiff % p25519 = fpSub (vDA % p25519) (vCB % p25519))
    (hU3 : vU3 % p25519 = fpPow (vSum % p25519) (2 ^ (1#32 : BitVec 32).toNat))
    (hTmp : vTmp % p25519 = fpPow (vDiff % p25519) (2 ^ (1#32 : BitVec 32).toNat))
    (hA24E : vA24E % p25519 = 121666 * vE % p25519)
    (hU2 : vU2 % p25519 = vAA * vBB % p25519)
    (hA24EpBB : vA24EpBB % p25519 = fpAdd (vA24E % p25519) (vBB % p25519))
    (hW2 : vW2 % p25519 = vE * vA24EpBB % p25519) (hW3 : vW3 % p25519 = U1 * vTmp % p25519) :
    montDiffAddAndDouble (U1 % p25519) ⟨PU % p25519, PW % p25519⟩ ⟨QU % p25519, QW % p25519⟩ =
      (⟨vU2 % p25519, vW2 % p25519⟩, ⟨vU3 % p25519, vW3 % p25519⟩) := by
  have zA : (vA : ZMod p25519) = PW + PU := by rw [← z_mod vA, hA, z_add, z_mod, z_mod]
  have zB : (vB : ZMod p25519) = PU - PW := by rw [← z_mod vB, hB, z_sub, z_mod, z_mod]
  have zC : (vC : ZMod p25519) = QW + QU := by rw [← z_mod vC, hC, z_add, z_mod, z_mod]
  have zD : (vD : ZMod p25519) = QU - QW := by rw [← z_mod vD, hD, z_sub, z_mod, z_mod]
  have zAA : (vAA : ZMod p25519) = vA * vA := by rw [← z_mod vAA, hAA, z_sq2, z_mod]
  have zBB : (vBB : ZMod p25519) = vB * vB := by rw [← z_mod vBB, hBB, z_sq2, z_mod]
  have zDA : (vDA : ZMod p25519) = vA * vD := by rw [← z_mod vDA, hDA, z_mod]; push_cast; ring
  have zCB : (vCB : ZMod p25519) = vB * vC := by rw [← z_mod vCB, hCB, z_mod]; push_cast; ring
  have zE : (vE : ZMod p25519) = vAA - vBB := by rw [← z_mod vE, hE, z_sub, z_mod, z_mod]
  have zSum : (vSum : ZMod p25519) = vCB + vDA := by rw [← z_mod vSum, hSum, z_add, z_mod, z_mod]
  have zDiff : (vDiff : ZMod p25519) = vDA - vCB := by rw [← z_mod vDiff, hDiff, z_sub, z_mod, z_mod]
  have zU3 : (vU3 : ZMod p25519) = vSum * vSum := by rw [← z_mod vU3, hU3, z_sq2, z_mod]
  have zTmp : (vTmp : ZMod p25519) = vDiff * vDiff := by rw [← z_mod vTmp, hTmp, z_sq2, z_mod]
  have zA24E : (vA24E : ZMod p25519) = 121666 * vE := by rw [← z_mod vA24E, hA24E, z_mod]; push_cast; ring
  have zU2 : (vU2 : ZMod p25519) = vAA * vBB := by rw [← z_mod vU2, hU2, z_mod]; push_cast; ring
  have zA24EpBB : (vA24EpBB : ZMod p25519) = vA24E + vBB := by
    rw [← z_mod vA24EpBB, hA24EpBB, z_add, z_mod, z_mod]
  have zW2 : (vW2 : ZMod p25519) = vE * vA24EpBB := by rw [← z_mod vW2, hW2, z_mod]; push_cast; ring
  have zW3 : (vW3 : ZMod p25519) = U1 * vTmp := by rw [← z_mod vW3, hW3, z_mod]; push_cast; ring
  simp only [montDiffAddAndDouble, Prod.mk.injEq, MontProjPoint.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · refine (eq_of_z (fpMul_lt _ _) (lt_p_mod _) ?_)
    simp only [z_mul, z_sq, z_add, z_sub, z_mod]
    rw [zU2, zAA, zBB, zA, zB]; ring
  · refine (eq_of_z (fpMul_lt _ _) (lt_p_mod _) ?_)
    simp only [z_mul, z_sq, z_add, z_sub, z_mod]
    rw [zW2, zA24EpBB, zA24E, zE, zAA, zBB, zA, zB]; push_cast; ring
  · refine (eq_of_z (fpSq_lt _) (lt_p_mod _) ?_)
    simp only [z_mul, z_sq, z_add, z_sub, z_mod]
    rw [zU3, zSum, zCB, zDA, zA, zB, zC, zD]; ring
  · refine (eq_of_z (fpMul_lt _ _) (lt_p_mod _) ?_)
    simp only [z_mul, z_sq, z_add, z_sub, z_mod]
    rw [zW3, zTmp, zDiff, zCB, zDA, zA, zB, zC, zD]; ring

theorem montb_of_words (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) (B : Nat)
    (hU : fe51LimbsBounded ([w0, w1, w2, w3, w4].flatMap unpack64) B)
    (hW : fe51LimbsBounded ([w5, w6, w7, w8, w9].flatMap unpack64) B) :
    montProjBounded ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9].flatMap unpack64) B := by
  have l0 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 0 (by decide)
  have l1 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 1 (by decide)
  have l2 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 2 (by decide)
  have l3 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 3 (by decide)
  have l4 := readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 4 (by decide)
  have u0 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 0 (by decide)
  have u1 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 1 (by decide)
  have u2 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 2 (by decide)
  have u3 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 3 (by decide)
  have u4 := readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 4 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.add_zero] at l0 l1 l2 l3 l4 u0 u1 u2 u3 u4
  unfold fe51LimbsBounded at hU hW
  refine ⟨by simp, ?_, ?_⟩
  · simp only [montFe51LimbsBoundedAt, fe51LimbsBoundedAt, Nat.reduceAdd, Nat.zero_add]
    rw [l0, l1, l2, l3, l4]; exact hU.2
  · simp only [montFe51LimbsBoundedAt, fe51LimbsBoundedAt, Nat.reduceAdd]
    rw [u0, u1, u2, u3, u4]; exact hW.2

theorem post_intro {m : Memory} {A B C R : SepProp} {Y : List (BitVec 8) → List (BitVec 8) → SepProp}
    (p q : List (BitVec 8)) (h : m ⊨ (A ∗ B ∗ C ∗ Y p q) ∗ R) :
    m ⊨ (A ∗ B ∗ C ∗ (∃∗ x, ∃∗ y, Y x y)) ∗ R := by
  have e1 : Y p q ⊢ (∃∗ x, ∃∗ y, Y x y) := fun hh hY => ⟨p, ⟨q, hY⟩⟩
  have e : (A ∗ B ∗ C ∗ Y p q) ⊢ (A ∗ B ∗ C ∗ (∃∗ x, ∃∗ y, Y x y)) :=
    sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) e1))
  exact sat_sep_mono h e

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

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

abbrev dadName : String := "curve25519_dalek::montgomery::differential_add_and_double"

theorem lk12 : lookupBlockSym dadName x25519CliMultiLib.blocks = some (12, 0) := by decide +kernel

set_option maxHeartbeats 8000000 in
theorem dad_ok : fnOk dadName montDiffAddAndDoubleSpec := by
  refine ⟨12, 0, lk12, fun mpl hP => ?_⟩
  intro x R s0 hpc hrun hpre hal hCLp
  obtain ⟨Pb, Qb, u1, p_bs, q_bs, u1_bs⟩ := x
  have hfa : x25519CliMultiLib.fnAddr mpl dadName = mpl.base 12 := by
    simp [MultiPlacedLib.fnAddr, lk12]
  rw [hfa] at hpc
  simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at hpre
  have h1 := Satisfies.of_eq hpre
    (Q := ⌜s0.readReg64 Reg.x0 = Pb ∧ s0.readReg64 Reg.x1 = Qb ∧ s0.readReg64 Reg.x2 = u1 ∧
        montProjBounded p_bs (2 ^ 53) ∧ montProjBounded q_bs (2 ^ 53) ∧ fe51LimbsBounded u1_bs (2 ^ 54)⌝ ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝ ∗ stackFrame s0 1056 ∗ (Pb ↦ₛ p_bs) ∗ (Qb ↦ₛ q_bs) ∗
      (u1 ↦ₛ u1_bs) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ R) (by ac_rfl)
  rw [sat_pure_sep, sat_pure_sep] at h1
  obtain ⟨⟨hx0, hx1, hx2, hpb, hqb, hub⟩, hCL, h1⟩ := h1
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, hpw⟩ := list10 (chunks64 p_bs 10) (chunks64_length _ _)
  have hpe : p_bs = [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9].flatMap unpack64 := by rw [← hpw]; exact bytes_words_eq p_bs 10 (by rw [hpb.1])
  subst hpe
  clear hpw
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, hqw⟩ := list10 (chunks64 q_bs 10) (chunks64_length _ _)
  have hqe : q_bs = [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9].flatMap unpack64 := by rw [← hqw]; exact bytes_words_eq q_bs 10 (by rw [hqb.1])
  subst hqe
  clear hqw
  obtain ⟨uw0, uw1, uw2, uw3, uw4, huw⟩ := list5 (chunks64 u1_bs 5) (chunks64_length _ _)
  have hue : u1_bs = [uw0, uw1, uw2, uw3, uw4].flatMap unpack64 := by rw [← huw]; exact bytes_words_eq u1_bs 5 (by rw [hub.1])
  subst hue
  clear huw
  obtain ⟨hPU, hPW⟩ := montb_words p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 _ hpb
  obtain ⟨hQU, hQW⟩ := montb_words q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 _ hqb
  rw [lbw] at hPU hPW hQU hQW hub
  rw [← words_eq_bytes, ← words_eq_bytes, ← words_eq_bytes] at h1
  simp only [stackFrame] at h1
  have hs0 := h1
  clear h1
  have hr0 : s0.regs.regs 0#5 = Pb := by rw [← readGpr_eq s0 0#5 (by decide)]; exact hx0
  have hr1 : s0.regs.regs 1#5 = Qb := by rw [← readGpr_eq s0 1#5 (by decide)]; exact hx1
  have hr2 : s0.regs.regs 2#5 = u1 := by rw [← readGpr_eq s0 2#5 (by decide)]; exact hx2
  have hal' : (s0.sp &&& 15#64 == 0#64) = true := hal
  replace hs0 := sat_mr_split (a := s0.sp - BitVec.ofNat 64 1056) 224 832 (by norm_num) (s0.sp - 832#64) (aSb _ 1056 224 832 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 832#64) 8 824 (by norm_num) (s0.sp - 824#64) (aSb _ 832 8 824 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 824#64) 40 784 (by norm_num) (s0.sp - 784#64) (aSb _ 824 40 784 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 784#64) 40 744 (by norm_num) (s0.sp - 744#64) (aSb _ 784 40 744 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 744#64) 40 704 (by norm_num) (s0.sp - 704#64) (aSb _ 744 40 704 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 704#64) 40 664 (by norm_num) (s0.sp - 664#64) (aSb _ 704 40 664 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 664#64) 40 624 (by norm_num) (s0.sp - 624#64) (aSb _ 664 40 624 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 624#64) 40 584 (by norm_num) (s0.sp - 584#64) (aSb _ 624 40 584 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 584#64) 40 544 (by norm_num) (s0.sp - 544#64) (aSb _ 584 40 544 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 544#64) 40 504 (by norm_num) (s0.sp - 504#64) (aSb _ 544 40 504 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 504#64) 40 464 (by norm_num) (s0.sp - 464#64) (aSb _ 504 40 464 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 464#64) 40 424 (by norm_num) (s0.sp - 424#64) (aSb _ 464 40 424 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 424#64) 40 384 (by norm_num) (s0.sp - 384#64) (aSb _ 424 40 384 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 384#64) 40 344 (by norm_num) (s0.sp - 344#64) (aSb _ 384 40 344 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 344#64) 40 304 (by norm_num) (s0.sp - 304#64) (aSb _ 344 40 304 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 304#64) 40 264 (by norm_num) (s0.sp - 264#64) (aSb _ 304 40 264 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 264#64) 40 224 (by norm_num) (s0.sp - 224#64) (aSb _ 264 40 224 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 224#64) 40 184 (by norm_num) (s0.sp - 184#64) (aSb _ 224 40 184 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 184#64) 40 144 (by norm_num) (s0.sp - 144#64) (aSb _ 184 40 144 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 144#64) 40 104 (by norm_num) (s0.sp - 104#64) (aSb _ 144 40 104 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 104#64) 8 96 (by norm_num) (s0.sp - 96#64) (aSb _ 104 8 96 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  obtain ⟨L96, hL96, hs0⟩ := memRegion_words' (s0.sp - 96#64) 12 (by norm_num) hs0
  obtain ⟨sv0, sv1, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11, rfl⟩ := list12 L96 hL96
  rw [pick2] at hs0
  obtain ⟨L104, hL104, hs0⟩ := memRegion_words' (s0.sp - 104#64) 1 (by norm_num) hs0
  obtain ⟨g1, rfl⟩ := list1 L104 hL104
  rw [pick3] at hs0
  obtain ⟨L144, hL144, hs0⟩ := memRegion_words' (s0.sp - 144#64) 5 (by norm_num) hs0
  obtain ⟨w3_0, w3_1, w3_2, w3_3, w3_4, rfl⟩ := list5 L144 hL144
  rw [pick4] at hs0
  obtain ⟨L184, hL184, hs0⟩ := memRegion_words' (s0.sp - 184#64) 5 (by norm_num) hs0
  obtain ⟨w2_0, w2_1, w2_2, w2_3, w2_4, rfl⟩ := list5 L184 hL184
  rw [pick5] at hs0
  obtain ⟨L224, hL224, hs0⟩ := memRegion_words' (s0.sp - 224#64) 5 (by norm_num) hs0
  obtain ⟨a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4, rfl⟩ := list5 L224 hL224
  rw [pick6] at hs0
  obtain ⟨L264, hL264, hs0⟩ := memRegion_words' (s0.sp - 264#64) 5 (by norm_num) hs0
  obtain ⟨u2_0, u2_1, u2_2, u2_3, u2_4, rfl⟩ := list5 L264 hL264
  rw [pick7] at hs0
  obtain ⟨L304, hL304, hs0⟩ := memRegion_words' (s0.sp - 304#64) 5 (by norm_num) hs0
  obtain ⟨a24e_0, a24e_1, a24e_2, a24e_3, a24e_4, rfl⟩ := list5 L304 hL304
  rw [pick8] at hs0
  obtain ⟨L344, hL344, hs0⟩ := memRegion_words' (s0.sp - 344#64) 5 (by norm_num) hs0
  obtain ⟨tmp_0, tmp_1, tmp_2, tmp_3, tmp_4, rfl⟩ := list5 L344 hL344
  rw [pick9] at hs0
  obtain ⟨L384, hL384, hs0⟩ := memRegion_words' (s0.sp - 384#64) 5 (by norm_num) hs0
  obtain ⟨u3_0, u3_1, u3_2, u3_3, u3_4, rfl⟩ := list5 L384 hL384
  rw [pick10] at hs0
  obtain ⟨L424, hL424, hs0⟩ := memRegion_words' (s0.sp - 424#64) 5 (by norm_num) hs0
  obtain ⟨diff_0, diff_1, diff_2, diff_3, diff_4, rfl⟩ := list5 L424 hL424
  rw [pick11] at hs0
  obtain ⟨L464, hL464, hs0⟩ := memRegion_words' (s0.sp - 464#64) 5 (by norm_num) hs0
  obtain ⟨sum_0, sum_1, sum_2, sum_3, sum_4, rfl⟩ := list5 L464 hL464
  rw [pick12] at hs0
  obtain ⟨L504, hL504, hs0⟩ := memRegion_words' (s0.sp - 504#64) 5 (by norm_num) hs0
  obtain ⟨cb_0, cb_1, cb_2, cb_3, cb_4, rfl⟩ := list5 L504 hL504
  rw [pick13] at hs0
  obtain ⟨L544, hL544, hs0⟩ := memRegion_words' (s0.sp - 544#64) 5 (by norm_num) hs0
  obtain ⟨da_0, da_1, da_2, da_3, da_4, rfl⟩ := list5 L544 hL544
  rw [pick14] at hs0
  obtain ⟨L584, hL584, hs0⟩ := memRegion_words' (s0.sp - 584#64) 5 (by norm_num) hs0
  obtain ⟨e_0, e_1, e_2, e_3, e_4, rfl⟩ := list5 L584 hL584
  rw [pick15] at hs0
  obtain ⟨L624, hL624, hs0⟩ := memRegion_words' (s0.sp - 624#64) 5 (by norm_num) hs0
  obtain ⟨bb_0, bb_1, bb_2, bb_3, bb_4, rfl⟩ := list5 L624 hL624
  rw [pick16] at hs0
  obtain ⟨L664, hL664, hs0⟩ := memRegion_words' (s0.sp - 664#64) 5 (by norm_num) hs0
  obtain ⟨aa_0, aa_1, aa_2, aa_3, aa_4, rfl⟩ := list5 L664 hL664
  rw [pick17] at hs0
  obtain ⟨L704, hL704, hs0⟩ := memRegion_words' (s0.sp - 704#64) 5 (by norm_num) hs0
  obtain ⟨d_0, d_1, d_2, d_3, d_4, rfl⟩ := list5 L704 hL704
  rw [pick18] at hs0
  obtain ⟨L744, hL744, hs0⟩ := memRegion_words' (s0.sp - 744#64) 5 (by norm_num) hs0
  obtain ⟨c_0, c_1, c_2, c_3, c_4, rfl⟩ := list5 L744 hL744
  rw [pick19] at hs0
  obtain ⟨L784, hL784, hs0⟩ := memRegion_words' (s0.sp - 784#64) 5 (by norm_num) hs0
  obtain ⟨b_0, b_1, b_2, b_3, b_4, rfl⟩ := list5 L784 hL784
  rw [pick20] at hs0
  obtain ⟨L824, hL824, hs0⟩ := memRegion_words' (s0.sp - 824#64) 5 (by norm_num) hs0
  obtain ⟨a_0, a_1, a_2, a_3, a_4, rfl⟩ := list5 L824 hL824
  rw [pick21] at hs0
  obtain ⟨L832, hL832, hs0⟩ := memRegion_words' (s0.sp - 832#64) 1 (by norm_num) hs0
  obtain ⟨g0, rfl⟩ := list1 L832 hL832
  rw [s1056] at hs0
  rw [pick26] at hs0
  rw [pick26] at hs0
  rw [pick26] at hs0
  rw [pick26] at hs0
  rw [pick26] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick25] at hs0
  rw [pick26] at hs0
  have hs : s0.mem ⊨ ((s0.sp - 96#64) ↦₆₄* [sv0, sv1, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11]) ∗ ((s0.sp - 832#64) ↦₆₄* [g0]) ∗ ((s0.sp - 824#64) ↦₆₄* [a_0, a_1, a_2, a_3, a_4]) ∗ ((s0.sp - 784#64) ↦₆₄* [b_0, b_1, b_2, b_3, b_4]) ∗ ((s0.sp - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((s0.sp - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((s0.sp - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((s0.sp - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((s0.sp - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((s0.sp - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((s0.sp - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((s0.sp - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((s0.sp - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((s0.sp - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((s0.sp - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((s0.sp - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((s0.sp - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((s0.sp - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((s0.sp - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((s0.sp - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((s0.sp - 104#64) ↦₆₄* [g1]) ∗ memRegion (s0.sp - 832#64 - 224#64) 224 ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ R := hs0
  clear hs0
  obtain ⟨sf1, st1, hrun1, hpc1, hsp1, hv1, t144, t164, t76, t96, t100, t120, t68, t188, t172, t176, t180, t156, t168, t160, t72, t84, t80, t104, t112, t136, t108, t132, t124, t140, t148, t152, C1⟩ :=
    X25519Dalek.differentialAddAndDouble_0_192 hP hCL hal' hPU hPW hQU hQW hub hrun hpc rfl hr0 hr1 hr2 hs
  have hCL1 := libCodeLoaded_keepsFrozen hCL (X25519Dalek.steps_keepsFrozen_v2 st1)
  obtain ⟨sf2, st2, hrun2, hpc2, hsp2, hv2, t316, t328, t324, t336, t348, t232, t228, t248, t256, t276, t344, t304, t332, t308, t280, C2⟩ :=
    X25519Dalek.differentialAddAndDouble_192_364 hP hCL1 hal' hPU hPW hQU hQW hub hrun1 hpc1 hsp1 (C1.1) (C1.2.1) (C1.2.2.1) (C1.2.2.2.1) (C1.2.2.2.2.1) (C1.2.2.2.2.2.1) (C1.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hCL2 := libCodeLoaded_keepsFrozen hCL1 (X25519Dalek.steps_keepsFrozen_v2 st2)
  obtain ⟨sf3, st3, hrun3, hpc3, hsp3, hv3, o79, o80, o81, o82, o83, o64, o65, o66, o67, o68, C3⟩ :=
    X25519Dalek.differentialAddAndDouble_364_384 hP hCL2 hal' hPU hPW hQU hQW hub hrun2 hpc2 hsp2 (C2.1) (C2.2.1) (C2.2.2.1) (C2.2.2.2.1) (C2.2.2.2.2.1) (C2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hCL3 := libCodeLoaded_keepsFrozen hCL2 (X25519Dalek.steps_keepsFrozen_v2 st3)
  obtain ⟨sf4, st4, hrun4, hpc4, hsp4, hv4, o118, o119, o120, o121, o122, o103, o104, o105, o106, o107, t452, t476, t488, t492, t484, C4⟩ :=
    X25519Dalek.differentialAddAndDouble_384_532 hP hCL3 hal' hPU hPW hQU hQW hub hrun3 hpc3 hsp3 (C3.1) (C3.2.1) (C3.2.2.1) (C3.2.2.2.1) (C3.2.2.2.2.1) (C3.2.2.2.2.2.1) (C3.2.2.2.2.2.2.1) (C3.2.2.2.2.2.2.2.1) (C3.2.2.2.2.2.2.2.2.1) (C3.2.2.2.2.2.2.2.2.2.1) (C3.2.2.2.2.2.2.2.2.2.2.1) (C3.2.2.2.2.2.2.2.2.2.2.2.1) (C3.2.2.2.2.2.2.2.2.2.2.2.2.1) (C3.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hCL4 := libCodeLoaded_keepsFrozen hCL3 (X25519Dalek.steps_keepsFrozen_v2 st4)
  obtain ⟨sf5, st5, hrun5, hpc5, hsp5, hv5, t632, t644, t660, t676, t680, t560, t564, t584, t588, t616, t672, t648, t656, t652, t600, C5⟩ :=
    X25519Dalek.differentialAddAndDouble_532_696 hP hCL4 hal' hPU hPW hQU hQW hub hrun4 hpc4 hsp4 (C4.1) (C4.2.1) (C4.2.2.1) (C4.2.2.2.1) (C4.2.2.2.2.1) (C4.2.2.2.2.2.1) (C4.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hCL5 := libCodeLoaded_keepsFrozen hCL4 (X25519Dalek.steps_keepsFrozen_v2 st5)
  obtain ⟨sf6, st6, hrun6, hpc6, hsp6, hv6, o166, o167, o168, o169, o170, o151, o152, o153, o154, o155, C6⟩ :=
    X25519Dalek.differentialAddAndDouble_696_716 hP hCL5 hal' hPU hPW hQU hQW hub hrun5 hpc5 hsp5 (C5.1) (C5.2.1) (C5.2.2.1) (C5.2.2.2.1) (C5.2.2.2.2.1) (C5.2.2.2.2.2.1) (C5.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hCL6 := libCodeLoaded_keepsFrozen hCL5 (X25519Dalek.steps_keepsFrozen_v2 st6)
  obtain ⟨sf7, st7, hrun7, hpc7, hsp7, hv7, C7⟩ :=
    X25519Dalek.differentialAddAndDouble_716_724 hP hCL6 hal' hPU hPW hQU hQW hub hrun6 hpc6 hsp6 (C6.1) (C6.2.1) (C6.2.2.1) (C6.2.2.2.1) (C6.2.2.2.2.1) (C6.2.2.2.2.2.1) (C6.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hCL7 := libCodeLoaded_keepsFrozen hCL6 (X25519Dalek.steps_keepsFrozen_v2 st7)
  obtain ⟨sf8, st8, hrun8, hpc8, hsp8, hv8, o196, o197, o198, o199, o200, o181, o182, o183, o184, o185, C8⟩ :=
    X25519Dalek.differentialAddAndDouble_724_752 hP hCL7 hal' hPU hPW hQU hQW hub hrun7 hpc7 hsp7 (C7.1) (C7.2.1) (C7.2.2.1) (C7.2.2.2.1) (C7.2.2.2.2.1) (C7.2.2.2.2.2.1) (C7.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hCL8 := libCodeLoaded_keepsFrozen hCL7 (X25519Dalek.steps_keepsFrozen_v2 st8)
  obtain ⟨sf9, st9, hrun9, hpc9, hsp9, hv9, o235, o236, o237, o238, o239, t768, t772, t784, t788, t792, o220, o221, o222, o223, o224, C9⟩ :=
    X25519Dalek.differentialAddAndDouble_752_828 hP hCL8 hal' hPU hPW hQU hQW hub hrun8 hpc8 hsp8 (C8.1) (C8.2.1) (C8.2.2.1) (C8.2.2.2.1) (C8.2.2.2.2.1) (C8.2.2.2.2.2.1) (C8.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hCL9 := libCodeLoaded_keepsFrozen hCL8 (X25519Dalek.steps_keepsFrozen_v2 st9)
  obtain ⟨sf10, st10, hrun10, hpc10, hsp10, hv10, C10⟩ :=
    X25519Dalek.differentialAddAndDouble_828_ret hP hCL9 hal' hPU hPW hQU hQW hub hrun9 hpc9 hsp9 (C9.1) (C9.2.1) (C9.2.2.1) (C9.2.2.2.1) (C9.2.2.2.2.1) (C9.2.2.2.2.2.1) (C9.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hCL10 := libCodeLoaded_keepsFrozen hCL9 (X25519Dalek.steps_keepsFrozen_v2 st10)
  refine ⟨sf10, Steps.trans' st1 (Steps.trans' st2 (Steps.trans' st3 (Steps.trans' st4 (Steps.trans' st5 (Steps.trans' st6 (Steps.trans' st7 (Steps.trans' st8 (Steps.trans' st9 (st10))))))))), ?_⟩
  left
  refine ⟨⟨?_, hsp10, hrun10⟩, ⟨hsp10, ?_⟩, ?_⟩
  · rw [hpc10, readGpr_eq s0 30#5 (by decide)]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hv10.trans (hv9.trans (hv8.trans (hv7.trans (hv6.trans (hv5.trans (hv4.trans (hv3.trans (hv2.trans (hv1)))))))))⟩
    · rw [readGpr_eq _ _ (by decide), readGpr_eq _ _ (by decide)]; exact (C10.1)
    · rw [readGpr_eq _ _ (by decide), readGpr_eq _ _ (by decide)]; exact (C10.2.1)
    · rw [readGpr_eq _ _ (by decide), readGpr_eq _ _ (by decide)]; exact (C10.2.2.1)
    · rw [readGpr_eq _ _ (by decide), readGpr_eq _ _ (by decide)]; exact (C10.2.2.2.1)
    · rw [readGpr_eq _ _ (by decide), readGpr_eq _ _ (by decide)]; exact (C10.2.2.2.2.1)
    · rw [readGpr_eq _ _ (by decide), readGpr_eq _ _ (by decide)]; exact (C10.2.2.2.2.2.1)
    · rw [readGpr_eq _ _ (by decide), readGpr_eq _ _ (by decide)]; exact (C10.2.2.2.2.2.2.1)
    · rw [readGpr_eq _ _ (by decide), readGpr_eq _ _ (by decide)]; exact (C10.2.2.2.2.2.2.2.1)
    · rw [readGpr_eq _ _ (by decide), readGpr_eq _ _ (by decide)]; exact (C10.2.2.2.2.2.2.2.2.1)
    · rw [readGpr_eq _ _ (by decide), readGpr_eq _ _ (by decide)]; exact (C10.2.2.2.2.2.2.2.2.2.1)
    · rw [readGpr_eq _ _ (by decide), readGpr_eq _ _ (by decide)]; exact (C10.2.2.2.2.2.2.2.2.2.2.1)
  simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, stackFrame, hsp10]
  rw [← words_eq_bytes]
  have hA24E := (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  rw [a24_val] at hA24E
  have hmath := dad_math (fe51Val p0 p1 p2 p3 p4) (fe51Val p5 p6 p7 p8 p9) (fe51Val q0 q1 q2 q3 q4) (fe51Val q5 q6 q7 q8 q9) (fe51Val uw0 uw1 uw2 uw3 uw4) (fe51Val t76 t96 t100 t120 t68) (fe51Val t144 t164 t172 t180 t188) (fe51Val t232 t228 t248 t256 t276) (fe51Val t316 t328 t324 t336 t348) (fe51Val o64 o65 o66 o67 o68) (fe51Val o79 o80 o81 o82 o83) (fe51Val o103 o104 o105 o106 o107) (fe51Val o118 o119 o120 o121 o122) (fe51Val t452 t476 t488 t492 t484) (fe51Val t560 t564 t584 t588 t616) (fe51Val t632 t644 t660 t676 t680) (fe51Val o151 o152 o153 o154 o155) (fe51Val o166 o167 o168 o169 o170) (fe51Val o181 o182 o183 o184 o185) (fe51Val o196 o197 o198 o199 o200) (fe51Val t768 t772 t784 t788 t792) (fe51Val o220 o221 o222 o223 o224) (fe51Val o235 o236 o237 o238 o239) (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2 (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2 (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2 (C2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2 (C3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2 (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2 (C5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2 (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) hA24E (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2 (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have hφ : montProjBounded ([o196, o197, o198, o199, o200, o220, o221, o222, o223, o224].flatMap unpack64) (2 ^ 52) ∧ montProjBounded ([o151, o152, o153, o154, o155, o235, o236, o237, o238, o239].flatMap unpack64) (2 ^ 52) ∧
      montProjOfBytes ([o196, o197, o198, o199, o200, o220, o221, o222, o223, o224].flatMap unpack64) = (montDiffAddAndDouble (fe51ValOfBytes ([uw0, uw1, uw2, uw3, uw4].flatMap unpack64) % p25519)
        (montProjOfBytes ([p0, p1, p2, p3, p4, p5, p6, p7, p8, p9].flatMap unpack64))
        (montProjOfBytes ([q0, q1, q2, q3, q4, q5, q6, q7, q8, q9].flatMap unpack64))).fst ∧
      montProjOfBytes ([o151, o152, o153, o154, o155, o235, o236, o237, o238, o239].flatMap unpack64) = (montDiffAddAndDouble (fe51ValOfBytes ([uw0, uw1, uw2, uw3, uw4].flatMap unpack64) % p25519)
        (montProjOfBytes ([p0, p1, p2, p3, p4, p5, p6, p7, p8, p9].flatMap unpack64))
        (montProjOfBytes ([q0, q1, q2, q3, q4, q5, q6, q7, q8, q9].flatMap unpack64))).snd := by
    simp only [montProj_words, valw]
    rw [hmath]
    refine ⟨montb_of_words o196 o197 o198 o199 o200 o220 o221 o222 o223 o224 _ ((lbw _ _ _ _ _ _).mpr (C8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)) ((lbw _ _ _ _ _ _).mpr (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)), montb_of_words o151 o152 o153 o154 o155 o235 o236 o237 o238 o239 _ ((lbw _ _ _ _ _ _).mpr (C6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)) ((lbw _ _ _ _ _ _).mpr (C9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)), rfl, rfl⟩
  refine post_intro ([o196, o197, o198, o199, o200, o220, o221, o222, o223, o224].flatMap unpack64) ([o151, o152, o153, o154, o155, o235, o236, o237, o238, o239].flatMap unpack64) ?_
  rw [← words_eq_bytes, ← words_eq_bytes]
  have hfin := sat_pure_sep.mpr ⟨hφ, C10.2.2.2.2.2.2.2.2.2.2.2⟩
  exact Satisfies.of_eq hfin (by ac_rfl)

end X25519Dalek.LP

namespace X25519Dalek

theorem fnOk_differential_add_and_double_v2_dev :
    fnOk "curve25519_dalek::montgomery::differential_add_and_double" montDiffAddAndDoubleSpec :=
  LP.dad_ok

end X25519Dalek

end
end

section
open X25519Dalek

theorem solution :
    fnOk
      "curve25519_dalek::montgomery::differential_add_and_double"
      montDiffAddAndDoubleSpec := by
  apply X25519Dalek.fnOk_differential_add_and_double_v2_dev <;> assumption

end
