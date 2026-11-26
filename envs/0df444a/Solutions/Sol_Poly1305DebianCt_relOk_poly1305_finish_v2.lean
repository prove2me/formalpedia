-- Prove2me | solution 1 for Poly1305DebianCt.relOk_poly1305_finish_v2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-26T21:09:53.947216+00:00
-- url     : https://prove2.me/submissions/f66d2ac3-852f-4478-b855-6a42f9ce9cb7

import Definitions.Def_Poly1305DebianCt_PlacedObj
import Definitions.Def_Poly1305DebianCt_Spec
import Mathlib.Tactic.IntervalCases
import Definitions.Def_Link_LinkOk
import Theorems.Thm_Arm64Facts_steps_codeLoaded_v2
import Definitions.Def_Arm64_Leakage
import Mathlib.Tactic.Ring
import Definitions.Def_Poly1305Libsodium_Spec
import Mathlib.Tactic.ClearExcept

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

namespace Poly1305DebianCtFw
open Poly1305DebianCt

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

/-- Register reads of the entry state, as `mkS` sees them. -/
theorem readGpr_eq (s : State) (i : BitVec 5) (h : i ≠ 31#5) :
    s.readReg64 (.gpr i) = s.regs.regs i := by
  simp [State.readReg64, RegFile.read, h]

end Poly1305DebianCtFw

end
end

section
section
/-! # Execution by backward chaining, and instruction fetch in the placed libsodium library

`P pl ex` is the placed program with hook table `ex`. No hook has its entry point inside the text
block (`hook_none_in`), so inside the block `Step` is fetch-and-execute. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFw
open Poly1305DebianCt

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj

abbrev P (pl : Placement) (ex : String → Option (State → State)) : Program :=
  libsodiumDebianOnetimeauthCtLib.program pl ex

/-! ## Reaching a final state -/

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
theorem code_length : libsodiumDebianOnetimeauthCtPlacedCode.length = 2324 := by rfl

theorem patched_length (pl : Placement) : (libsodiumDebianOnetimeauthCtText.patched pl).length = 2324 := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE]
  show (List.map (fun _ => 4) (List.range (libsodiumDebianOnetimeauthCtPlacedCode.length / 4))).sum = 2324
  rw [code_length]; rfl

theorem stub_far {pl : Placement} (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl) (e : String)
    (he : e ∈ libsodiumDebianOnetimeauthCtLib.text.externs) : 2324 ≤ (pl.ρ e - pl.base).toNat := by
  have := (hP.text.externs_ok e he).2
  rwa [show libsodiumDebianOnetimeauthCtLib.text.code.length = 2324 from code_length] at this

/-- No hook has its entry point inside the text block. -/
theorem hook_none_in {pl : Placement} (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    (ex : String → Option (State → State)) {off : Nat} (hoff : off < 2324) :
    (P pl ex).externAt? (pl.base + BitVec.ofNat 64 off) = none := by
  have e : (pl.base + BitVec.ofNat 64 off - pl.base).toNat = off := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  simp only [Program.externAt?, Program.hookAtOff?, P, PlacedLib.program, e]
  have h1 : (libsodiumDebianOnetimeauthCtLib.text.externs.map fun e => (e, (pl.ρ e - pl.base).toNat)).findSome?
      (fun (n, o) => if o == off then ex n else none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro x hx
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
    have := stub_far hP e' he'
    have hne : ((pl.ρ e' - pl.base).toNat == off) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp only [hne, Bool.false_eq_true, ite_false]
  have h2 : libsodiumDebianOnetimeauthCtLib.text.symbols.findSome?
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
    (hL : Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthCtLib pl ex) (e : String)
    (he : e ∈ Link.PlacedLib.externFns libsodiumDebianOnetimeauthCtLib) :
    (P pl ex).externAt? (pl.ρ e) = ex e := by
  have hfns : Link.PlacedLib.externFns libsodiumDebianOnetimeauthCtLib =
      libsodiumDebianOnetimeauthCtLib.text.externs := by decide
  have h := findSome_stub hL.1 e he libsodiumDebianOnetimeauthCtLib.text.externs
    (fun x hx => by rw [hfns]; exact hx)
  have hany : libsodiumDebianOnetimeauthCtLib.text.externs.any
      (fun e' => (pl.ρ e' - pl.base).toNat == (pl.ρ e - pl.base).toNat) = true := by
    rw [List.any_eq_true]; exact ⟨e, by rw [← hfns]; exact he, by simp⟩
  rw [hany, if_pos rfl] at h
  have hdef : (P pl ex).externAt? (pl.ρ e) =
      ((libsodiumDebianOnetimeauthCtLib.text.externs.map fun e' => (e', (pl.ρ e' - pl.base).toNat)).findSome?
        (fun (n, o) => if o == (pl.ρ e - pl.base).toNat then ex n else none)).or
      (libsodiumDebianOnetimeauthCtLib.text.symbols.findSome?
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
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324) (hk : k < 4) :
    m.read8 (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      (libsodiumDebianOnetimeauthCtText.patchedWord pl off).extractLsb' (8 * k) 8 ∧
    m.perm (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (P pl ex).code.length = 2324 := patched_length pl
  have h := codeLoaded_cell hCL (off + k) (by omega)
  have ha : pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
      (P pl ex).base + BitVec.ofNat 64 (off + k) := by
    show _ = pl.base + _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  refine ⟨?_, h.2⟩
  rw [h.1]
  have ht := take4_drop_patched (blk := libsodiumDebianOnetimeauthCtText) (pl := pl) hal
    (by rw [show libsodiumDebianOnetimeauthCtText.code = libsodiumDebianOnetimeauthCtPlacedCode from rfl, code_length]; exact hlen)
  have e1 : (P pl ex).code[off + k]'(by omega) =
      (((libsodiumDebianOnetimeauthCtText.patched pl).drop off).take 4)[k]'(by
        simp [List.length_take, List.length_drop, patched_length]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + i < 32 := by omega
  simp [hi, this]; omega

theorem fetch_word {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
    (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    (hCL : (P pl ex).CodeLoaded m) {off : Nat} (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324) :
    (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (libsodiumDebianOnetimeauthCtText.patchedWord pl off) := by
  have hb4 : pl.base.toNat % 4 = 0 := by
    have := hP.text.base_aligned
    simp [libsodiumDebianOnetimeauthCtLib, libsodiumDebianOnetimeauthCtText] at this; omega
  have hnw : pl.base.toNat + 2324 ≤ 2 ^ 64 := by
    have := hP.text.no_wrap
    have hl : libsodiumDebianOnetimeauthCtText.code.length = 2324 := code_length
    rw [show libsodiumDebianOnetimeauthCtLib.text = libsodiumDebianOnetimeauthCtText from rfl, hl] at this
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
  simp only [Program.fetchMem, hook_none_in hP ex (show off < 2324 by omega), Option.isSome_none,
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
    (h : libsodiumDebianOnetimeauthCtText.relocAt? off = none) :
    libsodiumDebianOnetimeauthCtText.patchedWord pl off = libsodiumDebianOnetimeauthCtText.wordAt off := by
  simp [CodeBlock.patchedWord, h]

end Poly1305DebianCtFw

end
end

section
section
/-! # One lemma per instruction shape of `poly1305_finish`, on abstract states `mkS`

Some lemmas are copied from the x25519 `G` tree (`Solutions/X25519DalekField/G/Steps.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFw
open Poly1305DebianCt

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

end Poly1305DebianCtFw

end
end

section
section
/-! # 64-bit reads and writes inside owned byte lists; stack regions

`memRegion_split`, `memRegion_merge`, `pack64` and `unpack64_pack64` are copied from the x25519
`G` tree (`Solutions/X25519DalekField/G/Mem.lean`, `Solutions/X25519DalekEdwards/Dbl/Frame.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFw
open Poly1305DebianCt

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

end Poly1305DebianCtFw

end
end

section
section
/-! # More instruction shapes, small frames, and calling a function through its contract -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFw
open Poly1305DebianCt

open Arm64 Arm64.Obj

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_hint (k : BitVec 7) :
    execInstWithSvc svc (.hint k) (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) r sp ps m v := by
  simp [execInstWithSvc]

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

theorem ex_cmp_reg (n k : BitVec 5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .SUBS .xzr (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp (AddWithCarry64 (r n) (~~~(r k)) true).2 m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, shiftVal, shift64, hn, hk]

end exec

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

theorem readGpr_unfold (s : State) (i : BitVec 5) :
    s.readReg64 (.gpr i) = if i = 31#5 then 0#64 else s.regs.regs i := by
  simp [State.readReg64, RegFile.read]

theorem mkS_vregs' (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64)
    (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128) :
    (mkS s0 pc r sp ps m v).vregs = ⟨v⟩ := rfl

theorem mkS_regs' (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64)
    (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128) :
    (mkS s0 pc r sp ps m v).regs = ⟨r⟩ := rfl

/-! ## Two-cell frames -/

/-! ## Stepping, and calls -/

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

end Poly1305DebianCtFw

end
end

section
section
/-! # Two runs in lock step: the rules behind every constant-time proof of this mission

`Leakage.ObsEquiv prog arity stop₁ stop₂ s₁ s₂` says the runs from `s₁` and `s₂` reveal the same
observations and stop together. It is proved backwards, one step of both runs at a time:

* `oe_stop`: both runs have stopped;
* `oe_exec`: both runs fetch the same instruction at the same `pc`, it reveals the same values in
  both (`leakedValues`), and the successors are again observationally equivalent;
* `oe_hook`: both runs enter the same hooked function with the same revealed arguments, and the
  hook's results are observationally equivalent;
* `ct_of_rel`: a lemma of the shape "for every pair of related entry states and every continuation
  that is fine on related return states, the pair is fine" gives `ct_subroutine_ok`.

Stop conditions only need to agree on states with equal `pc`, `sp` and status (`StopCompat`);
`SubroutineStop a₁`, `SubroutineStop a₂` do when `a₁`, `a₂` agree on `lr` and `sp`
(`stopCompat_sub`). Loops are plain induction over the iteration index, and a call to a function of
the library is the callee's relational lemma applied with the caller's continuation. -/

set_option autoImplicit false

namespace Poly1305DebianCtFw

open Arm64 Leakage

/-! ## Determinism of a step -/

theorem externAt_none_of_fetch {p : Program} {m : Memory} {pc : BitVec 64} {i : Instr}
    (h : p.fetchMem m pc = some i) : p.externAt? pc = none := by
  unfold Program.fetchMem at h
  cases hx : p.externAt? pc with
  | none => rfl
  | some f => simp [hx] at h

theorem fetch_none_of_extern {p : Program} {m : Memory} {pc : BitVec 64} {f : State → State}
    (h : p.externAt? pc = some f) : p.fetchMem m pc = none := by
  unfold Program.fetchMem; simp [h]

theorem step_exec_eq {p : Program} {s s' : State} {i : Instr}
    (hf : p.fetchMem s.mem s.pc = some i) (hs : Step p s s') : s' = p.evalInst i s := by
  cases hs with
  | exec _ h_fetch => rw [hf] at h_fetch; cases h_fetch; rfl
  | halt_unmapped _ h_fetch => rw [hf] at h_fetch; cases h_fetch
  | externHook _ h_ext => rw [externAt_none_of_fetch hf] at h_ext; cases h_ext
  | extern_fault _ h_ext => rw [externAt_none_of_fetch hf] at h_ext; cases h_ext

theorem step_hook_eq {p : Program} {s s' : State} {f : State → State}
    (he : p.externAt? s.pc = some f) (hk : s.mem.KeepsFrozen (f s).mem)
    (hy : (f s).symtab = s.symtab) (hs : Step p s s') : s' = f s := by
  cases hs with
  | exec _ h_fetch => rw [fetch_none_of_extern he] at h_fetch; cases h_fetch
  | halt_unmapped _ _ h_ext => rw [he] at h_ext; cases h_ext
  | externHook _ h_ext => rw [he] at h_ext; cases h_ext; rfl
  | extern_fault _ h_ext h_nkeep => rw [he] at h_ext; cases h_ext; exact absurd ⟨hk, hy⟩ h_nkeep

/-- `Step` is deterministic. -/
theorem step_det {p : Program} {s a b : State} (ha : Step p s a) (hb : Step p s b) : a = b := by
  cases ha with
  | exec _ hf => exact (step_exec_eq hf hb).symm
  | halt_unmapped hr hf hx =>
    cases hb with
    | exec _ hf' => rw [hf] at hf'; cases hf'
    | halt_unmapped => rfl
    | externHook _ hx' => rw [hx] at hx'; cases hx'
    | extern_fault _ hx' => rw [hx] at hx'; cases hx'
  | externHook _ hx hk hy => exact (step_hook_eq hx hk hy hb).symm
  | extern_fault _ hx hn =>
    cases hb with
    | exec _ hf' => rw [fetch_none_of_extern hx] at hf'; cases hf'
    | halt_unmapped _ _ hx' => rw [hx] at hx'; cases hx'
    | externHook _ hx' hk hy => rw [hx] at hx'; cases hx'; exact absurd ⟨hk, hy⟩ hn
    | extern_fault _ hx' => rw [hx] at hx'

/-! ## The observation of one step -/

theorem hookName_none {p : Program} {pc : BitVec 64} (h : p.externAt? pc = none) :
    hookName? p pc = none := by
  unfold Program.externAt? Program.hookAtOff? at h
  rw [Option.or_eq_none_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [List.findSome?_eq_none_iff] at h1 h2
  unfold hookName?
  rw [Option.or_eq_none_iff, List.findSome?_eq_none_iff, List.findSome?_eq_none_iff]
  constructor
  · rintro ⟨n, o⟩ hx
    have := h1 ⟨n, o⟩ hx
    by_cases ho : o = (pc - p.base).toNat <;> simp_all
  · rintro ⟨n, o⟩ hx
    have := h2 ⟨n, o⟩ hx
    by_cases ho : o = (pc - p.base).toNat <;> simp_all

theorem stepObs_exec {p : Program} {ar : String → Nat} {s : State} {i : Instr}
    (hf : p.fetchMem s.mem s.pc = some i) : stepObs p ar s = (s.pc, leakedValues i s) := by
  unfold stepObs
  rw [hookName_none (externAt_none_of_fetch hf), hf]

/-- `args k` reads `x0 … x(k-1)`; equal argument registers below `K` and arities at most `K`
give equal revealed arguments. -/
theorem args_eq_of {ar : String → Nat} {K : Nat} (hK : ∀ n, ar n ≤ K) {s₁ s₂ : State}
    (h : ∀ i < K, s₁.readReg64 (.gpr (BitVec.ofNat 5 i)) = s₂.readReg64 (.gpr (BitVec.ofNat 5 i))) :
    ∀ n, args (ar n) s₁ = args (ar n) s₂ := by
  intro n
  unfold args
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact h i (by have := hK n; omega)

/-! ## Stop conditions -/

/-- `stop₁` and `stop₂` agree on states with equal `pc`, `sp` and status. -/
def StopCompat (stop₁ stop₂ : State → Prop) : Prop :=
  ∀ s₁ s₂ : State, s₁.pc = s₂.pc → s₁.sp = s₂.sp → s₁.status = s₂.status → (stop₁ s₁ ↔ stop₂ s₂)

/-! ## Observational equivalence, backwards -/

section rules
variable {p : Program} {ar : String → Nat} {stop₁ stop₂ : State → Prop}


/-- One step of the simulation: the stops agree, the observations agree, and each step of the
first run is matched by a step of the second to states again included. -/
theorem obsIncluded_of_step {s₁ s₂ : State} (hstop : stop₁ s₁ ↔ stop₂ s₂)
    (hobs : stepObs p ar s₁ = stepObs p ar s₂)
    (hstep : ∀ s₁', Step p s₁ s₁' → ∃ s₂', Step p s₂ s₂' ∧ ObsIncluded p ar stop₁ stop₂ s₁' s₂') :
    ObsIncluded p ar stop₁ stop₂ s₁ s₂ := by
  intro t f₁ hr
  cases hr with
  | refl => exact ⟨s₂, ObsUntil.refl s₂, hstop⟩
  | @step _ s₁' _ t' hc hs hrest =>
    obtain ⟨s₂', hs₂, hinc⟩ := hstep s₁' hs
    obtain ⟨f₂, hr₂, hiff⟩ := hinc t' f₁ hrest
    refine ⟨f₂, ?_, hiff⟩
    rw [hobs]
    exact ObsUntil.step (fun h => hc (hstop.mpr h)) hs₂ hr₂

/-- One step of each run, given as `Step` facts, with equal observations. -/
theorem oe_step (hc : StopCompat stop₁ stop₂) {s₁ s₂ t₁ t₂ : State}
    (hpc : s₁.pc = s₂.pc) (hsp : s₁.sp = s₂.sp) (hst : s₁.status = s₂.status)
    (h1 : Step p s₁ t₁) (h2 : Step p s₂ t₂)
    (hobs : stepObs p ar s₁ = stepObs p ar s₂)
    (h : ObsEquiv p ar stop₁ stop₂ t₁ t₂) : ObsEquiv p ar stop₁ stop₂ s₁ s₂ := by
  have hstop := hc s₁ s₂ hpc hsp hst
  refine ⟨obsIncluded_of_step hstop hobs ?_, obsIncluded_of_step hstop.symm hobs.symm ?_⟩
  · intro s₁' hs
    rw [step_det hs h1]
    exact ⟨_, h2, h.1⟩
  · intro s₂' hs
    rw [step_det hs h2]
    exact ⟨_, h1, h.2⟩

/-- Both runs execute instruction `i`, fetched at the same `pc`, revealing the same values. -/
theorem oe_exec (hc : StopCompat stop₁ stop₂) {s₁ s₂ : State} {i : Instr}
    (hpc : s₁.pc = s₂.pc) (hsp : s₁.sp = s₂.sp)
    (hr1 : s₁.status = .Running) (hr2 : s₂.status = .Running)
    (hf1 : p.fetchMem s₁.mem s₁.pc = some i) (hf2 : p.fetchMem s₂.mem s₂.pc = some i)
    (hl : leakedValues i s₁ = leakedValues i s₂)
    (h : ObsEquiv p ar stop₁ stop₂ (p.evalInst i s₁) (p.evalInst i s₂)) :
    ObsEquiv p ar stop₁ stop₂ s₁ s₂ := by
  have hstop := hc s₁ s₂ hpc hsp (hr1.trans hr2.symm)
  have hobs : stepObs p ar s₁ = stepObs p ar s₂ := by
    rw [stepObs_exec hf1, stepObs_exec hf2, hpc, hl]
  refine ⟨obsIncluded_of_step hstop hobs ?_, obsIncluded_of_step hstop.symm hobs.symm ?_⟩
  · intro s₁' hs
    rw [step_exec_eq hf1 hs]
    exact ⟨_, Step.exec hr2 hf2, h.1⟩
  · intro s₂' hs
    rw [step_exec_eq hf2 hs]
    exact ⟨_, Step.exec hr1 hf1, h.2⟩

theorem oe_congr {s₁ s₂ t₁ t₂ : State} (e1 : s₁ = t₁) (e2 : s₂ = t₂)
    (h : ObsEquiv p ar stop₁ stop₂ t₁ t₂) : ObsEquiv p ar stop₁ stop₂ s₁ s₂ := by
  subst e1 e2; exact h

end rules

/-! ## Observation sequences compose -/

/-! ## From a relational lemma to `ct_subroutine_ok` -/

end Poly1305DebianCtFw

end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFinish

open Arm64 Arm64.Obj Poly1305DebianCtFw

/-- The 324 bytes of `poly1305_finish` (text offsets 1056..1379), as in the code block. -/
def SL : List (BitVec 8) := [
  0x3f#8, 0x23#8, 0x03#8, 0xd5#8, 0xfd#8, 0x7b#8, 0xbe#8, 0xa9#8, 0xfd#8, 0x03#8, 0x00#8, 0x91#8, 0xf3#8, 0x53#8, 0x01#8, 0xa9#8,
  0xf4#8, 0x03#8, 0x01#8, 0xaa#8, 0xf3#8, 0x03#8, 0x00#8, 0xaa#8, 0x01#8, 0x20#8, 0x40#8, 0xf9#8, 0x61#8, 0x02#8, 0x00#8, 0xb4#8,
  0x00#8, 0x00#8, 0x01#8, 0x8b#8, 0x22#8, 0x00#8, 0x80#8, 0x52#8, 0x02#8, 0x20#8, 0x01#8, 0x39#8, 0x20#8, 0x04#8, 0x00#8, 0x91#8,
  0x1f#8, 0x3c#8, 0x00#8, 0xf1#8, 0xe8#8, 0x00#8, 0x00#8, 0x54#8, 0x20#8, 0x24#8, 0x01#8, 0x91#8, 0xe2#8, 0x01#8, 0x80#8, 0xd2#8,
  0x60#8, 0x02#8, 0x00#8, 0x8b#8, 0x42#8, 0x00#8, 0x01#8, 0xcb#8, 0x01#8, 0x00#8, 0x80#8, 0x52#8, 0x00#8, 0x00#8, 0x00#8, 0x94#8,
  0x20#8, 0x00#8, 0x80#8, 0x52#8, 0x60#8, 0x62#8, 0x01#8, 0x39#8, 0x61#8, 0x22#8, 0x01#8, 0x91#8, 0xe0#8, 0x03#8, 0x13#8, 0xaa#8,
  0x02#8, 0x02#8, 0x80#8, 0xd2#8, 0x47#8, 0xff#8, 0xff#8, 0x97#8, 0x65#8, 0x8a#8, 0x41#8, 0xa9#8, 0xa3#8, 0x00#8, 0x80#8, 0x52#8,
  0x60#8, 0x86#8, 0x42#8, 0xa9#8, 0x44#8, 0xac#8, 0x40#8, 0x92#8, 0x02#8, 0xb0#8, 0x42#8, 0x8b#8, 0x40#8, 0xa4#8, 0x40#8, 0x92#8,
  0x42#8, 0xfc#8, 0x6a#8, 0xd3#8, 0x42#8, 0x14#8, 0xa3#8, 0x9b#8, 0x45#8, 0xac#8, 0x40#8, 0x92#8, 0x82#8, 0xb0#8, 0x42#8, 0x8b#8,
  0x44#8, 0xac#8, 0x40#8, 0x92#8, 0x02#8, 0xb0#8, 0x42#8, 0x8b#8, 0x48#8, 0xa4#8, 0x40#8, 0x92#8, 0x40#8, 0xfc#8, 0x6a#8, 0xd3#8,
  0x42#8, 0x54#8, 0x56#8, 0xb2#8, 0x00#8, 0x14#8, 0xa3#8, 0x9b#8, 0x05#8, 0x00#8, 0x80#8, 0xd2#8, 0x07#8, 0xac#8, 0x40#8, 0x92#8,
  0x80#8, 0xb0#8, 0x40#8, 0x8b#8, 0xe4#8, 0x14#8, 0x00#8, 0x91#8, 0x03#8, 0xb0#8, 0x44#8, 0x8b#8, 0x42#8, 0xb0#8, 0x43#8, 0x8b#8,
  0x5f#8, 0x00#8, 0x05#8, 0xeb#8, 0xe9#8, 0xb3#8, 0x9f#8, 0xda#8, 0xe7#8, 0xfc#8, 0x82#8, 0x8a#8, 0x86#8, 0x00#8, 0x09#8, 0x8a#8,
  0x65#8, 0x00#8, 0x09#8, 0x8a#8, 0x64#8, 0x1e#8, 0x40#8, 0xf9#8, 0xc6#8, 0xac#8, 0x40#8, 0x92#8, 0xc6#8, 0x00#8, 0x07#8, 0xaa#8,
  0x03#8, 0xfc#8, 0x82#8, 0x8a#8, 0xa5#8, 0xac#8, 0x40#8, 0x92#8, 0x20#8, 0xac#8, 0x40#8, 0x92#8, 0x00#8, 0x00#8, 0x06#8, 0x8b#8,
  0x81#8, 0xb0#8, 0xc1#8, 0x93#8, 0xa3#8, 0x00#8, 0x03#8, 0xaa#8, 0x21#8, 0xac#8, 0x40#8, 0x92#8, 0x07#8, 0xfd#8, 0x82#8, 0x8a#8,
  0x21#8, 0x00#8, 0x03#8, 0x8b#8, 0x42#8, 0x00#8, 0x09#8, 0x8a#8, 0x06#8, 0xac#8, 0x40#8, 0x92#8, 0x42#8, 0x00#8, 0x07#8, 0xaa#8,
  0x20#8, 0xb0#8, 0x40#8, 0x8b#8, 0x44#8, 0x60#8, 0x44#8, 0x8b#8, 0x84#8, 0xb0#8, 0x40#8, 0x8b#8, 0x01#8, 0xac#8, 0x54#8, 0xd3#8,
  0xc0#8, 0xb0#8, 0x00#8, 0xaa#8, 0x24#8, 0x60#8, 0x04#8, 0xaa#8, 0x80#8, 0x12#8, 0x00#8, 0xa9#8, 0xe0#8, 0x03#8, 0x13#8, 0xaa#8,
  0xf3#8, 0x53#8, 0x41#8, 0xa9#8, 0x01#8, 0x0c#8, 0x80#8, 0xd2#8, 0xfd#8, 0x7b#8, 0xc2#8, 0xa8#8, 0xbf#8, 0x23#8, 0x03#8, 0xd5#8,
  0x00#8, 0x00#8, 0x00#8, 0x14#8]

theorem code_slice :
    (Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedCode.drop 1056).take 324 = SL := by
  decide +kernel

theorem getD_SL (k : Nat) (hk : k < 324) :
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedCode.getD (1056 + k) 0#8 = SL.getD k 0#8 := by
  rw [← code_slice]
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hk, List.getElem?_drop]

theorem wordAt_SL (off : Nat) (h1 : 1056 ≤ off) (h2 : off + 4 ≤ 1380) :
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.wordAt off = wordOfBytesLE SL (off - 1056) := by
  obtain ⟨j, rfl⟩ : ∃ j, off = 1056 + j := ⟨off - 1056, by omega⟩
  simp only [CodeBlock.wordAt, wordOfBytesLE, Nat.add_sub_cancel_left]
  rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.code =
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedCode from rfl, getD_SL j (by omega),
    Nat.add_assoc, getD_SL (j + 1) (by omega), Nat.add_assoc, getD_SL (j + 2) (by omega),
    Nat.add_assoc, getD_SL (j + 3) (by omega)]

/-- The instruction at an unrelocated word of `poly1305_finish`. -/
theorem fw {pl : Placement} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {X : String → Option (State → State)} {m : Memory} (hCL : (P pl X).CodeLoaded m) (off : Nat)
    {I : Instr} (hal : off % 4 = 0 := by decide) (h1 : 1056 ≤ off := by decide)
    (h2 : off + 4 ≤ 1380 := by decide)
    (hr : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocAt? off = none := by decide +kernel)
    (hd : decode (wordOfBytesLE SL (off - 1056)) = some I := by decide +kernel) :
    (P pl X).fetchMem m (pl.base + BitVec.ofNat 64 off) = some I := by
  rw [fetch_word hP hCL hal (by omega), patchedWord_plain pl hr, wordAt_SL off h1 h2, hd]

section
variable {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
  (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl) (hCL : (P pl ex).CodeLoaded m)
include hP hCL

theorem f_0 : (P pl ex).fetchMem m (pl.base + 1056#64) = Arm64.Instr.hint 0x19#7 :=
  fw hP hCL 1056

theorem f_4 : (P pl ex).fetchMem m (pl.base + 1060#64) = Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xffffffffffffffe0#64) :=
  fw hP hCL 1060

theorem f_8 : (P pl ex).fetchMem m (pl.base + 1064#64) = Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.sp) 0x000#12 false :=
  fw hP hCL 1064

theorem f_c : (P pl ex).fetchMem m (pl.base + 1068#64) = Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x14#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64) :=
  fw hP hCL 1068

theorem f_10 : (P pl ex).fetchMem m (pl.base + 1072#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1072

theorem f_14 : (P pl ex).fetchMem m (pl.base + 1076#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1076

theorem f_18 : (P pl ex).fetchMem m (pl.base + 1080#64) = Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000040#64) :=
  fw hP hCL 1080

theorem f_1c : (P pl ex).fetchMem m (pl.base + 1084#64) = Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x01#5) 0x000000000000004c#64 :=
  fw hP hCL 1084

theorem f_20 : (P pl ex).fetchMem m (pl.base + 1088#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1088

theorem f_24 : (P pl ex).fetchMem m (pl.base + 1092#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x02#5) 0x0001#16 0 :=
  fw hP hCL 1092

theorem f_28 : (P pl ex).fetchMem m (pl.base + 1096#64) = Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x02#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000048#64) :=
  fw hP hCL 1096

theorem f_2c : (P pl ex).fetchMem m (pl.base + 1100#64) = Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x01#5) 0x001#12 false :=
  fw hP hCL 1100

theorem f_30 : (P pl ex).fetchMem m (pl.base + 1104#64) = Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) 0x00f#12 false :=
  fw hP hCL 1104

theorem f_34 : (P pl ex).fetchMem m (pl.base + 1108#64) = Arm64.Instr.bCond (Arm64.CondCode.HI) 0x000000000000001c#64 :=
  fw hP hCL 1108

theorem f_38 : (P pl ex).fetchMem m (pl.base + 1112#64) = Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x01#5) 0x049#12 false :=
  fw hP hCL 1112

theorem f_3c : (P pl ex).fetchMem m (pl.base + 1116#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x02#5) 0x000f#16 0 :=
  fw hP hCL 1116

theorem f_40 : (P pl ex).fetchMem m (pl.base + 1120#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1120

theorem f_44 : (P pl ex).fetchMem m (pl.base + 1124#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1124

theorem f_48 : (P pl ex).fetchMem m (pl.base + 1128#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0000#16 0 :=
  fw hP hCL 1128

theorem f_50 : (P pl ex).fetchMem m (pl.base + 1136#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x00#5) 0x0001#16 0 :=
  fw hP hCL 1136

theorem f_54 : (P pl ex).fetchMem m (pl.base + 1140#64) = Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000058#64) :=
  fw hP hCL 1140

theorem f_58 : (P pl ex).fetchMem m (pl.base + 1144#64) = Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x13#5) 0x048#12 false :=
  fw hP hCL 1144

theorem f_5c : (P pl ex).fetchMem m (pl.base + 1148#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x13#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1148

theorem f_60 : (P pl ex).fetchMem m (pl.base + 1152#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x02#5) 0x0010#16 0 :=
  fw hP hCL 1152

theorem f_64 : (P pl ex).fetchMem m (pl.base + 1156#64) = Arm64.Instr.bl 0xfffffffffffffd1c#64 :=
  fw hP hCL 1156

theorem f_68 : (P pl ex).fetchMem m (pl.base + 1160#64) = Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x02#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000018#64) :=
  fw hP hCL 1160

theorem f_6c : (P pl ex).fetchMem m (pl.base + 1164#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x03#5) 0x0005#16 0 :=
  fw hP hCL 1164

theorem f_70 : (P pl ex).fetchMem m (pl.base + 1168#64) = Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000028#64) :=
  fw hP hCL 1168

theorem f_74 : (P pl ex).fetchMem m (pl.base + 1172#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x02#5) 0x00000fffffffffff#64 :=
  fw hP hCL 1172

theorem f_78 : (P pl ex).fetchMem m (pl.base + 1176#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSR) 44 :=
  fw hP hCL 1176

theorem f_7c : (P pl ex).fetchMem m (pl.base + 1180#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) 0x000003ffffffffff#64 :=
  fw hP hCL 1180

theorem f_80 : (P pl ex).fetchMem m (pl.base + 1184#64) = Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) 42 63 :=
  fw hP hCL 1184

theorem f_84 : (P pl ex).fetchMem m (pl.base + 1188#64) = Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x05#5) :=
  fw hP hCL 1188

theorem f_88 : (P pl ex).fetchMem m (pl.base + 1192#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x02#5) 0x00000fffffffffff#64 :=
  fw hP hCL 1192

theorem f_8c : (P pl ex).fetchMem m (pl.base + 1196#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSR) 44 :=
  fw hP hCL 1196

theorem f_90 : (P pl ex).fetchMem m (pl.base + 1200#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x02#5) 0x00000fffffffffff#64 :=
  fw hP hCL 1200

theorem f_94 : (P pl ex).fetchMem m (pl.base + 1204#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSR) 44 :=
  fw hP hCL 1204

theorem f_98 : (P pl ex).fetchMem m (pl.base + 1208#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x02#5) 0x000003ffffffffff#64 :=
  fw hP hCL 1208

theorem f_9c : (P pl ex).fetchMem m (pl.base + 1212#64) = Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) 42 63 :=
  fw hP hCL 1212

theorem f_a0 : (P pl ex).fetchMem m (pl.base + 1216#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) 0xfffffc0000000000#64 :=
  fw hP hCL 1216

theorem f_a4 : (P pl ex).fetchMem m (pl.base + 1220#64) = Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x05#5) :=
  fw hP hCL 1220

theorem f_a8 : (P pl ex).fetchMem m (pl.base + 1224#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x05#5) 0x0000#16 0 :=
  fw hP hCL 1224

theorem f_ac : (P pl ex).fetchMem m (pl.base + 1228#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x00#5) 0x00000fffffffffff#64 :=
  fw hP hCL 1228

theorem f_b0 : (P pl ex).fetchMem m (pl.base + 1232#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSR) 44 :=
  fw hP hCL 1232

theorem f_b4 : (P pl ex).fetchMem m (pl.base + 1236#64) = Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x07#5) 0x005#12 false :=
  fw hP hCL 1236

theorem f_b8 : (P pl ex).fetchMem m (pl.base + 1240#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x04#5) (Arm64.ShiftType.LSR) 44 :=
  fw hP hCL 1240

theorem f_bc : (P pl ex).fetchMem m (pl.base + 1244#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSR) 44 :=
  fw hP hCL 1244

theorem f_c0 : (P pl ex).fetchMem m (pl.base + 1248#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x05#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1248

theorem f_c4 : (P pl ex).fetchMem m (pl.base + 1252#64) = Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINV) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.CondCode.LT) :=
  fw hP hCL 1252

theorem f_c8 : (P pl ex).fetchMem m (pl.base + 1256#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.ASR) 63 :=
  fw hP hCL 1256

theorem f_cc : (P pl ex).fetchMem m (pl.base + 1260#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1260

theorem f_d0 : (P pl ex).fetchMem m (pl.base + 1264#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1264

theorem f_d4 : (P pl ex).fetchMem m (pl.base + 1268#64) = Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000038#64) :=
  fw hP hCL 1268

theorem f_d8 : (P pl ex).fetchMem m (pl.base + 1272#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) 0x00000fffffffffff#64 :=
  fw hP hCL 1272

theorem f_dc : (P pl ex).fetchMem m (pl.base + 1276#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x07#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1276

theorem f_e0 : (P pl ex).fetchMem m (pl.base + 1280#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.ASR) 63 :=
  fw hP hCL 1280

theorem f_e4 : (P pl ex).fetchMem m (pl.base + 1284#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) 0x00000fffffffffff#64 :=
  fw hP hCL 1284

theorem f_e8 : (P pl ex).fetchMem m (pl.base + 1288#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x01#5) 0x00000fffffffffff#64 :=
  fw hP hCL 1288

theorem f_ec : (P pl ex).fetchMem m (pl.base + 1292#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x06#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1292

theorem f_f0 : (P pl ex).fetchMem m (pl.base + 1296#64) = Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x01#5) 44 :=
  fw hP hCL 1296

theorem f_f4 : (P pl ex).fetchMem m (pl.base + 1300#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1300

theorem f_f8 : (P pl ex).fetchMem m (pl.base + 1304#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x01#5) 0x00000fffffffffff#64 :=
  fw hP hCL 1304

theorem f_fc : (P pl ex).fetchMem m (pl.base + 1308#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.ASR) 63 :=
  fw hP hCL 1308

theorem f_100 : (P pl ex).fetchMem m (pl.base + 1312#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1312

theorem f_104 : (P pl ex).fetchMem m (pl.base + 1316#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1316

theorem f_108 : (P pl ex).fetchMem m (pl.base + 1320#64) = Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x00#5) 0x00000fffffffffff#64 :=
  fw hP hCL 1320

theorem f_10c : (P pl ex).fetchMem m (pl.base + 1324#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x07#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1324

theorem f_110 : (P pl ex).fetchMem m (pl.base + 1328#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSR) 44 :=
  fw hP hCL 1328

theorem f_114 : (P pl ex).fetchMem m (pl.base + 1332#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) (Arm64.ShiftType.LSR) 24 :=
  fw hP hCL 1332

theorem f_118 : (P pl ex).fetchMem m (pl.base + 1336#64) = Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSR) 44 :=
  fw hP hCL 1336

theorem f_11c : (P pl ex).fetchMem m (pl.base + 1340#64) = Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x00#5) 20 43 :=
  fw hP hCL 1340

theorem f_120 : (P pl ex).fetchMem m (pl.base + 1344#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 44 :=
  fw hP hCL 1344

theorem f_124 : (P pl ex).fetchMem m (pl.base + 1348#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x04#5) (Arm64.ShiftType.LSL) 24 :=
  fw hP hCL 1348

theorem f_128 : (P pl ex).fetchMem m (pl.base + 1352#64) = Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x14#5) 0x0000000000000000#64) :=
  fw hP hCL 1352

theorem f_12c : (P pl ex).fetchMem m (pl.base + 1356#64) = Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x13#5) (Arm64.ShiftType.LSL) 0 :=
  fw hP hCL 1356

theorem f_130 : (P pl ex).fetchMem m (pl.base + 1360#64) = Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x14#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64) :=
  fw hP hCL 1360

theorem f_134 : (P pl ex).fetchMem m (pl.base + 1364#64) = Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0060#16 0 :=
  fw hP hCL 1364

theorem f_138 : (P pl ex).fetchMem m (pl.base + 1368#64) = Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000020#64) :=
  fw hP hCL 1368

theorem f_13c : (P pl ex).fetchMem m (pl.base + 1372#64) = Arm64.Instr.hint 0x1d#7 :=
  fw hP hCL 1372

end

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
  have hn := D.isLt
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  simp only [BitVec.getLsbD]
  by_cases hc : D.toNat < 2 ^ 27
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) hi1)),
      Nat.testBit_lt_two_pow hc]
  · have hq : D.toNat / 2 ^ 27 = 2 ^ 37 - 1 := by split at h1 <;> split at h2 <;> omega
    have key : ∀ j, 27 ≤ j → j < 64 → D.toNat.testBit j = true := by
      intro j hj1 hj2
      have e : D.toNat.testBit j = (D.toNat / 2 ^ 27).testBit (j - 27) := by
        rw [Nat.testBit_div_two_pow]; congr 1; omega
      rw [e, hq, Nat.testBit_two_pow_sub_one]
      simp only [decide_eq_true_eq]; omega
    rw [key i hi1 hi2, key 27 le_rfl (by omega)]

theorem lo_bits2 (D : BitVec 64) (h : D.toNat % 4 = 0) : ∀ i, i < 2 → D.getLsbD i = false := by
  intro i hi
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize D.toNat = n at h ⊢
  interval_cases i <;> simp <;> omega

/-- The offset field of a relocated branch word decodes to the branch distance. -/
theorem hoff (t : BitVec 32) {P T : BitVec 64} (hr : BranchInRange P T) :
    ((((t &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32)).extractLsb' 0 26).signExtend 64)
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
  rw [branchWord, decode_b_class _ hm, h31, if_pos rfl, hoff _ hr]

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
  rw [branchWord, decode_b_class _ hm, h31]; simp only [Bool.false_eq_true, if_false, hoff _ hr]

abbrev rBl : RelocEntry := { off := 1132, kind := .call26, sym := "memset" }
abbrev rB : RelocEntry := { off := 1376, kind := .jump26, sym := "sodium_memzero" }

theorem rBl_mem : rBl ∈ Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text.relocs := by decide
theorem rB_mem : rB ∈ Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text.relocs := by decide

theorem relocTarget_bl (pl : Placement) :
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocTarget pl 1132 rBl = pl.ρ "memset" := by
  have hb : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.b2bNext? rBl = none := by decide
  have hl : lookup "memset" Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.symbols = none := by decide
  simp only [CodeBlock.relocTarget, hb, ite_self, CodeBlock.target, CodeBlock.resolve, hl]
  simp [addSignedAddr]

theorem relocTarget_b (pl : Placement) :
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocTarget pl 1376 rB = pl.ρ "sodium_memzero" := by
  have hb : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.b2bNext? rB = none := by decide
  have hl : lookup "sodium_memzero" Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.symbols = none := by decide
  simp only [CodeBlock.relocTarget, hb, ite_self, CodeBlock.target, CodeBlock.resolve, hl]
  simp [addSignedAddr]

section
variable {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
  (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl) (hCL : (P pl ex).CodeLoaded m)
include hP hCL

theorem f_4c : (P pl ex).fetchMem m (pl.base + 1132#64) =
    some (.bl (pl.ρ "memset" - (pl.base + 1132#64))) := by
  have hrange : BranchInRange (pl.base + BitVec.ofNat 64 1132) (pl.ρ "memset") := by
    have h := (hP.text.relocs_ok _ rBl_mem).2.2
    rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text = Poly1305DebianCt.libsodiumDebianOnetimeauthCtText from rfl, relocTarget_bl] at h
    exact h
  have hpw : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl 1132 =
      branchWord 0x94000000#32 (pl.base + BitVec.ofNat 64 1132) (pl.ρ "memset") := by
    have hr : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocAt? 1132 = some rBl := by decide
    have hw : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.wordAt 1132 = 0x94000000#32 := by decide +kernel
    have hx1 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxableAt 1132 = false := by decide
    have hx2 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxableAt (1132 - 4) = false := by decide
    have hr1 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxedAt pl 1132 = false := by simp [CodeBlock.relaxedAt, hx1]
    have hr2 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxedAt pl (1132 - 4) = false := by
      simp [CodeBlock.relaxedAt, hx2]
    have hu : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.undefWeakBranch pl rBl = false := by
      simp [CodeBlock.undefWeakBranch, Poly1305DebianCt.libsodiumDebianOnetimeauthCtText]
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
    rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text = Poly1305DebianCt.libsodiumDebianOnetimeauthCtText from rfl, relocTarget_b] at h
    exact h
  have hpw : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl 1376 =
      branchWord 0x14000000#32 (pl.base + BitVec.ofNat 64 1376) (pl.ρ "sodium_memzero") := by
    have hr : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocAt? 1376 = some rB := by decide
    have hw : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.wordAt 1376 = 0x14000000#32 := by decide +kernel
    have hx1 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxableAt 1376 = false := by decide
    have hx2 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxableAt (1376 - 4) = false := by decide
    have hr1 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxedAt pl 1376 = false := by simp [CodeBlock.relaxedAt, hx1]
    have hr2 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxedAt pl (1376 - 4) = false := by
      simp [CodeBlock.relaxedAt, hx2]
    have hu : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.undefWeakBranch pl rB = false := by
      simp [CodeBlock.undefWeakBranch, Poly1305DebianCt.libsodiumDebianOnetimeauthCtText]
    rw [CodeBlock.patchedWord]
    simp only [hr, hr1, hr2, hw, hu, Bool.false_eq_true, if_false, Bool.and_false,
      relocTarget_b]
    simp [RelocKind.isGotOrTlsIe, patchRelocWord]
  rw [show pl.base + 1376#64 = pl.base + BitVec.ofNat 64 1376 from rfl,
    fetch_word hP hCL (by decide) (by decide), hpw, decode_branchWord_b hrange]

end

/-! ## Instruction shapes not in the framework -/

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

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

end Poly1305DebianCtFinish

end
end

section
section
/-! # Two runs of `poly1305_finish`: step rules, register invariants, hooks

`rs` steps both runs once on abstract states `mkS`; `rk` does so and then forgets every register
except the tracked ones (`Kp`: `x19 = st`, `x20 = mac`, `x21..x28` as at entry), and the flags.
`oe_hk` crosses a hooked extern in both runs. `no_both` shows that no function meets both the
`sodium_memzero` and the `memset` contracts, so the hook reached by the tail call is never
looked up under the name `memset` (which would reveal `x2`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFinish

open Arm64 Arm64.Obj Leakage Poly1305DebianCt Poly1305DebianCtFw

theorem a4 (b : BitVec 64) (x y : Nat) (h : x + 4 = y := by decide) :
    b + BitVec.ofNat 64 x + 4#64 = b + BitVec.ofNat 64 y := by rw [pc_add, h]

/-! ## Tracked registers -/

/-- `x19 = A`, `x20 = M`, and `x21..x28` as in the entry state `c₀`. -/
def Kp (c₀ : State) (A M : BitVec 64) (q : BitVec 5 → BitVec 64) : Prop :=
  q 19#5 = A ∧ q 20#5 = M ∧
    ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat ≤ 28 → q k = c₀.readReg64 (.gpr k)

theorem Kp_upd {c₀ : State} {A M : BitVec 64} {q : BitVec 5 → BitVec 64} (h : Kp c₀ A M q)
    {d : BitVec 5} (x : BitVec 64) (hd : d.toNat < 19 ∨ 28 < d.toNat := by decide) :
    Kp c₀ A M (upd q d x) := by
  obtain ⟨h19, h20, hcs⟩ := h
  have n19 : (19#5 : BitVec 5) ≠ d := fun e => by subst e; simp at hd
  have n20 : (20#5 : BitVec 5) ≠ d := fun e => by subst e; simp at hd
  refine ⟨by rw [upd_ne _ _ n19, h19], by rw [upd_ne _ _ n20, h20], fun k h1 h2 => ?_⟩
  have nk : k ≠ d := fun e => by subst e; omega
  rw [upd_ne _ _ nk, hcs k h1 h2]

/-! ## One step of both runs -/

section rules
variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

theorem rs (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State}
    (hr1 : c₁.status = .Running) (hr2 : c₂.status = .Running)
    {pc sp sp' pc' : BitVec 64} {r₁ r₂ r₁' r₂' : BitVec 5 → BitVec 64}
    {ps₁ ps₂ ps₁' ps₂' : PState} {m₁ m₂ m₁' m₂' : Memory} {v₁ v₂ : BitVec 5 → BitVec 128}
    {i : Instr}
    (hf1 : (P pl X).fetchMem m₁ pc = some i) (hf2 : (P pl X).fetchMem m₂ pc = some i)
    (e1 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) =
      mkS c₁ pc' r₁' sp' ps₁' m₁' v₁)
    (e2 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₂ pc r₂ sp ps₂ m₂ v₂) =
      mkS c₂ pc' r₂' sp' ps₂' m₂' v₂)
    (hl : leakedValues i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) = leakedValues i (mkS c₂ pc r₂ sp ps₂ m₂ v₂))
    (h : ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pc' r₁' sp' ps₁' m₁' v₁)
      (mkS c₂ pc' r₂' sp' ps₂' m₂' v₂)) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pc r₁ sp ps₁ m₁ v₁) (mkS c₂ pc r₂ sp ps₂ m₂ v₂) :=
  oe_exec hc rfl rfl hr1 hr2 hf1 hf2 hl (by rw [Program.evalInst, Program.evalInst, e1, e2]; exact h)

/-- Instructions that reveal nothing: the leaked values agree in any two states. -/
theorem lv0 {i : Instr} {s₁ s₂ : State} (h : ∀ s, leakedValues i s = []) :
    leakedValues i s₁ = leakedValues i s₂ := by rw [h, h]

/-- One step to the next instruction, then forget all registers but `Kp`, and the flags. -/
theorem rk (hc : StopCompat stop₁ stop₂) {c₁ c₂ c₀₁ c₀₂ : State} {A M : BitVec 64}
    (hr1 : c₁.status = .Running) (hr2 : c₂.status = .Running)
    {pc sp pcn : BitVec 64} {r₁ r₂ r₁' r₂' : BitVec 5 → BitVec 64}
    {ps₁ ps₂ ps₁' ps₂' : PState} {m₁ m₂ m₁' m₂' : Memory} {v₁ v₂ : BitVec 5 → BitVec 128}
    {i : Instr}
    (hf1 : (P pl X).fetchMem m₁ pc = some i) (hf2 : (P pl X).fetchMem m₂ pc = some i)
    (e1 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) =
      mkS c₁ (pc + 4#64) r₁' sp ps₁' m₁' v₁)
    (e2 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₂ pc r₂ sp ps₂ m₂ v₂) =
      mkS c₂ (pc + 4#64) r₂' sp ps₂' m₂' v₂)
    (hl : leakedValues i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) = leakedValues i (mkS c₂ pc r₂ sp ps₂ m₂ v₂))
    (k₁ : Kp c₀₁ A M r₁') (k₂ : Kp c₀₂ A M r₂') (hpc : pc + 4#64 = pcn)
    (h : ∀ (q₁ q₂ : BitVec 5 → BitVec 64) (ρ₁ ρ₂ : PState), Kp c₀₁ A M q₁ → Kp c₀₂ A M q₂ →
      ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pcn q₁ sp ρ₁ m₁' v₁) (mkS c₂ pcn q₂ sp ρ₂ m₂' v₂)) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pc r₁ sp ps₁ m₁ v₁) (mkS c₂ pc r₂ sp ps₂ m₂ v₂) := by
  subst hpc
  exact rs hc hr1 hr2 hf1 hf2 e1 e2 hl (h _ _ _ _ k₁ k₂)

/-- The code stays loaded across a step. -/
theorem cl_exec {c : State} (hr : c.status = .Running) {pc sp pc' sp' : BitVec 64}
    {r r' : BitVec 5 → BitVec 64} {ps ps' : PState} {m m' : Memory} {v : BitVec 5 → BitVec 128}
    {i : Instr} (hf : (P pl X).fetchMem m pc = some i)
    (e : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c pc r sp ps m v) = mkS c pc' r' sp' ps' m' v)
    (H : (P pl X).CodeLoaded m) : (P pl X).CodeLoaded m' := by
  have st : Step (P pl X) (mkS c pc r sp ps m v) (mkS c pc' r' sp' ps' m' v) := by
    have := Step.exec (prog := P pl X) (s := mkS c pc r sp ps m v) hr hf
    rwa [Program.evalInst, e] at this
  exact Arm64Facts.steps_codeLoaded_v2 (Steps.step st (Steps.refl _)) H

/-! ## Hooks -/

theorem stepObs_hook_eq' {p : Program} {ar : String → Nat} {s₁ s₂ : State} {f : State → State}
    (hpc : s₁.pc = s₂.pc) (he : p.externAt? s₁.pc = some f)
    (hargs : ∀ n, hookName? p s₁.pc = some n → args (ar n) s₁ = args (ar n) s₂) :
    stepObs p ar s₁ = stepObs p ar s₂ := by
  unfold stepObs
  rw [← hpc]
  cases hn : hookName? p s₁.pc with
  | some n => simp only [hargs n hn]
  | none => simp only [fetch_none_of_extern he, fetch_none_of_extern (m := s₂.mem) he]

/-- A hook meeting `spec` in both runs; the continuation gets both outcomes and that the code is
still loaded. Only the arguments of the name the hook is looked up under must agree. -/
theorem oe_hk {α : Type} {spec : Spec α} (hc : StopCompat stop₁ stop₂) {s₁ s₂ : State}
    {f : State → State} (hok : HookOk f spec)
    (hpc : s₁.pc = s₂.pc) (hsp : s₁.sp = s₂.sp)
    (hr1 : s₁.status = .Running) (hr2 : s₂.status = .Running)
    (ha1 : s₁.spAligned = true) (ha2 : s₂.spAligned = true)
    (he : (P pl X).externAt? s₁.pc = some f)
    (hargs : ∀ n, hookName? (P pl X) s₁.pc = some n → args (arity n) s₁ = args (arity n) s₂)
    (x₁ x₂ : α) (R₁ R₂ : SepProp)
    (hpre1 : s₁.mem ⊨ spec.pre x₁ s₁ ∗ R₁) (hpre2 : s₂.mem ⊨ spec.pre x₂ s₂ ∗ R₂)
    (hcl1 : (P pl X).CodeLoaded s₁.mem) (hcl2 : (P pl X).CodeLoaded s₂.mem)
    (h : SubroutineOutcome spec x₁ R₁ s₁ (f s₁) → SubroutineOutcome spec x₂ R₂ s₂ (f s₂) →
      (P pl X).CodeLoaded (f s₁).mem → (P pl X).CodeLoaded (f s₂).mem →
      ObsEquiv (P pl X) arity stop₁ stop₂ (f s₁) (f s₂)) :
    ObsEquiv (P pl X) arity stop₁ stop₂ s₁ s₂ := by
  obtain ⟨hk1, hy1, ho1⟩ := hok x₁ R₁ s₁ hr1 hpre1 ha1
  obtain ⟨hk2, hy2, ho2⟩ := hok x₂ R₂ s₂ hr2 hpre2 ha2
  have he2 : (P pl X).externAt? s₂.pc = some f := hpc ▸ he
  have st1 : Step (P pl X) s₁ (f s₁) := Step.externHook hr1 he hk1 hy1
  have st2 : Step (P pl X) s₂ (f s₂) := Step.externHook hr2 he2 hk2 hy2
  exact oe_step hc hpc hsp (hr1.trans hr2.symm) st1 st2 (stepObs_hook_eq' hpc he hargs)
    (h ho1 ho2 (Arm64Facts.steps_codeLoaded_v2 (Steps.step st1 (Steps.refl _)) hcl1)
      (Arm64Facts.steps_codeLoaded_v2 (Steps.step st2 (Steps.refl _)) hcl2))

end rules

theorem not_sat_false' {m : Memory} {R : SepProp} : ¬ (m ⊨ (⌜False⌝ : SepProp) ∗ R) := by
  rw [sat_pure_sep]; exact fun h => h.1

/-- Every name's arity is at most 3. -/
theorem arity_le3 : ∀ n, arity n ≤ 3 := by
  intro n; unfold arity; split_ifs <;> omega

/-! ## No function meets both the `sodium_memzero` and the `memset` contracts -/

theorem no_both {f : State → State} (h1 : HookOk f Libc.explicitBzeroSpec)
    (h2 : HookOk f VerifiedLibraries.Musl.cryptoMemsetSpec) {s : State}
    (hr : s.status = .Running) (ha : s.spAligned = true) {A : BitVec 64} {R : SepProp}
    (hm : s.mem ⊨ memRegion A 1 ∗ memRegion (s.sp - 4096#64) 4096 ∗ R) : False := by
  let s' := mkS s s.pc (upd (upd (upd s.regs.regs 0#5 A) 1#5 1#64) 2#5 1#64) s.sp s.pstate s.mem
    s.vregs.regs
  have ha' : s'.spAligned = true := ha
  have hr' : s'.status = .Running := hr
  have hp1 : s'.mem ⊨ Libc.explicitBzeroSpec.pre (A, 1) s' ∗ R := by
    simp only [Libc.explicitBzeroSpec, VerifiedLibraries.Musl.cExtern, ProofLib.stackAt,
      VerifiedLibraries.Musl.externStack]
    rw [sepConj_assoc, sat_pure_sep, sepConj_assoc]
    exact ⟨⟨by simp [s', Reg.x0], by simp [s', Reg.x1]⟩, hm⟩
  have hp2 : s'.mem ⊨ VerifiedLibraries.Musl.cryptoMemsetSpec.pre (A, 1#8, 1) s' ∗ R := by
    simp only [VerifiedLibraries.Musl.cryptoMemsetSpec, VerifiedLibraries.Musl.cExtern,
      ProofLib.stackAt, VerifiedLibraries.Musl.externStack]
    rw [sepConj_assoc, sat_pure_sep, sepConj_assoc]
    refine ⟨⟨by simp [s', Reg.x0], ?_, by simp [s', Reg.x2]⟩, hm⟩
    simp [s', Reg.x1, State.readReg32]
  obtain ⟨-, -, o1⟩ := h1 (A, 1) R s' hr' hp1 ha'
  obtain ⟨-, -, o2⟩ := h2 (A, 1#8, 1) R s' hr' hp2 ha'
  rcases o1 with ⟨-, -, p1⟩ | ⟨-, p⟩ | ⟨_, -, p⟩ | ⟨-, p⟩
  rotate_left
  · exact not_sat_false' p
  · exact not_sat_false' p
  · exact not_sat_false' p
  rcases o2 with ⟨-, -, p2⟩ | ⟨-, p⟩ | ⟨_, -, p⟩ | ⟨-, p⟩
  rotate_left
  · exact not_sat_false' p
  · exact not_sat_false' p
  · exact not_sat_false' p
  simp only [Libc.explicitBzeroSpec, VerifiedLibraries.Musl.cExtern] at p1
  simp only [VerifiedLibraries.Musl.cryptoMemsetSpec, VerifiedLibraries.Musl.cExtern] at p2
  rw [sepConj_assoc] at p1
  rw [sepConj_assoc, sepConj_assoc, sat_pure_sep] at p2
  have r1 := (sat_bytes_read p1 0 (by simp)).1
  have r2 := (sat_bytes_read p2.2 0 (by simp)).1
  rw [r1] at r2
  simp at r2

/-- At the address of `sodium_memzero`, the hook is looked up under a name of arity at most 2. -/
theorem hookName_memzero {pl : Placement} {X : String → Option (State → State)}
    (hL : Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthCtLib pl X)
    (hz : Poly1305Libsodium.MemzeroOk X) (hs : MemsetOk X)
    (hnb : ∀ f : State → State, HookOk f Libc.explicitBzeroSpec →
      HookOk f VerifiedLibraries.Musl.cryptoMemsetSpec → False) :
    ∀ n, hookName? (P pl X) (pl.ρ "sodium_memzero") = some n → arity n ≤ 2 := by
  intro n hn
  unfold hookName? at hn
  rw [Option.or_eq_some_iff] at hn
  rcases hn with hn | ⟨-, hn⟩
  · obtain ⟨⟨e, o⟩, hmem, hf⟩ := List.exists_of_findSome?_eq_some hn
    dsimp only at hf
    have ho : o = (pl.ρ "sodium_memzero" - pl.base).toNat ∧ e = n := by
      by_cases h : (o == (pl.ρ "sodium_memzero" - (P pl X).base).toNat && ((P pl X).externs e).isSome) = true
      · rw [if_pos h] at hf
        cases hf
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact ⟨h.1, rfl⟩
      · rw [if_neg h] at hf
        cases hf
    obtain ⟨rfl, rfl⟩ := ho
    obtain ⟨e', he', hee⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at hee
    obtain ⟨rfl, ho⟩ := hee
    by_cases hm : e' = "memset"
    · subst hm
      exfalso
      have hρ : pl.ρ "memset" = pl.ρ "sodium_memzero" := by
        have h1 := BitVec.eq_of_toNat_eq ho
        have h2 := congrArg (· + pl.base) h1
        simpa using h2
      have hag := hL.1 "memset" (by decide) "sodium_memzero" (by decide) hρ
      obtain ⟨fz, hfz, hzok⟩ := hz
      obtain ⟨fm, hfm, hmok⟩ := hs
      have hfe : fm = fz := Option.some.inj (hfm.symm.trans (hag.trans hfz))
      subst hfe
      exact hnb fm hzok hmok
    · unfold arity
      split_ifs with h1 h2 <;> first | omega | exact absurd h2 hm
  · obtain ⟨⟨e, o⟩, -, hf⟩ := List.exists_of_findSome?_eq_some hn
    simp [P, PlacedLib.program] at hf

end Poly1305DebianCtFinish

end
end

section
section
/-! # The memory of a run of `poly1305_finish` between the prologue and the tail call

`MemI A M SP sk F m`: the 96 state bytes at `A` in five pieces (`h`/`r`, the pad and leftover,
the buffer, `final`, the rest), the 16 `mac` bytes at `M`, the saved registers `sk` in the 32-byte
frame at `SP - 32`, the 4096 bytes below it that the hooks may use, and the caller's frame `F`.
Contents are not tracked: constant time needs only the addresses. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFinish

open Arm64 Arm64.Obj Leakage Poly1305DebianCt Poly1305DebianCtFw
open Poly1305Libsodium (u64At)

theorem sat_2 {m : Memory} {P Q R : SepProp} (h : m ⊨ P ∗ Q ∗ R) : m ⊨ Q ∗ P ∗ R := by
  rwa [sepConj_left_comm]

theorem sat_3 {m : Memory} {P Q R S : SepProp} (h : m ⊨ P ∗ Q ∗ R ∗ S) : m ⊨ R ∗ P ∗ Q ∗ S := by
  rwa [sepConj_left_comm Q R S, sepConj_left_comm P R] at h

theorem sat_4 {m : Memory} {P Q R S T : SepProp} (h : m ⊨ P ∗ Q ∗ R ∗ S ∗ T) :
    m ⊨ S ∗ P ∗ Q ∗ R ∗ T := by
  rwa [sepConj_left_comm R S T, sepConj_left_comm Q S, sepConj_left_comm P S] at h

/-- The saved registers `x29, x30, x19, x20` of the entry state, as the frame holds them. -/
def stk (c₀ : State) : List (BitVec 8) :=
  unpack64 (c₀.readReg64 (.gpr 29#5)) ++ unpack64 (c₀.readReg64 (.gpr 30#5)) ++
    unpack64 (c₀.readReg64 (.gpr 19#5)) ++ unpack64 (c₀.readReg64 (.gpr 20#5))

theorem stk_length (c₀ : State) : (stk c₀).length = 32 := by simp [stk, unpack64]

def MemI (A M SP : BitVec 64) (sk : List (BitVec 8)) (F : SepProp) (m : Memory) : Prop :=
  ∃ (a b c : List (BitVec 8)) (d : BitVec 8) (e mac : List (BitVec 8)),
    a.length = 48 ∧ b.length = 24 ∧ c.length = 16 ∧ e.length = 7 ∧ mac.length = 16 ∧
    m ⊨ (A ↦ₛ a) ∗ ((A + 48#64) ↦ₛ b) ∗ ((A + 72#64) ↦ₛ c) ∗ ((A + 88#64) ↦ₛ [d]) ∗
      ((A + 89#64) ↦ₛ e) ∗ (M ↦ₛ mac) ∗ ((SP - 32#64) ↦ₛ sk) ∗ memRegion (SP - 4128#64) 4096 ∗ F

/-- What `poly1305_finish` hands back: returned to `lr`, the calling convention kept, the code
still loaded, and the state, `mac` and frame owned again (contents unknown). -/
def FinishPost (pl : Placement) (X : String → Option (State → State)) (c₀ : State) (F : SepProp)
    (f : State) : Prop :=
  Returned c₀ f ∧ CallingConventionPreserved c₀ f ∧ (P pl X).CodeLoaded f.mem ∧
    ∃ st mac : List (BitVec 8), st.length = 96 ∧ mac.length = 16 ∧
      f.mem ⊨ ((c₀.readReg64 Reg.x0 ↦ₛ st) ∗ (c₀.readReg64 Reg.x1 ↦ₛ mac) ∗ stackFrame c₀ 4128) ∗ F

theorem assemble (A : BitVec 64) (a b c : List (BitVec 8)) (d : BitVec 8) (e : List (BitVec 8))
    (ha : a.length = 48) (hb : b.length = 24) (hc : c.length = 16) :
    (A ↦ₛ (a ++ b ++ c ++ [d] ++ e)) = (A ↦ₛ a) ∗ ((A + 48#64) ↦ₛ b) ∗ ((A + 72#64) ↦ₛ c) ∗
      ((A + 88#64) ↦ₛ [d]) ∗ ((A + 89#64) ↦ₛ e) := by
  simp only [List.append_assoc]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [ha, hb, hc, List.length_singleton, pc_add]

/-- The loads of the reduction (`x19 + 0x18 … 0x38`) are readable. -/
theorem memI_rd {A M SP : BitVec 64} {sk : List (BitVec 8)} {F : SepProp} {m : Memory}
    (h : MemI A M SP sk F m) :
    m.canRead (A + 0x18#64) 8 = true ∧ m.canRead (A + 0x18#64 + 8#64) 8 = true ∧
    m.canRead (A + 0x28#64) 8 = true ∧ m.canRead (A + 0x28#64 + 8#64) 8 = true ∧
    m.canRead (A + 0x38#64) 8 = true := by
  obtain ⟨a, b, c, d, e, mac, la, lb, lc, le, lm, hm⟩ := h
  have r24 := (sat_bytes_read64 hm 24 (by omega)).2
  have r32 := (sat_bytes_read64 hm 32 (by omega)).2
  have r40 := (sat_bytes_read64 hm 40 (by omega)).2
  have hb : m ⊨ ((A + 48#64) ↦ₛ b) ∗ ((A ↦ₛ a) ∗ ((A + 72#64) ↦ₛ c) ∗ ((A + 88#64) ↦ₛ [d]) ∗
      ((A + 89#64) ↦ₛ e) ∗ (M ↦ₛ mac) ∗ ((SP - 32#64) ↦ₛ sk) ∗ memRegion (SP - 4128#64) 4096 ∗ F) :=
    Satisfies.of_eq hm (by ac_rfl)
  have r48 := (sat_bytes_read64 hb 0 (by omega)).2
  have r56 := (sat_bytes_read64 hb 8 (by omega)).2
  refine ⟨r24, ?_, r40, ?_, ?_⟩
  · rw [pc_add]; exact r32
  · rw [show A + 0x28#64 + 8#64 = A + 48#64 + BitVec.ofNat 64 0 by bv_omega]; exact r48
  · rw [show A + 0x38#64 = A + 48#64 + BitVec.ofNat 64 8 by bv_omega]; exact r56

/-- The store `stp x0, x4, [x20]` of the tag keeps the invariant. -/
theorem memI_stp {A M SP : BitVec 64} {sk : List (BitVec 8)} {F : SepProp} {m : Memory}
    (h : MemI A M SP sk F m) (w1 w2 : BitVec 64) :
    m.canWrite (M + 0#64) 8 = true ∧ m.canWrite (M + 0#64 + 8#64) 8 = true ∧
    MemI A M SP sk F ((m.write64 (M + 0#64) w1).write64 (M + 0#64 + 8#64) w2) := by
  obtain ⟨a, b, c, d, e, mac, la, lb, lc, le, lm, hm⟩ := h
  have hM : m ⊨ (M ↦ₛ mac) ∗ ((A ↦ₛ a) ∗ ((A + 48#64) ↦ₛ b) ∗ ((A + 72#64) ↦ₛ c) ∗
      ((A + 88#64) ↦ₛ [d]) ∗ ((A + 89#64) ↦ₛ e) ∗ ((SP - 32#64) ↦ₛ sk) ∗
      memRegion (SP - 4128#64) 4096 ∗ F) := Satisfies.of_eq hm (by ac_rfl)
  have w0 := sat_bytes_write64 hM 0 (by omega) w1
  have w8 := (sat_bytes_write64 hM 8 (by omega) w2).1
  have w08 := sat_bytes_write64 w0.2 8 (by simp; omega) w2
  have e8 : M + 0#64 + 8#64 = M + BitVec.ofNat 64 8 := by rw [BitVec.add_zero]
  refine ⟨w0.1, by simpa only [e8] using w8, ?_⟩
  rw [e8]
  refine ⟨a, b, c, d, e, (List.take 0 mac ++ unpack64 w1 ++ List.drop (0 + 8) mac).take 8 ++
    unpack64 w2 ++ (List.take 0 mac ++ unpack64 w1 ++ List.drop (0 + 8) mac).drop (8 + 8),
    la, lb, lc, le, by simp [lm], Satisfies.of_eq w08.2 (by ac_rfl)⟩

/-- The precondition of `sodium_memzero(A, 96)`: the state as a region, the 4096 bytes below `SP`,
with the `mac`, the rest of the frame and `F` as frame. -/
theorem memI_zero {A M SP : BitVec 64} {sk : List (BitVec 8)} {F : SepProp} {m : Memory}
    (h : MemI A M SP sk F m) (hsk : sk.length = 32) :
    ∃ mac : List (BitVec 8), mac.length = 16 ∧
      m ⊨ (memRegion A 96 ∗ memRegion (SP - 4096#64) 4096) ∗
        ((M ↦ₛ mac) ∗ memRegion (SP - 4128#64) 32 ∗ F) := by
  obtain ⟨a, b, c, d, e, mac, la, lb, lc, le, lm, hm⟩ := h
  refine ⟨mac, lm, ?_⟩
  replace hm : m ⊨ ((A ↦ₛ a) ∗ ((A + 48#64) ↦ₛ b) ∗ ((A + 72#64) ↦ₛ c) ∗ ((A + 88#64) ↦ₛ [d]) ∗
      ((A + 89#64) ↦ₛ e)) ∗ ((M ↦ₛ mac) ∗ ((SP - 32#64) ↦ₛ sk) ∗ memRegion (SP - 4128#64) 4096 ∗ F) :=
    Satisfies.of_eq hm (by ac_rfl)
  rw [← assemble A a b c d e la lb lc] at hm
  have h1 := sat_sep_mono hm (bytes_entails_memRegion A _)
  have hl : (a ++ b ++ c ++ [d] ++ e).length = 96 := by simp [la, lb, lc, le]
  rw [hl] at h1
  have h2 : m ⊨ ((SP - 32#64) ↦ₛ sk) ∗ (memRegion (SP - 4128#64) 4096 ∗
      (memRegion A 96 ∗ (M ↦ₛ mac) ∗ F)) := Satisfies.of_eq h1 (by ac_rfl)
  have h3 := sat_sep_mono h2 (bytes_entails_memRegion _ sk)
  rw [hsk] at h3
  have h4 : m ⊨ (memRegion (SP - 4128#64) 4096 ∗ memRegion (SP - 32#64) 32) ∗
      (memRegion A 96 ∗ (M ↦ₛ mac) ∗ F) := Satisfies.of_eq h3 (by ac_rfl)
  have h5 := sat_sep_mono h4 (memRegion_merge (SP - 4128#64) (SP - 32#64) 4096 32
    (by bv_omega) (by decide) (by decide))
  have h6 := sat_sep_mono h5 (memRegion_split (SP - 4128#64) 32 4096 (by decide))
  rw [show SP - 4128#64 + BitVec.ofNat 64 32 = SP - 4096#64 by bv_omega] at h6
  exact Satisfies.of_eq h6 (by ac_rfl)

/-- After `sodium_memzero`: the state zero, the `mac`, and the whole 4128-byte frame. -/
theorem zero_post {A M SP : BitVec 64} {F : SepProp} {m : Memory} {mac : List (BitVec 8)}
    (h : m ⊨ ((A ↦ₛ List.replicate 96 0#8) ∗ memRegion (SP - 4096#64) 4096) ∗
      ((M ↦ₛ mac) ∗ memRegion (SP - 4128#64) 32 ∗ F)) :
    m ⊨ ((A ↦ₛ List.replicate 96 0#8) ∗ (M ↦ₛ mac) ∗ memRegion (SP - 4128#64) 4128) ∗ F := by
  have h1 : m ⊨ (memRegion (SP - 4128#64) 32 ∗ memRegion (SP - 4096#64) 4096) ∗
      ((A ↦ₛ List.replicate 96 0#8) ∗ (M ↦ₛ mac) ∗ F) := Satisfies.of_eq h (by ac_rfl)
  have h2 := sat_sep_mono h1 (memRegion_merge (SP - 4128#64) (SP - 4096#64) 32 4096
    (by bv_omega) (by decide) (by decide))
  exact Satisfies.of_eq h2 (by ac_rfl)

/-- The saved registers read back from the frame. -/
theorem memI_stk {A M SP : BitVec 64} {c₀ : State} {F : SepProp} {m : Memory}
    (h : MemI A M SP (stk c₀) F m) :
    m.read64 (SP - 32#64) = c₀.readReg64 (.gpr 29#5) ∧ m.canRead (SP - 32#64) 8 = true ∧
    m.read64 (SP - 32#64 + 8#64) = c₀.readReg64 (.gpr 30#5) ∧
      m.canRead (SP - 32#64 + 8#64) 8 = true ∧
    m.read64 (SP - 32#64 + 0x10#64) = c₀.readReg64 (.gpr 19#5) ∧
      m.canRead (SP - 32#64 + 0x10#64) 8 = true ∧
    m.read64 (SP - 32#64 + 0x10#64 + 8#64) = c₀.readReg64 (.gpr 20#5) ∧
      m.canRead (SP - 32#64 + 0x10#64 + 8#64) 8 = true := by
  obtain ⟨a, b, c, d, e, mac, la, lb, lc, le, lm, hm⟩ := h
  have hS : m ⊨ ((SP - 32#64) ↦ₛ stk c₀) ∗ ((A ↦ₛ a) ∗ ((A + 48#64) ↦ₛ b) ∗
      ((A + 72#64) ↦ₛ c) ∗ ((A + 88#64) ↦ₛ [d]) ∗ ((A + 89#64) ↦ₛ e) ∗ (M ↦ₛ mac) ∗
      memRegion (SP - 4128#64) 4096 ∗ F) := Satisfies.of_eq hm (by ac_rfl)
  have e : ((SP - 32#64) ↦ₛ stk c₀) = ((SP - 32#64) ↦₆₄ c₀.readReg64 (.gpr 29#5)) ∗
      ((SP - 32#64 + 8#64) ↦₆₄ c₀.readReg64 (.gpr 30#5)) ∗
      ((SP - 32#64 + 0x10#64) ↦₆₄ c₀.readReg64 (.gpr 19#5)) ∗
      ((SP - 32#64 + 0x10#64 + 8#64) ↦₆₄ c₀.readReg64 (.gpr 20#5)) := by
    simp only [stk, List.append_assoc, pointsToBytes_append, unpack64_length, pointsTo64_eq_bytes,
      pc_add]
  rw [e] at hS
  simp only [sepConj_assoc] at hS
  have r0 := sat64_read hS
  have r8 := sat64_read (sat_2 hS)
  have r16 := sat64_read (sat_3 hS)
  have r24 := sat64_read (sat_4 hS)
  exact ⟨r0.1, r0.2.1, r8.1, r8.2.1, r16.1, r16.2.1, r24.1, r24.2.1⟩

end Poly1305DebianCtFinish

end
end

section
section
/-! # The reduction and the tail call of `poly1305_finish` (offsets 0x68..0x140), two runs

Only `x19` (the state), `x20` (the `mac`) and the stack pointer decide addresses; every other
register is forgotten after each instruction (`rk`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFinish

open Arm64 Arm64.Obj Leakage Poly1305DebianCt Poly1305DebianCtFw

section
variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

set_option maxHeartbeats 4000000 in
/-- From +0x68 to +0x12c: the reduction and the store of the tag. -/
theorem red_rel (hc : StopCompat stop₁ stop₂) (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {c₁ c₂ c₀₁ c₀₂ : State} (hr1 : c₁.status = .Running) (hr2 : c₂.status = .Running)
    {A M SP sp : BitVec 64} {sk₁ sk₂ : List (BitVec 8)} {F₁ F₂ : SepProp}
    {q₁ q₂ : BitVec 5 → BitVec 64} {ρ₁ ρ₂ : PState} {m₁ m₂ : Memory}
    {v₁ v₂ : BitVec 5 → BitVec 128}
    (k₁ : Kp c₀₁ A M q₁) (k₂ : Kp c₀₂ A M q₂)
    (H₁ : (P pl X).CodeLoaded m₁) (H₂ : (P pl X).CodeLoaded m₂)
    (M₁ : MemI A M SP sk₁ F₁ m₁) (M₂ : MemI A M SP sk₂ F₂ m₂)
    (K : ∀ (q₁ q₂ : BitVec 5 → BitVec 64) (ρ₁ ρ₂ : PState) (m₁ m₂ : Memory),
      Kp c₀₁ A M q₁ → Kp c₀₂ A M q₂ → (P pl X).CodeLoaded m₁ → (P pl X).CodeLoaded m₂ →
      MemI A M SP sk₁ F₁ m₁ → MemI A M SP sk₂ F₂ m₂ →
      ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 1356#64) q₁ sp ρ₁ m₁ v₁)
        (mkS c₂ (pl.base + 1356#64) q₂ sp ρ₂ m₂ v₂)) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 1160#64) q₁ sp ρ₁ m₁ v₁)
      (mkS c₂ (pl.base + 1160#64) q₂ sp ρ₂ m₂ v₂) := by
  have R₁ := memI_rd M₁
  have R₂ := memI_rd M₂
  -- +0x68: ldp x5, x2, [x19, #0x18]
  refine rk hc hr1 hr2 (f_68 hP H₁) (f_68 hP H₂)
    (ex_ldp64_gpr 5#5 2#5 19#5 (by decide) (by decide) (by decide) 0x18#64 (by rw [k₁.1]; exact R₁.1) (by rw [k₁.1]; exact R₁.2.1))
    (ex_ldp64_gpr 5#5 2#5 19#5 (by decide) (by decide) (by decide) 0x18#64 (by rw [k₂.1]; exact R₂.1) (by rw [k₂.1]; exact R₂.2.1))
    (by simp [leakedValues, evalAddrMode, k₁.1, k₂.1]) (Kp_upd (Kp_upd k₁ _) _) (Kp_upd (Kp_upd k₂ _) _) (a4 _ 1160 1164) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_6c hP H₁) (f_6c hP H₂)
    (ex_movz32 3#5 (by decide) _)
    (ex_movz32 3#5 (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1164 1168) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  -- +0x70: ldp x0, x1, [x19, #0x28]
  refine rk hc hr1 hr2 (f_70 hP H₁) (f_70 hP H₂)
    (ex_ldp64_gpr 0#5 1#5 19#5 (by decide) (by decide) (by decide) 0x28#64 (by rw [k₁.1]; exact R₁.2.2.1) (by rw [k₁.1]; exact R₁.2.2.2.1))
    (ex_ldp64_gpr 0#5 1#5 19#5 (by decide) (by decide) (by decide) 0x28#64 (by rw [k₂.1]; exact R₂.2.2.1) (by rw [k₂.1]; exact R₂.2.2.2.1))
    (by simp [leakedValues, evalAddrMode, k₁.1, k₂.1]) (Kp_upd (Kp_upd k₁ _) _) (Kp_upd (Kp_upd k₂ _) _) (a4 _ 1168 1172) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_74 hP H₁) (f_74 hP H₂)
    (ex_and_imm 4#5 2#5 (by decide) (by decide) _)
    (ex_and_imm 4#5 2#5 (by decide) (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1172 1176) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_78 hP H₁) (f_78 hP H₂)
    (ex_add_shift 2#5 0#5 2#5 (by decide) (by decide) (by decide) .LSR 44)
    (ex_add_shift 2#5 0#5 2#5 (by decide) (by decide) (by decide) .LSR 44)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1176 1180) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_7c hP H₁) (f_7c hP H₂)
    (ex_and_imm 0#5 2#5 (by decide) (by decide) _)
    (ex_and_imm 0#5 2#5 (by decide) (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1180 1184) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_80 hP H₁) (f_80 hP H₂)
    (ex_bitfield .UBFM 2#5 2#5 (by decide) (by decide) 42 63)
    (ex_bitfield .UBFM 2#5 2#5 (by decide) (by decide) 42 63)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1184 1188) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_84 hP H₁) (f_84 hP H₂)
    (ex_umaddl 2#5 2#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide))
    (ex_umaddl 2#5 2#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide))
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1188 1192) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_88 hP H₁) (f_88 hP H₂)
    (ex_and_imm 5#5 2#5 (by decide) (by decide) _)
    (ex_and_imm 5#5 2#5 (by decide) (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1192 1196) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_8c hP H₁) (f_8c hP H₂)
    (ex_add_shift 2#5 4#5 2#5 (by decide) (by decide) (by decide) .LSR 44)
    (ex_add_shift 2#5 4#5 2#5 (by decide) (by decide) (by decide) .LSR 44)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1196 1200) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_90 hP H₁) (f_90 hP H₂)
    (ex_and_imm 4#5 2#5 (by decide) (by decide) _)
    (ex_and_imm 4#5 2#5 (by decide) (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1200 1204) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_94 hP H₁) (f_94 hP H₂)
    (ex_add_shift 2#5 0#5 2#5 (by decide) (by decide) (by decide) .LSR 44)
    (ex_add_shift 2#5 0#5 2#5 (by decide) (by decide) (by decide) .LSR 44)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1204 1208) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_98 hP H₁) (f_98 hP H₂)
    (ex_and_imm 8#5 2#5 (by decide) (by decide) _)
    (ex_and_imm 8#5 2#5 (by decide) (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1208 1212) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_9c hP H₁) (f_9c hP H₂)
    (ex_bitfield .UBFM 0#5 2#5 (by decide) (by decide) 42 63)
    (ex_bitfield .UBFM 0#5 2#5 (by decide) (by decide) 42 63)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1212 1216) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_a0 hP H₁) (f_a0 hP H₂)
    (ex_orr_imm 2#5 2#5 (by decide) (by decide) _)
    (ex_orr_imm 2#5 2#5 (by decide) (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1216 1220) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_a4 hP H₁) (f_a4 hP H₂)
    (ex_umaddl 0#5 0#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide))
    (ex_umaddl 0#5 0#5 3#5 5#5 (by decide) (by decide) (by decide) (by decide))
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1220 1224) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_a8 hP H₁) (f_a8 hP H₂)
    (ex_movz64 5#5 (by decide) _)
    (ex_movz64 5#5 (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1224 1228) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_ac hP H₁) (f_ac hP H₂)
    (ex_and_imm 7#5 0#5 (by decide) (by decide) _)
    (ex_and_imm 7#5 0#5 (by decide) (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1228 1232) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_b0 hP H₁) (f_b0 hP H₂)
    (ex_add_shift 0#5 4#5 0#5 (by decide) (by decide) (by decide) .LSR 44)
    (ex_add_shift 0#5 4#5 0#5 (by decide) (by decide) (by decide) .LSR 44)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1232 1236) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_b4 hP H₁) (f_b4 hP H₂)
    (ex_add_imm 4#5 7#5 (by decide) (by decide) _)
    (ex_add_imm 4#5 7#5 (by decide) (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1236 1240) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_b8 hP H₁) (f_b8 hP H₂)
    (ex_add_shift 3#5 0#5 4#5 (by decide) (by decide) (by decide) .LSR 44)
    (ex_add_shift 3#5 0#5 4#5 (by decide) (by decide) (by decide) .LSR 44)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1240 1244) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_bc hP H₁) (f_bc hP H₂)
    (ex_add_shift 2#5 2#5 3#5 (by decide) (by decide) (by decide) .LSR 44)
    (ex_add_shift 2#5 2#5 3#5 (by decide) (by decide) (by decide) .LSR 44)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1244 1248) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_c0 hP H₁) (f_c0 hP H₂)
    (ex_cmp_reg 2#5 5#5 (by decide) (by decide))
    (ex_cmp_reg 2#5 5#5 (by decide) (by decide))
    rfl k₁ k₂ (a4 _ 1248 1252) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_c4 hP H₁) (f_c4 hP H₂)
    (ex_csetm 9#5 (by decide) .LT)
    (ex_csetm 9#5 (by decide) .LT)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1252 1256) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_c8 hP H₁) (f_c8 hP H₂)
    (ex_and_shift 7#5 7#5 2#5 (by decide) (by decide) (by decide) .ASR 63)
    (ex_and_shift 7#5 7#5 2#5 (by decide) (by decide) (by decide) .ASR 63)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1256 1260) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_cc hP H₁) (f_cc hP H₂)
    (ex_and_shift 6#5 4#5 9#5 (by decide) (by decide) (by decide) .LSL 0)
    (ex_and_shift 6#5 4#5 9#5 (by decide) (by decide) (by decide) .LSL 0)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1260 1264) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_d0 hP H₁) (f_d0 hP H₂)
    (ex_and_shift 5#5 3#5 9#5 (by decide) (by decide) (by decide) .LSL 0)
    (ex_and_shift 5#5 3#5 9#5 (by decide) (by decide) (by decide) .LSL 0)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1264 1268) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  -- +0xd4: ldr x4, [x19, #0x38]
  refine rk hc hr1 hr2 (f_d4 hP H₁) (f_d4 hP H₂)
    (ex_ldr64_gpr 4#5 19#5 (by decide) (by decide) 0x38#64 (by rw [k₁.1]; exact R₁.2.2.2.2))
    (ex_ldr64_gpr 4#5 19#5 (by decide) (by decide) 0x38#64 (by rw [k₂.1]; exact R₂.2.2.2.2))
    (by simp [leakedValues, evalAddrMode, k₁.1, k₂.1]) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1268 1272) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_d8 hP H₁) (f_d8 hP H₂)
    (ex_and_imm 6#5 6#5 (by decide) (by decide) _)
    (ex_and_imm 6#5 6#5 (by decide) (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1272 1276) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_dc hP H₁) (f_dc hP H₂)
    (ex_orr_shift 6#5 6#5 7#5 (by decide) (by decide) (by decide) .LSL 0)
    (ex_orr_shift 6#5 6#5 7#5 (by decide) (by decide) (by decide) .LSL 0)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1276 1280) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_e0 hP H₁) (f_e0 hP H₂)
    (ex_and_shift 3#5 0#5 2#5 (by decide) (by decide) (by decide) .ASR 63)
    (ex_and_shift 3#5 0#5 2#5 (by decide) (by decide) (by decide) .ASR 63)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1280 1284) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_e4 hP H₁) (f_e4 hP H₂)
    (ex_and_imm 5#5 5#5 (by decide) (by decide) _)
    (ex_and_imm 5#5 5#5 (by decide) (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1284 1288) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_e8 hP H₁) (f_e8 hP H₂)
    (ex_and_imm 0#5 1#5 (by decide) (by decide) _)
    (ex_and_imm 0#5 1#5 (by decide) (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1288 1292) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_ec hP H₁) (f_ec hP H₂)
    (ex_add_shift 0#5 0#5 6#5 (by decide) (by decide) (by decide) .LSL 0)
    (ex_add_shift 0#5 0#5 6#5 (by decide) (by decide) (by decide) .LSL 0)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1292 1296) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_f0 hP H₁) (f_f0 hP H₂)
    (ex_extr 1#5 4#5 1#5 (by decide) (by decide) (by decide) 44)
    (ex_extr 1#5 4#5 1#5 (by decide) (by decide) (by decide) 44)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1296 1300) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_f4 hP H₁) (f_f4 hP H₂)
    (ex_orr_shift 3#5 5#5 3#5 (by decide) (by decide) (by decide) .LSL 0)
    (ex_orr_shift 3#5 5#5 3#5 (by decide) (by decide) (by decide) .LSL 0)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1300 1304) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_f8 hP H₁) (f_f8 hP H₂)
    (ex_and_imm 1#5 1#5 (by decide) (by decide) _)
    (ex_and_imm 1#5 1#5 (by decide) (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1304 1308) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_fc hP H₁) (f_fc hP H₂)
    (ex_and_shift 7#5 8#5 2#5 (by decide) (by decide) (by decide) .ASR 63)
    (ex_and_shift 7#5 8#5 2#5 (by decide) (by decide) (by decide) .ASR 63)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1308 1312) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_100 hP H₁) (f_100 hP H₂)
    (ex_add_shift 1#5 1#5 3#5 (by decide) (by decide) (by decide) .LSL 0)
    (ex_add_shift 1#5 1#5 3#5 (by decide) (by decide) (by decide) .LSL 0)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1312 1316) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_104 hP H₁) (f_104 hP H₂)
    (ex_and_shift 2#5 2#5 9#5 (by decide) (by decide) (by decide) .LSL 0)
    (ex_and_shift 2#5 2#5 9#5 (by decide) (by decide) (by decide) .LSL 0)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1316 1320) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_108 hP H₁) (f_108 hP H₂)
    (ex_and_imm 6#5 0#5 (by decide) (by decide) _)
    (ex_and_imm 6#5 0#5 (by decide) (by decide) _)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1320 1324) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_10c hP H₁) (f_10c hP H₂)
    (ex_orr_shift 2#5 2#5 7#5 (by decide) (by decide) (by decide) .LSL 0)
    (ex_orr_shift 2#5 2#5 7#5 (by decide) (by decide) (by decide) .LSL 0)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1324 1328) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_110 hP H₁) (f_110 hP H₂)
    (ex_add_shift 0#5 1#5 0#5 (by decide) (by decide) (by decide) .LSR 44)
    (ex_add_shift 0#5 1#5 0#5 (by decide) (by decide) (by decide) .LSR 44)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1328 1332) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_114 hP H₁) (f_114 hP H₂)
    (ex_add_shift 4#5 2#5 4#5 (by decide) (by decide) (by decide) .LSR 24)
    (ex_add_shift 4#5 2#5 4#5 (by decide) (by decide) (by decide) .LSR 24)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1332 1336) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_118 hP H₁) (f_118 hP H₂)
    (ex_add_shift 4#5 4#5 0#5 (by decide) (by decide) (by decide) .LSR 44)
    (ex_add_shift 4#5 4#5 0#5 (by decide) (by decide) (by decide) .LSR 44)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1336 1340) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_11c hP H₁) (f_11c hP H₂)
    (ex_bitfield .UBFM 1#5 0#5 (by decide) (by decide) 20 43)
    (ex_bitfield .UBFM 1#5 0#5 (by decide) (by decide) 20 43)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1340 1344) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_120 hP H₁) (f_120 hP H₂)
    (ex_orr_shift 0#5 6#5 0#5 (by decide) (by decide) (by decide) .LSL 44)
    (ex_orr_shift 0#5 6#5 0#5 (by decide) (by decide) (by decide) .LSL 44)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1344 1348) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  refine rk hc hr1 hr2 (f_124 hP H₁) (f_124 hP H₂)
    (ex_orr_shift 4#5 1#5 4#5 (by decide) (by decide) (by decide) .LSL 24)
    (ex_orr_shift 4#5 1#5 4#5 (by decide) (by decide) (by decide) .LSL 24)
    (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1348 1352) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  -- +0x128: stp x0, x4, [x20]
  obtain ⟨W1₁, W2₁, MI₁⟩ := memI_stp M₁ (q₁ 0#5) (q₁ 4#5)
  obtain ⟨W1₂, W2₂, MI₂⟩ := memI_stp M₂ (q₂ 0#5) (q₂ 4#5)
  have e₁ := ex_stp64_gpr (svc := evalSvc (P pl X).svc) (s0 := c₁) (pc := pl.base + 1352#64)
    (r := q₁) (sp := sp) (ps := ρ₁) (m := m₁) (v := v₁) 0#5 4#5 20#5 (by decide) (by decide)
    (by decide) 0#64 (by rw [k₁.2.1]; exact W1₁) (by rw [k₁.2.1]; exact W2₁)
  have e₂ := ex_stp64_gpr (svc := evalSvc (P pl X).svc) (s0 := c₂) (pc := pl.base + 1352#64)
    (r := q₂) (sp := sp) (ps := ρ₂) (m := m₂) (v := v₂) 0#5 4#5 20#5 (by decide) (by decide)
    (by decide) 0#64 (by rw [k₂.2.1]; exact W1₂) (by rw [k₂.2.1]; exact W2₂)
  rw [k₁.2.1] at e₁
  rw [k₂.2.1] at e₂
  have C₁ := cl_exec hr1 (f_128 hP H₁) e₁ H₁
  have C₂ := cl_exec hr2 (f_128 hP H₂) e₂ H₂
  refine rk hc hr1 hr2 (f_128 hP H₁) (f_128 hP H₂) e₁ e₂
    (by simp [leakedValues, evalAddrMode, k₁.2.1, k₂.2.1]) k₁ k₂ (a4 _ 1352 1356) ?_
  intro q₁' q₂' ρ₁' ρ₂' k₁' k₂'
  exact K _ _ _ _ _ _ k₁' k₂' C₁ C₂ MI₁ MI₂

end

end Poly1305DebianCtFinish

end
end

section
section
/-! # The epilogue and the tail call `b sodium_memzero` (offsets 0x12c..0x140), two runs

The saved registers come back from the frame, and the `sodium_memzero(st, 96)` hook returns both
runs to `lr` with the state zeroed: `FinishPost`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFinish

open Arm64 Arm64.Obj Leakage Poly1305DebianCt Poly1305DebianCtFw

theorem args_eq2 {k : Nat} (hk : k ≤ 2) {s₁ s₂ : State}
    (h0 : s₁.readReg64 (.gpr 0#5) = s₂.readReg64 (.gpr 0#5))
    (h1 : s₁.readReg64 (.gpr 1#5) = s₂.readReg64 (.gpr 1#5)) : args k s₁ = args k s₂ := by
  unfold args
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have : i < 2 := by omega
  interval_cases i
  · exact h0
  · exact h1

theorem cs_final {c₀ f : State} {r : BitVec 5 → BitVec 64} (hk : KeptRegs f r)
    (g : ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 31 → r k = c₀.readReg64 (.gpr k))
    (hv : calleeSavedVRegs f = calleeSavedVRegs c₀) : CalleeSavedPreserved c₀ f := by
  have e : ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 30 →
      f.readReg64 (.gpr k) = c₀.readReg64 (.gpr k) := fun k h1 h2 => by
    rw [readGpr_eq f k (by intro e; subst e; simp at h2), hk k h1 h2, g k h1 (by omega)]
  exact ⟨e 19#5 (by decide) (by decide), e 20#5 (by decide) (by decide),
    e 21#5 (by decide) (by decide), e 22#5 (by decide) (by decide),
    e 23#5 (by decide) (by decide), e 24#5 (by decide) (by decide),
    e 25#5 (by decide) (by decide), e 26#5 (by decide) (by decide),
    e 27#5 (by decide) (by decide), e 28#5 (by decide) (by decide),
    e 29#5 (by decide) (by decide), hv⟩

/-- The registers at the tail call: `x19, x20, x29, x30` restored, `x21..x28` kept. -/
theorem g_of {c₀ : State} {A M : BitVec 64} {q : BitVec 5 → BitVec 64} (k : Kp c₀ A M q)
    (a0 a1 : BitVec 64) : ∀ j : BitVec 5, 19 ≤ j.toNat → j.toNat < 31 →
      upd (upd (upd (upd (upd (upd q 0#5 a0) 19#5 (c₀.readReg64 (.gpr 19#5))) 20#5
        (c₀.readReg64 (.gpr 20#5))) 1#5 a1) 29#5 (c₀.readReg64 (.gpr 29#5))) 30#5
        (c₀.readReg64 (.gpr 30#5)) j = c₀.readReg64 (.gpr j) := by
  intro j h1 h2
  have e : j = BitVec.ofNat 5 j.toNat := by simp
  generalize j.toNat = n at e h1 h2
  subst e
  interval_cases n <;> simp only [upd_apply, BitVec.reduceEq, BitVec.ofNat_eq_ofNat, ite_false,
    ite_true] <;> exact k.2.2 _ (by decide) (by decide)

section
variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

theorem rn (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State}
    (hr1 : c₁.status = .Running) (hr2 : c₂.status = .Running)
    {pc sp sp' pcn : BitVec 64} {r₁ r₂ r₁' r₂' : BitVec 5 → BitVec 64}
    {ps₁ ps₂ ps₁' ps₂' : PState} {m₁ m₂ m₁' m₂' : Memory} {v₁ v₂ : BitVec 5 → BitVec 128}
    {i : Instr}
    (hf1 : (P pl X).fetchMem m₁ pc = some i) (hf2 : (P pl X).fetchMem m₂ pc = some i)
    (e1 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) =
      mkS c₁ (pc + 4#64) r₁' sp' ps₁' m₁' v₁)
    (e2 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₂ pc r₂ sp ps₂ m₂ v₂) =
      mkS c₂ (pc + 4#64) r₂' sp' ps₂' m₂' v₂)
    (hl : leakedValues i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) = leakedValues i (mkS c₂ pc r₂ sp ps₂ m₂ v₂))
    (hpc : pc + 4#64 = pcn)
    (h : ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pcn r₁' sp' ps₁' m₁' v₁)
      (mkS c₂ pcn r₂' sp' ps₂' m₂' v₂)) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pc r₁ sp ps₁ m₁ v₁) (mkS c₂ pc r₂ sp ps₂ m₂ v₂) := by
  subst hpc
  exact rs hc hr1 hr2 hf1 hf2 e1 e2 hl h

/-- The `sodium_memzero(st, 96)` hook in both runs. -/
theorem hook_rel (hc : StopCompat stop₁ stop₂) {fz : State → State}
    (hzok : HookOk fz Libc.explicitBzeroSpec)
    (hzat : (P pl X).externAt? (pl.ρ "sodium_memzero") = some fz)
    (hna : ∀ n, hookName? (P pl X) (pl.ρ "sodium_memzero") = some n → arity n ≤ 2)
    {c₁ c₂ c₀₁ c₀₂ : State} (hr1 : c₁.status = .Running) (hr2 : c₂.status = .Running)
    {A M SP : BitVec 64} (hal : SP &&& 0b1111#64 = 0#64)
    (hSP₁ : c₀₁.sp = SP) (hSP₂ : c₀₂.sp = SP)
    (hA₁ : c₀₁.readReg64 Reg.x0 = A) (hA₂ : c₀₂.readReg64 Reg.x0 = A)
    (hM₁ : c₀₁.readReg64 Reg.x1 = M) (hM₂ : c₀₂.readReg64 Reg.x1 = M)
    {F₁ F₂ : SepProp} {r₁ r₂ : BitVec 5 → BitVec 64} {ρ₁ ρ₂ : PState} {m₁ m₂ : Memory}
    {v₁ v₂ : BitVec 5 → BitVec 128}
    (f0₁ : r₁ 0#5 = A) (f0₂ : r₂ 0#5 = A) (f1₁ : (r₁ 1#5).toNat = 96) (f1₂ : (r₂ 1#5).toNat = 96)
    (g₁ : ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 31 → r₁ k = c₀₁.readReg64 (.gpr k))
    (g₂ : ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 31 → r₂ k = c₀₂.readReg64 (.gpr k))
    (hv₁ : VRegFile.calleeSaved ⟨v₁⟩ = calleeSavedVRegs c₀₁)
    (hv₂ : VRegFile.calleeSaved ⟨v₂⟩ = calleeSavedVRegs c₀₂)
    (H₁ : (P pl X).CodeLoaded m₁) (H₂ : (P pl X).CodeLoaded m₂)
    (M₁ : MemI A M SP (stk c₀₁) F₁ m₁) (M₂ : MemI A M SP (stk c₀₂) F₂ m₂)
    (K : ∀ f₁ f₂ : State, FinishPost pl X c₀₁ F₁ f₁ → FinishPost pl X c₀₂ F₂ f₂ →
      ObsEquiv (P pl X) arity stop₁ stop₂ f₁ f₂) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (pl.ρ "sodium_memzero") r₁ SP ρ₁ m₁ v₁)
      (mkS c₂ (pl.ρ "sodium_memzero") r₂ SP ρ₂ m₂ v₂) := by
  obtain ⟨mac₁, lm₁, Z₁⟩ := memI_zero M₁ (stk_length c₀₁)
  obtain ⟨mac₂, lm₂, Z₂⟩ := memI_zero M₂ (stk_length c₀₂)
  have ha : ∀ (c : State) (r : BitVec 5 → BitVec 64) (ρ : PState) (m : Memory)
      (v : BitVec 5 → BitVec 128), (mkS c (pl.ρ "sodium_memzero") r SP ρ m v).spAligned = true :=
    fun c r ρ m v => by simp [hal]
  have hpre : ∀ (c : State) (r : BitVec 5 → BitVec 64) (ρ : PState) (m : Memory)
      (v : BitVec 5 → BitVec 128) (mac : List (BitVec 8)) (F : SepProp), r 0#5 = A →
      (r 1#5).toNat = 96 →
      (m ⊨ (memRegion A 96 ∗ memRegion (SP - 4096#64) 4096) ∗
        ((M ↦ₛ mac) ∗ memRegion (SP - 4128#64) 32 ∗ F)) →
      (mkS c (pl.ρ "sodium_memzero") r SP ρ m v).mem ⊨
        Libc.explicitBzeroSpec.pre (A, 96) (mkS c (pl.ρ "sodium_memzero") r SP ρ m v) ∗
          ((M ↦ₛ mac) ∗ memRegion (SP - 4128#64) 32 ∗ F) := by
    intro c r ρ m v mac F h0 h1 hm
    simp only [Libc.explicitBzeroSpec, VerifiedLibraries.Musl.cExtern, ProofLib.stackAt,
      VerifiedLibraries.Musl.externStack]
    rw [sepConj_assoc, sat_pure_sep]
    exact ⟨⟨by simp [Reg.x0, h0], by simp [Reg.x1, h1]⟩, hm⟩
  have post : ∀ (c c₀ : State) (r : BitVec 5 → BitVec 64) (ρ : PState) (m : Memory)
      (v : BitVec 5 → BitVec 128) (mac : List (BitVec 8)) (F : SepProp),
      c₀.sp = SP → c₀.readReg64 Reg.x0 = A → c₀.readReg64 Reg.x1 = M → mac.length = 16 →
      (∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 31 → r k = c₀.readReg64 (.gpr k)) →
      VRegFile.calleeSaved ⟨v⟩ = calleeSavedVRegs c₀ →
      SubroutineOutcome Libc.explicitBzeroSpec (A, 96) ((M ↦ₛ mac) ∗ memRegion (SP - 4128#64) 32 ∗ F)
        (mkS c (pl.ρ "sodium_memzero") r SP ρ m v) (fz (mkS c (pl.ρ "sodium_memzero") r SP ρ m v)) →
      (P pl X).CodeLoaded (fz (mkS c (pl.ρ "sodium_memzero") r SP ρ m v)).mem →
      FinishPost pl X c₀ F (fz (mkS c (pl.ρ "sodium_memzero") r SP ρ m v)) := by
    intro c c₀ r ρ m v mac F hSP hA hM lm g hv o G
    rcases o with ⟨⟨hpc, hsp, hst⟩, ⟨-, hcs⟩, hpost⟩ | ⟨-, p⟩ | ⟨_, -, p⟩ | ⟨-, p⟩
    rotate_left
    · exact absurd p not_sat_false'
    · exact absurd p not_sat_false'
    · exact absurd p not_sat_false'
    refine ⟨⟨?_, by rw [hsp, hSP]; rfl, hst⟩, ⟨by rw [hsp, hSP]; rfl, ?_⟩, G, ?_⟩
    · rw [hpc]; simpa [Reg.lr] using g 30#5 (by decide) (by decide)
    · exact cs_final (kept_of_cs hcs) g (hcs.2.2.2.2.2.2.2.2.2.2.2.trans hv)
    · simp only [Libc.explicitBzeroSpec, VerifiedLibraries.Musl.cExtern, ProofLib.stackAt,
        VerifiedLibraries.Musl.externStack, mkS_sp] at hpost
      refine ⟨List.replicate 96 0#8, mac, by simp, lm, ?_⟩
      rw [hA, hM, stackFrame, hSP]
      exact zero_post hpost
  refine oe_hk hc hzok rfl rfl hr1 hr2 (ha _ _ _ _ _) (ha _ _ _ _ _) hzat ?_ (A, 96) (A, 96)
    _ _ (hpre _ _ _ _ _ _ _ f0₁ f1₁ Z₁) (hpre _ _ _ _ _ _ _ f0₂ f1₂ Z₂) H₁ H₂ ?_
  · intro n hn
    refine args_eq2 (hna n hn) (by simp [f0₁, f0₂]) ?_
    simp only [mkS_readGpr, BitVec.reduceEq, ite_false]
    exact BitVec.eq_of_toNat_eq (f1₁.trans f1₂.symm)
  · intro o₁ o₂ G₁ G₂
    exact K _ _ (post _ _ _ _ _ _ _ _ hSP₁ hA₁ hM₁ lm₁ g₁ hv₁ o₁ G₁)
      (post _ _ _ _ _ _ _ _ hSP₂ hA₂ hM₂ lm₂ g₂ hv₂ o₂ G₂)

/-- From +0x12c to the return through `sodium_memzero`. -/
theorem tail_rel (hc : StopCompat stop₁ stop₂) (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {fz : State → State} (hzok : HookOk fz Libc.explicitBzeroSpec)
    (hzat : (P pl X).externAt? (pl.ρ "sodium_memzero") = some fz)
    (hna : ∀ n, hookName? (P pl X) (pl.ρ "sodium_memzero") = some n → arity n ≤ 2)
    {c₁ c₂ c₀₁ c₀₂ : State} (hr1 : c₁.status = .Running) (hr2 : c₂.status = .Running)
    {A M SP : BitVec 64} (hal : SP &&& 0b1111#64 = 0#64)
    (hSP₁ : c₀₁.sp = SP) (hSP₂ : c₀₂.sp = SP)
    (hA₁ : c₀₁.readReg64 Reg.x0 = A) (hA₂ : c₀₂.readReg64 Reg.x0 = A)
    (hM₁ : c₀₁.readReg64 Reg.x1 = M) (hM₂ : c₀₂.readReg64 Reg.x1 = M)
    {F₁ F₂ : SepProp} {q₁ q₂ : BitVec 5 → BitVec 64} {ρ₁ ρ₂ : PState} {m₁ m₂ : Memory}
    {v₁ v₂ : BitVec 5 → BitVec 128}
    (k₁ : Kp c₀₁ A M q₁) (k₂ : Kp c₀₂ A M q₂)
    (hv₁ : VRegFile.calleeSaved ⟨v₁⟩ = calleeSavedVRegs c₀₁)
    (hv₂ : VRegFile.calleeSaved ⟨v₂⟩ = calleeSavedVRegs c₀₂)
    (H₁ : (P pl X).CodeLoaded m₁) (H₂ : (P pl X).CodeLoaded m₂)
    (M₁ : MemI A M SP (stk c₀₁) F₁ m₁) (M₂ : MemI A M SP (stk c₀₂) F₂ m₂)
    (K : ∀ f₁ f₂ : State, FinishPost pl X c₀₁ F₁ f₁ → FinishPost pl X c₀₂ F₂ f₂ →
      ObsEquiv (P pl X) arity stop₁ stop₂ f₁ f₂) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 1356#64) q₁ (SP - 32#64) ρ₁ m₁ v₁)
      (mkS c₂ (pl.base + 1356#64) q₂ (SP - 32#64) ρ₂ m₂ v₂) := by
  have hal32 : (SP - 32#64) &&& 0b1111#64 = 0#64 := al16_sub SP 32 (by decide) (by decide) hal
  obtain ⟨s29₁, c29₁, s30₁, c30₁, s19₁, c19₁, s20₁, c20₁⟩ := memI_stk M₁
  obtain ⟨s29₂, c29₂, s30₂, c30₂, s19₂, c19₂, s20₂, c20₂⟩ := memI_stk M₂
  -- +0x12c: mov x0, x19
  refine rn hc hr1 hr2 (f_12c hP H₁) (f_12c hP H₂) (ex_mov 0#5 19#5 (by decide) (by decide))
    (ex_mov 0#5 19#5 (by decide) (by decide)) (lv0 fun _ => rfl) (a4 _ 1356 1360) ?_
  -- +0x130: ldp x19, x20, [sp, #0x10]
  refine rn hc hr1 hr2 (f_130 hP H₁) (f_130 hP H₂)
    (ex_ldp64_sp 19#5 20#5 (by decide) (by decide) 0x10#64 hal32 c19₁ c20₁)
    (ex_ldp64_sp 19#5 20#5 (by decide) (by decide) 0x10#64 hal32 c19₂ c20₂)
    (by simp [leakedValues, evalAddrMode]) (a4 _ 1360 1364) ?_
  rw [s19₁, s20₁, s19₂, s20₂]
  -- +0x134: mov x1, #0x60
  refine rn hc hr1 hr2 (f_134 hP H₁) (f_134 hP H₂) (ex_movz64 1#5 (by decide) _)
    (ex_movz64 1#5 (by decide) _) (lv0 fun _ => rfl) (a4 _ 1364 1368) ?_
  -- +0x138: ldp x29, x30, [sp], #0x20
  refine rn hc hr1 hr2 (f_138 hP H₁) (f_138 hP H₂)
    (ex_ldp64_post_sp 29#5 30#5 (by decide) (by decide) 0x20#64 hal32 c29₁ c30₁)
    (ex_ldp64_post_sp 29#5 30#5 (by decide) (by decide) 0x20#64 hal32 c29₂ c30₂)
    (by simp [leakedValues, evalAddrMode]) (a4 _ 1368 1372) ?_
  rw [s29₁, s30₁, s29₂, s30₂, show SP - 32#64 + 0x20#64 = SP by bv_omega]
  -- +0x13c: autiasp
  refine rn hc hr1 hr2 (f_13c hP H₁) (f_13c hP H₂) (ex_hint _) (ex_hint _) (lv0 fun _ => rfl) (a4 _ 1372 1376) ?_
  -- +0x140: b sodium_memzero
  refine rs hc hr1 hr2 (f_140 hP H₁) (f_140 hP H₂) (ex_b _) (ex_b _) (lv0 fun _ => rfl) ?_
  rw [show pl.base + 1376#64 + (pl.ρ "sodium_memzero" - (pl.base + 1376#64)) =
    pl.ρ "sodium_memzero" by bv_omega]
  exact hook_rel hc hzok hzat hna hr1 hr2 hal hSP₁ hSP₂ hA₁ hA₂ hM₁ hM₂
    (by simp [upd_apply, k₁.1]) (by simp [upd_apply, k₂.1]) (by simp [upd_apply])
    (by simp [upd_apply]) (g_of k₁ _ _) (g_of k₂ _ _) hv₁ hv₂ H₁ H₂ M₁ M₂ K

end

end Poly1305DebianCtFinish

end
end

section
section
section
section

end
end

section
section
/-! # Instruction fetch for the placed `libsodiumDebianOnetimeauth` text block -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtBlocks

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

theorem hook_none {pl : Placement} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)
    (X : String → Option (State → State)) {off : Nat} (hoff : off < 2324) :
    (prog pl X).externAt? (pl.base + BitVec.ofNat 64 off) = none := by
  have hl : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.code.length = 2324 := code_length
  have e1 := (hP.text.externs_ok "__stack_chk_fail" (by decide)).2
  have e3 := (hP.text.externs_ok "memset" (by decide)).2
  have e4 := (hP.text.externs_ok "randombytes_buf" (by decide)).2
  have e5 := (hP.text.externs_ok "sodium_memzero" (by decide)).2
  rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text = Poly1305DebianCt.libsodiumDebianOnetimeauthCtText from rfl, hl]
    at e1 e3 e4 e5
  have hpc : (pl.base + BitVec.ofNat 64 off - pl.base).toNat = off := by
    rw [show pl.base + BitVec.ofNat 64 off - pl.base = BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_ofNat]; omega
  simp only [prog, Program.externAt?, Program.hookAtOff?, PlacedLib.program, hpc]
  rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text.externs =
    ["__stack_chk_fail", "memset", "randombytes_buf", "sodium_memzero"] from rfl]
  simp only [List.map_cons, List.map_nil, List.findSome?_cons, List.findSome?_nil, ite_self,
    beq_iff_eq]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

/-- Byte `k < 4` of the word at aligned offset `off` of the placed code. -/
theorem read8_code {pl : Placement} {m : Memory} {X : String → Option (State → State)}
    (hCL : (prog pl X).CodeLoaded m) {off k : Nat}
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
    (by rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.code = Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedCode from rfl,
      code_length]; exact hlen)
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
    {X : String → Option (State → State)} (hCL : (prog pl X).CodeLoaded m) {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324) :
    (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off) := by
  have hb4 : pl.base.toNat % 4 = 0 := by
    have := hP.text.base_aligned
    rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text.align = 32 from rfl] at this
    omega
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
  simp only [Program.fetchMem, hook_none hP X hlen', Option.isSome_none, Bool.false_eq_true,
    if_false, hpc, ne_eq, not_true_eq_false]
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

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Abstract machine states and single-step plumbing

Every state reached by `poly1305_blocks` is `mkS s0 pc sp m ps r`: the entry state `s0` with
`pc`, `sp`, memory `m`, flags `ps` and the registers `x1..x17` (given by `r k` for `1 ≤ k ≤ 17`)
replaced. `x0`, `x18..x30` and everything else stay those of `s0`. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Arm64 Arm64.Obj

/-- Register `k ∈ [1, 17]` is a scratch register of the abstraction. -/
def Ok (i : BitVec 5) : Prop := 1 ≤ i.toNat ∧ i.toNat ≤ 17

instance (i : BitVec 5) : Decidable (Ok i) := inferInstanceAs (Decidable (_ ∧ _))

/-- Update of the scratch register function. -/
def upd (r : Nat → BitVec 64) (k : Nat) (v : BitVec 64) : Nat → BitVec 64 :=
  fun j => if j = k then v else r j

@[simp] theorem upd_same (r : Nat → BitVec 64) (k : Nat) (v : BitVec 64) : upd r k v k = v := by
  simp [upd]

def mkRegs (rf : RegFile) (r : Nat → BitVec 64) : RegFile :=
  ⟨fun i => if 1 ≤ i.toNat ∧ i.toNat ≤ 17 then r i.toNat else rf.regs i⟩

/-- The abstract state. -/
def mkS (s0 : State) (pc sp : BitVec 64) (m : Memory) (ps : PState) (r : Nat → BitVec 64) : State :=
  { s0 with regs := mkRegs s0.regs r, pc := pc, sp := sp, mem := m, pstate := ps }

section lemmas
variable (s0 : State) (pc sp : BitVec 64) (m : Memory) (ps : PState) (r : Nat → BitVec 64)

@[simp] theorem mkS_mem : (mkS s0 pc sp m ps r).mem = m := rfl
@[simp] theorem mkS_pc : (mkS s0 pc sp m ps r).pc = pc := rfl
@[simp] theorem mkS_sp : (mkS s0 pc sp m ps r).sp = sp := rfl
@[simp] theorem mkS_status : (mkS s0 pc sp m ps r).status = s0.status := rfl
@[simp] theorem mkS_pstate : (mkS s0 pc sp m ps r).pstate = ps := rfl
@[simp] theorem mkS_vregs : (mkS s0 pc sp m ps r).vregs = s0.vregs := rfl

theorem rd_gpr (i : BitVec 5) (h : Ok i) : (mkS s0 pc sp m ps r).readReg64 (.gpr i) = r i.toNat := by
  have h31 : (i == 31#5) = false := by
    have : i ≠ 31#5 := by intro e; subst e; simp [Ok] at h
    simpa using this
  simp only [State.readReg64, h31, mkS, RegFile.read, mkRegs]
  simp [Ok] at h; simp [h]

theorem rd_hi (i : BitVec 5) (h : 17 < i.toNat) :
    (mkS s0 pc sp m ps r).readReg64 (.gpr i) = s0.readReg64 (.gpr i) := by
  simp only [State.readReg64, mkS, RegFile.read, mkRegs]
  have : ¬ (1 ≤ i.toNat ∧ i.toNat ≤ 17) := by omega
  simp [this]

@[simp] theorem rd_xzr : (mkS s0 pc sp m ps r).readReg64 .xzr = 0#64 := rfl
@[simp] theorem rd_sp : (mkS s0 pc sp m ps r).readReg64 .sp = sp := rfl

theorem wr_gpr (i : BitVec 5) (h : Ok i) (v : BitVec 64) :
    (mkS s0 pc sp m ps r).writeReg64 (.gpr i) v = mkS s0 pc sp m ps (upd r i.toNat v) := by
  have h31 : (i == 31#5) = false := by
    have : i ≠ 31#5 := by intro e; subst e; simp [Ok] at h
    simpa using this
  simp only [mkS, State.writeReg64, h31, mkRegs, RegFile.write]
  simp only [Bool.false_eq_true, if_false]
  congr 2; funext j
  by_cases hj : j = i
  · subst hj; simp [Ok] at h; simp [h, upd]
  · have : j.toNat ≠ i.toNat := fun e => hj (BitVec.eq_of_toNat_eq e)
    simp [hj, upd, this]

@[simp] theorem wr_xzr (v : BitVec 64) : (mkS s0 pc sp m ps r).writeReg64 .xzr v = mkS s0 pc sp m ps r := rfl
@[simp] theorem wr_sp (v : BitVec 64) : (mkS s0 pc sp m ps r).writeReg64 .sp v = mkS s0 pc v m ps r := rfl
@[simp] theorem mkS_advancePC : (mkS s0 pc sp m ps r).advancePC = mkS s0 (pc + 4#64) sp m ps r := rfl
@[simp] theorem mkS_setPC (q : BitVec 64) : (mkS s0 pc sp m ps r).setPC q = mkS s0 q sp m ps r := rfl
@[simp] theorem mkS_setPState (q : PState) : (mkS s0 pc sp m ps r).setPState q = mkS s0 pc sp m q r := rfl
@[simp] theorem mkS_setMem (q : Memory) : (mkS s0 pc sp m ps r).setMem q = mkS s0 pc sp q ps r := rfl

end lemmas

/-! ## Steps utilities -/

theorem step_mkS {pl : Placement} {X : String → Option (State → State)} {s0 : State} {pc sp : BitVec 64} {m : Memory} {ps : PState}
    {r : Nat → BitVec 64} {inst : Instr} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some inst) {s' : State}
    (he : execInstWithSvc (evalSvc Syscall.standard) inst (mkS s0 pc sp m ps r) = s') :
    Step (prog pl X) (mkS s0 pc sp m ps r) s' := by
  have := Step.exec (prog := prog pl X) (s := mkS s0 pc sp m ps r) hrun hf
  rw [Program.evalInst] at this
  rwa [show (prog pl X).svc = Syscall.standard from rfl, he] at this

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Memory: byte writes, the written region, and the memory invariant `MemOk`

The routine writes only the accumulator bytes `[x0 + 24, x0 + 48)` (the region `W`). `MemOk s0 m`: every cell outside `W` is that of `s0.mem`, and
every byte of `W` is mapped read-write (not lazy-free, anonymity unchanged), as in `s0.mem`. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Arm64.Obj

section write8
variable (m : Memory) (a b : BitVec 64) (v : BitVec 8)

theorem cells_write8_ne (h : b ≠ a) : (m.write8 a v).cells b = m.cells b := by
  simp [Memory.write8, h]

theorem perm_write8 : (m.write8 a v).perm b = m.perm b := by
  by_cases h : b = a
  · subst h
    rcases hc : m.cells b with _ | ⟨_ | p, x⟩ <;>
      simp [Memory.write8, Memory.perm, Memory.rawPerm, hc, Perm.rwx]
  · simp [Memory.perm, cells_write8_ne m a b v h]

theorem lazy_write8 : (m.write8 a v).isLazyFree b = if b = a then false else m.isLazyFree b := by
  by_cases h : b = a
  · subst h
    rcases hc : m.cells b with _ | ⟨_ | p, x⟩ <;>
      simp [Memory.write8, Memory.isLazyFree, Memory.rawPerm, hc, Perm.rwx]
  · simp [Memory.isLazyFree, cells_write8_ne m a b v h, h]

theorem anon_write8 : (m.write8 a v).isAnon b = m.isAnon b := by
  by_cases h : b = a
  · subst h
    rcases hc : m.cells b with _ | ⟨_ | p, x⟩ <;>
      simp [Memory.write8, Memory.isAnon, Memory.rawPerm, hc, Perm.rwx]
  · simp [Memory.isAnon, cells_write8_ne m a b v h]

end write8

/-- The state address `x0` of the entry state. -/
abbrev X0 (s0 : State) : BitVec 64 := s0.readReg64 (.gpr 0#5)

/-- The written region: the accumulator bytes. -/
def W (s0 : State) (a : BitVec 64) : Prop :=
  InRegion (X0 s0 + 24#64) 24 a

def MemOk (s0 : State) (m : Memory) : Prop :=
  (∀ a, ¬ W s0 a → m.cells a = s0.mem.cells a) ∧
  (∀ a, W s0 a → m.perm a = some Perm.rw ∧ m.isLazyFree a = false ∧
    m.isAnon a = s0.mem.isAnon a ∧ s0.mem.perm a = some Perm.rw)

theorem memOk_write8 {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} (ha : W s0 a)
    (v : BitVec 8) : MemOk s0 (m.write8 a v) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have : b ≠ a := fun e => hb (e ▸ ha)
    rw [cells_write8_ne _ _ _ _ this]; exact hm.1 b hb
  · obtain ⟨h1, h2, h3, h4⟩ := hm.2 b hb
    refine ⟨by rw [perm_write8]; exact h1, ?_, by rw [anon_write8]; exact h3, h4⟩
    rw [lazy_write8]; split <;> simp_all

theorem read8_of_notW {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} (ha : ¬ W s0 a) :
    m.read8 a = s0.mem.read8 a := by
  simp [Memory.read8, hm.1 a ha]

theorem perm_of_notW {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} (ha : ¬ W s0 a) :
    m.perm a = s0.mem.perm a := by
  simp [Memory.perm, hm.1 a ha]

theorem lazy_of_notW {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} (ha : ¬ W s0 a) :
    m.isLazyFree a = s0.mem.isLazyFree a := by
  simp [Memory.isLazyFree, hm.1 a ha]

/-! ## Permission checks over ranges -/

theorem allPerm_of {m : Memory} {p : Option Perm → Bool} :
    ∀ (n : Nat) (a : BitVec 64), (∀ k < n, p (m.perm (a + BitVec.ofNat 64 k)) = true) →
      m.allPerm p a n = true
  | 0, _, _ => rfl
  | n + 1, a, h => by
    simp only [Memory.allPerm, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), allPerm_of n _ fun k hk => ?_⟩
    have := h (k + 1) (by omega)
    rwa [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm 1 k] at *

theorem allNoLazy_of {m : Memory} :
    ∀ (n : Nat) (a : BitVec 64), (∀ k < n, m.isLazyFree (a + BitVec.ofNat 64 k) = false) →
      m.allNoLazyFree a n = true
  | 0, _, _ => rfl
  | n + 1, a, h => by
    simp only [Memory.allNoLazyFree, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), allNoLazy_of n _ fun k hk => ?_⟩
    have := h (k + 1) (by omega)
    rwa [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm 1 k] at *

theorem canWrite_of {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} {n : Nat}
    (h : ∀ k < n, W s0 (a + BitVec.ofNat 64 k)) : m.canWrite a n = true :=
  allPerm_of n a fun k hk => by rw [(hm.2 _ (h k hk)).1]; rfl

theorem canRead_W {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} {n : Nat}
    (h : ∀ k < n, W s0 (a + BitVec.ofNat 64 k)) : m.canRead a n = true := by
  simp only [Memory.canRead, Bool.and_eq_true]
  exact ⟨allPerm_of n a fun k hk => by rw [(hm.2 _ (h k hk)).1]; rfl,
    allNoLazy_of n a fun k hk => (hm.2 _ (h k hk)).2.1⟩

/-- Readable in `s0.mem` and outside `W`: readable in `m`. -/
theorem canRead_notW {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} {n : Nat}
    (h : ∀ k < n, ¬ W s0 (a + BitVec.ofNat 64 k) ∧ (s0.mem.perm (a + BitVec.ofNat 64 k)).r = true ∧
      s0.mem.isLazyFree (a + BitVec.ofNat 64 k) = false) : m.canRead a n = true := by
  simp only [Memory.canRead, Bool.and_eq_true]
  exact ⟨allPerm_of n a fun k hk => by rw [perm_of_notW hm (h k hk).1]; exact (h k hk).2.1,
    allNoLazy_of n a fun k hk => by rw [lazy_of_notW hm (h k hk).1]; exact (h k hk).2.2⟩

/-! ## Code stays loaded -/

theorem codeLoaded_of {p : Program} {m0 m : Memory} (h : p.CodeLoaded m0)
    (hc : ∀ a, m0.perm a = some Perm.rx → m.cells a = m0.cells a) : p.CodeLoaded m := by
  unfold Program.CodeLoaded at h ⊢
  refine ⟨h.1, h.2.1, fun i hi => ?_⟩
  obtain ⟨e1, e2, e3⟩ := h.2.2 i hi
  have hcl := hc _ e2
  simp only [Memory.read8, Memory.perm, Memory.isLazyFree, hcl] at e1 e2 e3 ⊢
  exact ⟨e1, e2, e3⟩

/-- Everything the stepping lemmas need about memory `m`. -/
def Good (pl : Placement) (X : String → Option (State → State)) (s0 : State) (m : Memory) : Prop :=
  Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl ∧ (prog pl X).CodeLoaded s0.mem ∧ MemOk s0 m

theorem Good.codeLoaded {pl : Placement} {X : String → Option (State → State)} {s0 : State} {m : Memory}
    (hg : Good pl X s0 m) : (prog pl X).CodeLoaded m :=
  codeLoaded_of hg.2.1 fun a ha => hg.2.2.1 a fun hw => by
    have := (hg.2.2.2 a hw).2.2.2; rw [ha] at this; cases this

theorem Good.write8 {pl : Placement} {X : String → Option (State → State)} {s0 : State} {m : Memory}
    (hg : Good pl X s0 m) {a : BitVec 64} (ha : W s0 a) (v : BitVec 8) : Good pl X s0 (m.write8 a v) :=
  ⟨hg.1, hg.2.1, memOk_write8 hg.2.2 ha v⟩

end Poly1305DebianCtBlocks

end
end

section
section
/-! # The instruction at each address of `poly1305_blocks` (text offsets 0x1a0..0x2ac)

Each lemma is `rfl` after `fetch_word` and `patchedWord_plain` (no relocation lies inside the
function). Lemma `f_<k>` is function offset `k` (hex). -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Arm64 Arm64.Obj

set_option maxRecDepth 100000

theorem patchedWord_plain (pl : Placement) {off : Nat}
    (h : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocAt? off = none) :
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off = Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.wordAt off := by
  simp [CodeBlock.patchedWord, h]

section
variable {pl : Placement} {X : String → Option (State → State)} {s0 : State} {m : Memory}
  (hg : Good pl X s0 m)
include hg

theorem f_0 : (prog pl X).fetchMem m (pl.base + 416#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x07#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000010#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_4 : (prog pl X).fetchMem m (pl.base + 420#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_8 : (prog pl X).fetchMem m (pl.base + 424#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c : (prog pl X).fetchMem m (pl.base + 428#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x03#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000058#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_10 : (prog pl X).fetchMem m (pl.base + 432#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W32) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x03#5) 0x000#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_14 : (prog pl X).fetchMem m (pl.base + 436#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.ShiftType.LSL) 2) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_18 : (prog pl X).fetchMem m (pl.base + 440#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000020#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1c : (prog pl X).fetchMem m (pl.base + 444#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 2) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_20 : (prog pl X).fetchMem m (pl.base + 448#64) = some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.CondCode.NE)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_24 : (prog pl X).fetchMem m (pl.base + 452#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 62 61) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_28 : (prog pl X).fetchMem m (pl.base + 456#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) 62 61) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_2c : (prog pl X).fetchMem m (pl.base + 460#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x05#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.gpr 0x01#5) 0x0000000000000010#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_30 : (prog pl X).fetchMem m (pl.base + 464#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x04#5) 0x00000fffffffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_34 : (prog pl X).fetchMem m (pl.base + 468#64) = some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x04#5) 44) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_38 : (prog pl X).fetchMem m (pl.base + 472#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) 0x00000fffffffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_3c : (prog pl X).fetchMem m (pl.base + 476#64) = some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x05#5) 24) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_40 : (prog pl X).fetchMem m (pl.base + 480#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_44 : (prog pl X).fetchMem m (pl.base + 484#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_48 : (prog pl X).fetchMem m (pl.base + 488#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x07#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_4c : (prog pl X).fetchMem m (pl.base + 492#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_50 : (prog pl X).fetchMem m (pl.base + 496#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_54 : (prog pl X).fetchMem m (pl.base + 500#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_58 : (prog pl X).fetchMem m (pl.base + 504#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_5c : (prog pl X).fetchMem m (pl.base + 508#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_60 : (prog pl X).fetchMem m (pl.base + 512#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_64 : (prog pl X).fetchMem m (pl.base + 516#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_68 : (prog pl X).fetchMem m (pl.base + 520#64) = some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x11#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_6c : (prog pl X).fetchMem m (pl.base + 524#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_70 : (prog pl X).fetchMem m (pl.base + 528#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_74 : (prog pl X).fetchMem m (pl.base + 532#64) = some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x0f#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_78 : (prog pl X).fetchMem m (pl.base + 536#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_7c : (prog pl X).fetchMem m (pl.base + 540#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_80 : (prog pl X).fetchMem m (pl.base + 544#64) = some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x0e#5) 44) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_84 : (prog pl X).fetchMem m (pl.base + 548#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_88 : (prog pl X).fetchMem m (pl.base + 552#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_8c : (prog pl X).fetchMem m (pl.base + 556#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_90 : (prog pl X).fetchMem m (pl.base + 560#64) = some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x11#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_94 : (prog pl X).fetchMem m (pl.base + 564#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_98 : (prog pl X).fetchMem m (pl.base + 568#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_9c : (prog pl X).fetchMem m (pl.base + 572#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a0 : (prog pl X).fetchMem m (pl.base + 576#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x11#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a4 : (prog pl X).fetchMem m (pl.base + 580#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x0e#5) 0x00000fffffffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a8 : (prog pl X).fetchMem m (pl.base + 584#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ac : (prog pl X).fetchMem m (pl.base + 588#64) = some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x03#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b0 : (prog pl X).fetchMem m (pl.base + 592#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b4 : (prog pl X).fetchMem m (pl.base + 596#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b8 : (prog pl X).fetchMem m (pl.base + 600#64) = some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x07#5) (Arm64.CondCode.CC)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_bc : (prog pl X).fetchMem m (pl.base + 604#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c0 : (prog pl X).fetchMem m (pl.base + 608#64) = some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x07#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c4 : (prog pl X).fetchMem m (pl.base + 612#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x06#5) 0x00000fffffffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c8 : (prog pl X).fetchMem m (pl.base + 616#64) = some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x06#5) 44) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_cc : (prog pl X).fetchMem m (pl.base + 620#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d0 : (prog pl X).fetchMem m (pl.base + 624#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d4 : (prog pl X).fetchMem m (pl.base + 628#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x06#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d8 : (prog pl X).fetchMem m (pl.base + 632#64) = some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) (Arm64.CondCode.CC)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_dc : (prog pl X).fetchMem m (pl.base + 636#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e0 : (prog pl X).fetchMem m (pl.base + 640#64) = some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x05#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e4 : (prog pl X).fetchMem m (pl.base + 644#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x04#5) 0x000003ffffffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e8 : (prog pl X).fetchMem m (pl.base + 648#64) = some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x04#5) 42) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ec : (prog pl X).fetchMem m (pl.base + 652#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 2) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f0 : (prog pl X).fetchMem m (pl.base + 656#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x11#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f4 : (prog pl X).fetchMem m (pl.base + 660#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x03#5) 0x00000fffffffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f8 : (prog pl X).fetchMem m (pl.base + 664#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSR) 44) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_fc : (prog pl X).fetchMem m (pl.base + 668#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_100 : (prog pl X).fetchMem m (pl.base + 672#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0xffffffffffffff2c#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_104 : (prog pl X).fetchMem m (pl.base + 676#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x03#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000018#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_108 : (prog pl X).fetchMem m (pl.base + 680#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0f#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000028#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_10c : (prog pl X).fetchMem m (pl.base + 684#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

end

end Poly1305DebianCtBlocks

end
end

section
section
/-! # One reachability lemma per instruction shape of `poly1305_blocks`

`Reach pl X Q s`: from `s` the placed program reaches a state satisfying `Q`. Each `r_*` lemma
reduces `Reach` at an abstract state to `Reach` at its successor. Register indices are generic
(`Ok` side conditions are discharged by `decide`). Values written to registers are stated as
`BitVec.ofNat 64 (Nat expression in the operands' toNat)`. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Arm64.Obj

theorem pc_add (b : BitVec 64) (x y : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

section
variable (svc : State → State) (s : State)
theorem ex_addSubImm (w : RegWidth) (op : AddSubOp) (rd rn : Reg) (imm : BitVec 12) (sh : Bool) :
    execInstWithSvc svc (.addSubImm w op rd rn imm sh) s = execAddSubImm w op rd rn imm sh s := rfl
theorem ex_addSubShift (w : RegWidth) (op : AddSubOp) (rd rn rm : Reg) (sh : ShiftType) (a : Nat) :
    execInstWithSvc svc (.addSubShift w op rd rn rm sh a) s = execAddSubShift w op rd rn rm sh a s := rfl
theorem ex_addSubCarry (w : RegWidth) (op : AddSubOp) (rd rn rm : Reg) :
    execInstWithSvc svc (.addSubCarry w op rd rn rm) s = execAddSubCarry w op rd rn rm s := rfl
theorem ex_logicalImm (w : RegWidth) (op : LogicalOp) (rd rn : Reg) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm w op rd rn mask) s = execLogicalImm w op rd rn mask s := rfl
theorem ex_bitfield (w : RegWidth) (op : BitfieldOp) (rd rn : Reg) (a b : Nat) :
    execInstWithSvc svc (.bitfield w op rd rn a b) s = execBitfield w op rd rn a b s := rfl
theorem ex_dataProc3 (w : RegWidth) (op : DataProc3Op) (rd rn rm ra : Reg) :
    execInstWithSvc svc (.dataProc3 w op rd rn rm ra) s = execDataProc3 w op rd rn rm ra s := rfl
theorem ex_condSelect (w : RegWidth) (op : CondSelectOp) (rd rn rm : Reg) (c : CondCode) :
    execInstWithSvc svc (.condSelect w op rd rn rm c) s = execCondSelect w op rd rn rm c s := rfl
theorem ex_extr (rd rn rm : Reg) (lsb : Nat) :
    execInstWithSvc svc (.extr .W64 rd rn rm lsb) s =
      (s.writeReg .W64 rd (((s.readReg64 rn ++ s.readReg64 rm) >>> (lsb % 64)).truncate 64)).advancePC :=
  rfl
theorem ex_bCond (c : CondCode) (off : BitVec 64) :
    execInstWithSvc svc (.bCond c off) s =
      if ConditionHolds c s.pstate then s.setPC (s.pc + off) else s.advancePC := rfl
theorem ex_ldr (w : RegWidth) (sz : MemWidth) (sg : Bool) (rt : Reg) (a : AddrMode) :
    execInstWithSvc svc (.ldr w sz sg rt a) s = execLdr w sz sg rt a s := rfl
theorem ex_str (sz : MemWidth) (rt : Reg) (a : AddrMode) :
    execInstWithSvc svc (.str sz rt a) s = execStr sz rt a s := rfl
theorem ex_ldp (w : RegWidth) (sg : Bool) (r1 r2 : Reg) (a : AddrMode) :
    execInstWithSvc svc (.ldp w sg r1 r2 a) s = execLdp w sg r1 r2 a s := rfl
theorem ex_stp (w : RegWidth) (r1 r2 : Reg) (a : AddrMode) :
    execInstWithSvc svc (.stp w r1 r2 a) s = execStp w r1 r2 a s := rfl
theorem ex_ret (rn : Reg) : execInstWithSvc svc (.ret rn) s = s.setPC (s.readReg64 rn) := rfl
end

theorem mkS_upd_congr {s0 : State} {pc sp : BitVec 64} {m : Memory} {ps : PState}
    {r : Nat → BitVec 64} {k : Nat} {v v' : BitVec 64} (h : v.toNat = v'.toNat) :
    mkS s0 pc sp m ps (upd r k v) = mkS s0 pc sp m ps (upd r k v') := by
  rw [BitVec.eq_of_toNat_eq h]

/-- The value of the carry flag as a number. -/
def cv (b : Bool) : Nat := if b then 1 else 0

theorem extr_nat (n k lsb : Nat) (h : lsb ≤ 64) :
    (n * 2 ^ 64 + k) / 2 ^ lsb = k / 2 ^ lsb + n * 2 ^ (64 - lsb) := by
  have e : 2 ^ 64 = 2 ^ lsb * 2 ^ (64 - lsb) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.add_comm, Nat.mul_left_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]

variable {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop} {s0 : State}
  {pc sp : BitVec 64} {m : Memory} {ps : PState} {r : Nat → BitVec 64}

/-! ## Arithmetic and logic -/

/-! ## Branches -/

/-! ## Loads and stores (64-bit) -/

/-! ## Instructions only the GCC build uses -/

end Poly1305DebianCtBlocks

end
end

section
section
/-! # The arithmetic of one block, independent of the machine

Radix `2^44` limbs (44, 44, 42 bits). `a0 a1 a2`: the limbs of `h + block + hibit` (unreduced);
`r0 r1 r2`: the key limbs, `s1 = 20 r1`, `s2 = 20 r2`. The code forms the column sums
`D0 D1 D2` from 64 × 64 → 128-bit products, carries (`E1`, `E2`), folds the top carry back
times 5 (`F`), and leaves the new limbs `N0 N1 N2`. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)
open Poly1305Boringssl

section
variable (a0 a1 a2 r0 r1 r2 : Nat)

end

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Chain helpers: pc normalization, naming computed values, carries as numbers -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Arm64.Obj

end Poly1305DebianCtBlocks

end
end

section
section
/-! # One iteration of the block loop (function offsets 0x2c..0xf8)

Entered at `0x2c` with the message pointer in `x1`, the key limbs `r0, r1, r2` in `x8, x9, x12`,
`s1 = 20 r1`, `s2 = 20 r2` in `x11, x10`, the hibit flag (`0` or `1`) in `x13` and the accumulator
limbs `h0, h1, h2` in `x7, x3, x15`; leaves the new limbs in the same registers and `x1 + 16` in
`x1` at `0xfc` (the loop test `cmp x1, x2`). `x2` and the key registers are untouched. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Arm64 Arm64.Obj

end Poly1305DebianCtBlocks

end
end

section
section
/-! # 64-bit words over byte writes; addresses of the state -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Arm64.Obj

theorem add_ofNat_inj (a : BitVec 64) {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    a + BitVec.ofNat 64 x = a + BitVec.ofNat 64 y ↔ x = y := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp [BitVec.toNat_add] at this; omega
  · rintro rfl; rfl

theorem inRegion_off (a : BitVec 64) (c n x : Nat) (h1 : c ≤ x) (h2 : x < c + n) (hx : x < 2 ^ 64) :
    InRegion (a + BitVec.ofNat 64 c) n (a + BitVec.ofNat 64 x) := by
  unfold InRegion
  have : a + BitVec.ofNat 64 x - (a + BitVec.ofNat 64 c) = BitVec.ofNat 64 (x - c) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_add]
    omega
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

/-- An accumulator byte is in `W`. -/
theorem W_h (s0 : State) (x : Nat) (h1 : 24 ≤ x) (h2 : x < 48) : W s0 (X0 s0 + BitVec.ofNat 64 x) := by
  have := inRegion_off (X0 s0) 24 24 x h1 (by omega) (by omega)
  unfold W; simpa using this

theorem write64_eq (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    m.write64 a v = (((((((m.write8 (a + BitVec.ofNat 64 0) (v.extractLsb' 0 8)).write8
      (a + BitVec.ofNat 64 1) (v.extractLsb' 8 8)).write8 (a + BitVec.ofNat 64 2) (v.extractLsb' 16 8)).write8
      (a + BitVec.ofNat 64 3) (v.extractLsb' 24 8)).write8 (a + BitVec.ofNat 64 4) (v.extractLsb' 32 8)).write8
      (a + BitVec.ofNat 64 5) (v.extractLsb' 40 8)).write8 (a + BitVec.ofNat 64 6) (v.extractLsb' 48 8)).write8
      (a + BitVec.ofNat 64 7) (v.extractLsb' 56 8) := rfl

theorem good_write64 {pl : Placement} {X : String → Option (State → State)} {s0 : State}
    {m : Memory} (hg : Good pl X s0 m) {a : BitVec 64} (ha : ∀ k < 8, W s0 (a + BitVec.ofNat 64 k))
    (v : BitVec 64) : Good pl X s0 (m.write64 a v) := by
  rw [write64_eq]
  exact Good.write8 (Good.write8 (Good.write8 (Good.write8 (Good.write8 (Good.write8
    (Good.write8 (Good.write8 hg (ha 0 (by decide)) _) (ha 1 (by decide)) _) (ha 2 (by decide)) _)
    (ha 3 (by decide)) _) (ha 4 (by decide)) _) (ha 5 (by decide)) _) (ha 6 (by decide)) _)
    (ha 7 (by decide)) _

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Byte lists: the block loop's specification `blocksAcc`, little-endian words -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Poly1305Boringssl

end Poly1305DebianCtBlocks

end
end

section
section
/-! # The entry facts and the prologue of `poly1305_blocks` (function offsets 0x00..0x28) -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)
open Arm64 Arm64.Obj Poly1305Boringssl

/-- The entry registers as a scratch-register function. -/
def r0 (s0 : State) : Nat → BitVec 64 := fun k => s0.regs.regs (BitVec.ofNat 5 k)

theorem mkS_self (s0 : State) : mkS s0 s0.pc s0.sp s0.mem s0.pstate (r0 s0) = s0 := by
  have hr : mkRegs s0.regs (r0 s0) = s0.regs := by
    cases hs : s0.regs with
    | mk f =>
      simp only [mkRegs, r0, hs]
      congr 1; funext i
      split <;> simp
  simp only [mkS, hr]

theorem r0_eq (s0 : State) (k : Nat) (h : k < 31 := by decide) :
    r0 s0 k = s0.readReg64 (.gpr (BitVec.ofNat 5 k)) := by
  simp only [r0, State.readReg64, RegFile.read]
  have : (BitVec.ofNat 5 k == 31#5) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  simp [this]

section helpers
variable {s0 : State} {m : Memory}

theorem h_canWrite (hm : MemOk s0 m) (off : Nat) (h1 : 24 ≤ off) (h2 : off + 8 ≤ 48) :
    m.canWrite (X0 s0 + BitVec.ofNat 64 off) 8 = true :=
  canWrite_of hm fun k hk => by rw [pc_add]; exact W_h s0 _ (by omega) (by omega)

theorem h_canRead (hm : MemOk s0 m) (off : Nat) (h1 : 24 ≤ off) (h2 : off + 8 ≤ 48) :
    m.canRead (X0 s0 + BitVec.ofNat 64 off) 8 = true :=
  canRead_W hm fun k hk => by rw [pc_add]; exact W_h s0 _ (by omega) (by omega)

theorem add8 (a : BitVec 64) (x : Nat) : a + BitVec.ofNat 64 x + 8#64 = a + BitVec.ofNat 64 (x + 8) :=
  pc_add a x 8

theorem good_h {pl : Placement} {X : String → Option (State → State)} (hg : Good pl X s0 m)
    (off : Nat) (h1 : 24 ≤ off) (h2 : off + 8 ≤ 48) (v : BitVec 64) :
    Good pl X s0 (m.write64 (X0 s0 + BitVec.ofNat 64 off) v) :=
  good_write64 hg (fun k hk => by rw [pc_add]; exact W_h s0 _ (by omega) (by omega)) v

end helpers

variable {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop} {s0 : State}

end Poly1305DebianCtBlocks

end
end

section
section
/-! # The epilogue (function offsets 0x104..0x10c) and the block loop (induction on the
remaining message; loop test `cmp x1, x2; b.ne` at 0xfc..0x100) -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)
open Arm64 Arm64.Obj Poly1305Boringssl

variable {pl : Placement} {X : String → Option (State → State)} {s0 : State}

/-- The message bytes at `X1`: outside `W`, readable at entry. -/
def MsgOk (s0 : State) (X1 : BitVec 64) (n : Nat) : Prop :=
  ∀ j < n, ¬ W s0 (X1 + BitVec.ofNat 64 j) ∧ (s0.mem.perm (X1 + BitVec.ofNat 64 j)).r = true ∧
    s0.mem.isLazyFree (X1 + BitVec.ofNat 64 j) = false

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Separation-logic glue: heap cells of the precondition, and `modHeap` for the postcondition

`modHeap h m` is `h` with every read-write byte replaced by the byte of memory `m`. If `h` matched
the entry memory and `m` differs only on read-write bytes of `h` (the region `W`), then
`modHeap h m` matches `m`, and it satisfies the postcondition's assertions. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Arm64.Obj

def modCell (m : Memory) (a : BitVec 64) : Option HeapCell → Option HeapCell
  | some (.rw _) => some (.rw (m.read8 a))
  | c => c

def modHeap (h : Heap) (m : Memory) : Heap :=
  { h with phys := fun a => modCell m a (h.phys a) }

theorem modCell_none (m : Memory) (a : BitVec 64) : modCell m a none = none := rfl

theorem modHeap_union (h1 h2 : Heap) (m : Memory) :
    modHeap (h1.union h2) m = (modHeap h1 m).union (modHeap h2 m) := by
  apply Heap.ext
  · funext a
    simp only [modHeap, Heap.union]
    rcases h1.phys a with _ | c <;> simp [modCell_none]
    rcases c <;> simp [modCell]
  all_goals rfl

theorem modHeap_disjoint {h1 h2 : Heap} (hd : h1.Disjoint h2) (m : Memory) :
    (modHeap h1 m).Disjoint (modHeap h2 m) := by
  refine ⟨fun a => ?_, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩
  rcases hd.1 a with e | e | ⟨b, e1, e2⟩
  · exact Or.inl (by simp [modHeap, e, modCell_none])
  · exact Or.inr (Or.inl (by simp [modHeap, e, modCell_none]))
  · exact Or.inr (Or.inr ⟨b, by simp [modHeap, e1, modCell], by simp [modHeap, e2, modCell]⟩)

theorem modHeap_empty (m : Memory) : modHeap Heap.empty m = Heap.empty := by
  apply Heap.ext <;> rfl

/-! ## Cells -/

theorem cell_union_left {h1 h2 : Heap} {a : BitVec 64} {c : HeapCell} (h : h1.phys a = some c) :
    (h1.union h2).phys a = some c := by
  simp [Heap.union, h]

theorem cell_union_right_rw {h1 h2 : Heap} (hd : h1.Disjoint h2) {a : BitVec 64} {b : BitVec 8}
    (h : h2.phys a = some (.rw b)) : (h1.union h2).phys a = some (.rw b) := by
  rcases hd.1 a with h0 | h0 | ⟨b', e1, e2⟩
  · simp [Heap.union, h0, h]
  · rw [h] at h0; cases h0
  · rw [h] at e2; cases e2

theorem cell_union_right_ro {h1 h2 : Heap} (hd : h1.Disjoint h2) {a : BitVec 64} {b : BitVec 8}
    (h : h2.phys a = some (.ro b)) : (h1.union h2).phys a = some (.ro b) := by
  rcases hd.1 a with h0 | h0 | ⟨b', e1, e2⟩
  · simp [Heap.union, h0, h]
  · rw [h] at h0; cases h0
  · rw [h] at e2; cases e2; simp [Heap.union, e1]

theorem bytes_rw : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap),
    (pointsToBytes a bs).holds h → ∀ i (hi : i < bs.length),
      h.phys (a + BitVec.ofNat 64 i) = some (.rw bs[i])
  | [], _, _, _, i, hi => by simp at hi
  | b :: bs, a, h, hs, i, hi => by
    obtain ⟨h1, h2, hd, rfl, p1, p2⟩ := hs
    cases i with
    | zero =>
      simp only [pointsTo8] at p1; subst p1
      exact cell_union_left (by simp [Heap.singleton])
    | succ i =>
      have := bytes_rw bs (a + 1#64) h2 p2 i (by simp at hi; omega)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm] at this
      exact cell_union_right_rw hd (by simpa using this)

theorem bytes_ro : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap),
    (pointsToBytesRO a bs).holds h → ∀ i (hi : i < bs.length),
      h.phys (a + BitVec.ofNat 64 i) = some (.ro bs[i])
  | [], _, _, _, i, hi => by simp at hi
  | b :: bs, a, h, hs, i, hi => by
    obtain ⟨h1, h2, hd, rfl, p1, p2⟩ := hs
    cases i with
    | zero =>
      simp only [pointsTo8RO] at p1; subst p1
      exact cell_union_left (by simp [Heap.singletonRO])
    | succ i =>
      have := bytes_ro bs (a + 1#64) h2 p2 i (by simp at hi; omega)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm] at this
      exact cell_union_right_ro hd (by simpa using this)

/-- Read-only bytes have no read-write cells: `modHeap` leaves them alone. -/
theorem modHeap_ro : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap) (m : Memory),
    (pointsToBytesRO a bs).holds h → modHeap h m = h
  | [], _, h, m, hs => by
    simp only [pointsToBytesRO, emp] at hs; subst hs; exact modHeap_empty m
  | b :: bs, a, h, m, hs => by
    obtain ⟨h1, h2, hd, rfl, p1, p2⟩ := hs
    rw [modHeap_union, modHeap_ro bs _ h2 m p2]
    simp only [pointsTo8RO] at p1; subst p1
    congr 1
    apply Heap.ext
    · funext x; simp only [modHeap, Heap.singletonRO]; split <;> rfl
    all_goals rfl

/-- `modHeap` of owned bytes: owned bytes holding what `m` holds there. -/
theorem modHeap_bytes : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap) (m : Memory),
    (pointsToBytes a bs).holds h →
      (pointsToBytes a ((List.range bs.length).map fun j => m.read8 (a + BitVec.ofNat 64 j))).holds
        (modHeap h m)
  | [], _, h, m, hs => by
    simp only [pointsToBytes, emp] at hs; subst hs
    simp only [List.length_nil, List.range_zero, List.map_nil, modHeap_empty]; rfl
  | b :: bs, a, h, m, hs => by
    obtain ⟨h1, h2, hd, rfl, p1, p2⟩ := hs
    rw [modHeap_union]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine ⟨_, _, modHeap_disjoint hd m, rfl, ?_, ?_⟩
    · simp only [pointsTo8] at p1 ⊢; subst p1
      apply Heap.ext
      · funext x; simp only [modHeap, Heap.singleton]
        split <;> rename_i e
        · subst e; simp [modCell]
        · rfl
      all_goals rfl
    · have := modHeap_bytes bs (a + 1#64) h2 m p2
      convert this using 3
      funext j
      simp only [Function.comp]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

/-- `modHeap h m` matches `m` when `h` matched `s0.mem`, `m` differs from `s0.mem` only on `W`,
    and `W` lies in the read-write cells of `h`. -/
theorem modHeap_matches {s0 : State} {h : Heap} {m : Memory} (hm : h.Matches s0.mem)
    (hok : MemOk s0 m) (hW : ∀ a, W s0 a → ∃ b, h.phys a = some (.rw b)) :
    (modHeap h m).Matches m := by
  have perm_eq : ∀ a, m.perm a = s0.mem.perm a := by
    intro a
    by_cases w : W s0 a
    · rw [(hok.2 a w).1, (hok.2 a w).2.2.2]
    · exact perm_of_notW hok w
  have anon_eq : ∀ a, m.isAnon a = s0.mem.isAnon a := by
    intro a
    by_cases w : W s0 a
    · exact (hok.2 a w).2.2.1
    · simp [Memory.isAnon, hok.1 a w]
  refine ⟨fun a c hc => ?_, hm.2.1, fun a ha => ?_⟩
  · have hca := hm.1 a
    simp only [modHeap] at hc
    by_cases w : W s0 a
    · obtain ⟨b, hb⟩ := hW a w
      rw [hb] at hc; simp only [modCell] at hc; cases hc
      exact ⟨rfl, (hok.2 a w).1, (hok.2 a w).2.1⟩
    · have hcell := hok.1 a w
      have r8 : m.read8 a = s0.mem.read8 a := by simp [Memory.read8, hcell]
      have pm : m.perm a = s0.mem.perm a := by simp [Memory.perm, hcell]
      have lz : m.isLazyFree a = s0.mem.isLazyFree a := by simp [Memory.isLazyFree, hcell]
      rcases e : h.phys a with _ | c'
      · rw [e] at hc; cases hc
      · rw [e] at hc
        have := hca c' e
        rcases c' with b | b | b | _ | _ <;> simp only [modCell] at hc <;> cases hc <;>
          simp only [r8, pm, lz] at this ⊢ <;> first | exact this | exact ⟨trivial, this.2⟩
  · have := hm.2.2 a ha
    rw [perm_eq, anon_eq]; exact this

end Poly1305DebianCtBlocks

end
end

section
section
/-! # `poly1305_blocks` meets `blocksSpec`: `Poly1305DebianCtBlocks.goal` -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)
open Arm64 Arm64.Obj Poly1305Boringssl

variable {pl : Placement} {X : String → Option (State → State)} {s0 : State}

/-- Two disjoint heaps do not both own a byte when one owns it read-write. -/
theorem disj_rw {h h' : Heap} (hd : h.Disjoint h') {a : BitVec 64} {b : BitVec 8} {c : HeapCell}
    (h1 : h.phys a = some (.rw b)) (h2 : h'.phys a = some c) : False := by
  rcases hd.1 a with z | z | ⟨_, z1, z2⟩
  · rw [h1] at z; cases z
  · rw [h2] at z; cases z
  · rw [h1] at z1; cases z1

theorem inRegion_eq {b a : BitVec 64} {n : Nat} (h : InRegion b n a) :
    a = b + BitVec.ofNat 64 (a - b).toNat ∧ (a - b).toNat < n := by
  refine ⟨?_, h⟩
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

theorem not_inRegion_h (A : BitVec 64) (k : Nat) (hk : k < 24 ∨ (48 ≤ k ∧ k < 2 ^ 32)) :
    ¬ InRegion (A + 24#64) 24 (A + BitVec.ofNat 64 k) := by
  unfold InRegion
  simp [BitVec.toNat_sub, BitVec.toNat_add]
  omega

/-- A read-write or read-only cell. -/
def Own (c : Option HeapCell) (b : BitVec 8) : Prop := c = some (.rw b) ∨ c = some (.ro b)

theorem own_left {h1 h2 : Heap} {a : BitVec 64} {b : BitVec 8} (h : Own (h1.phys a) b) :
    Own ((h1.union h2).phys a) b := by
  rcases h with h | h
  · exact Or.inl (cell_union_left h)
  · exact Or.inr (cell_union_left h)

theorem own_right {h1 h2 : Heap} (hd : h1.Disjoint h2) {a : BitVec 64} {b : BitVec 8}
    (h : Own (h2.phys a) b) : Own ((h1.union h2).phys a) b := by
  rcases h with h | h
  · exact Or.inl (cell_union_right_rw hd h)
  · exact Or.inr (cell_union_right_ro hd h)

theorem own_matches {h : Heap} {m : Memory} (hm : h.Matches m) {a : BitVec 64} {b : BitVec 8}
    (hc : Own (h.phys a) b) : m.read8 a = b ∧ (m.perm a).r = true ∧ m.isLazyFree a = false := by
  rcases hc with hc | hc
  · have := hm.1 a _ hc
    exact ⟨this.1, by rw [this.2.1]; rfl, this.2.2⟩
  · exact hm.1 a _ hc

theorem disj_own {h h' : Heap} (hd : h.Disjoint h') {a : BitVec 64} {b b' : BitVec 8}
    (h1 : h.phys a = some (.rw b)) (h2 : Own (h'.phys a) b') : False := by
  rcases h2 with h2 | h2
  · exact disj_rw hd h1 h2
  · exact disj_rw hd h1 h2

theorem bytesIn_cell {ro : Bool} {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap}
    (hb : (bytesIn ro a bs).holds h) (k : Nat) (hk : k < bs.length) :
    h.phys (a + BitVec.ofNat 64 k) = some (if ro then .ro bs[k] else .rw bs[k]) := by
  cases ro
  · exact bytes_rw bs a h hb k hk
  · exact bytes_ro bs a h hb k hk

theorem bytesIn_mod {ro : Bool} {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap} (m : Memory)
    (hb : (bytesIn ro a bs).holds h)
    (hv : ∀ k (hk : k < bs.length), m.read8 (a + BitVec.ofNat 64 k) = bs[k]) :
    (bytesIn ro a bs).holds (modHeap h m) := by
  cases ro
  · have := modHeap_bytes bs a h m hb
    have e : (List.range bs.length).map (fun j => m.read8 (a + BitVec.ofNat 64 j)) = bs := by
      apply List.ext_getElem (by simp)
      intro j h1 h2; simp only [List.getElem_map, List.getElem_range]; exact hv j h2
    rw [e] at this; exact this
  · rw [modHeap_ro bs a h m hb]; exact hb

theorem modHeap_frame {s0 : State} {h1 h2 : Heap} {mF : Memory} (hd : h1.Disjoint h2)
    (hm : (h1.union h2).Matches s0.mem) (hok : MemOk s0 mF)
    (wdom : ∀ a, W s0 a → ∃ b, h1.phys a = some (.rw b)) : modHeap h2 mF = h2 := by
  apply Heap.ext
  · funext a
    simp only [modHeap]
    rcases e : h2.phys a with _ | ⟨b | b | b | _ | _⟩ <;> try rfl
    -- a read-write byte of the frame lies outside `W` and is unchanged
    have h1a : h1.phys a = none := by
      rcases hd.1 a with z | z | ⟨c, z1, z2⟩
      · exact z
      · rw [e] at z; cases z
      · rw [e] at z2; cases z2
    have nw : ¬ W s0 a := fun w => by
      obtain ⟨c, hc⟩ := wdom a w; rw [h1a] at hc; cases hc
    have := hm.1 a _ (cell_union_right_rw hd e)
    simp only [modCell, read8_of_notW hok nw, this.1]
  all_goals rfl


end Poly1305DebianCtBlocks

end
end

end
end

section
section
/-! # One `Step` lemma per instruction shape of `poly1305_blocks`

Generated from the `r_…` reach lemmas of the functional proof (`Port.lean`): each `t_…` states the
step from `mkS s0 pc …` to its successor. The flag-setting and branch lemmas are written by hand. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Arm64.Obj

variable {pl : Placement} {X : String → Option (State → State)} {s0 : State}
  {pc sp : BitVec 64} {m : Memory} {ps : PState} {r : Nat → BitVec 64}

/-! ## Arithmetic and logic -/

/-- `add xd, xn, xm, lsl #a`. -/
theorem t_addLsl {d n k : BitVec 5} {a : Nat} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSL a))
    (ha : a < 64 := by decide)
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat * 2 ^ a)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_addSubShift]
  simp only [execAddSubShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, shiftVal, shift64]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  refine mkS_upd_congr ?_
  simp [AddWithCarry64, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt ha]
  omega

/-- `add xd, xn, xm, lsr #a`. -/
theorem t_addLsr {d n k : BitVec 5} {a : Nat} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSR a))
    (ha : a < 64 := by decide)
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat / 2 ^ a)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_addSubShift]
  simp only [execAddSubShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, shiftVal, shift64]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  refine mkS_upd_congr ?_
  have hy : (r k.toNat).toNat % 36893488147419103232 = (r k.toNat).toNat :=
    Nat.mod_eq_of_lt (by have := (r k.toNat).isLt; omega)
  simp [AddWithCarry64, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt ha, hy]
  omega

/-- `adc xd, xn, xm`. -/
theorem t_adc {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubCarry .W64 .ADD (.gpr d) (.gpr n) (.gpr k)))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat + cv ps.c)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_addSubCarry]
  simp only [execAddSubCarry, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, mkS_pstate]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  refine mkS_upd_congr ?_
  cases ps.c <;> simp [AddWithCarry64, BitVec.toNat_add, BitVec.toNat_setWidth, cv] <;> omega

/-- `cinc xd, xn, hs` (`csinc xd, xn, xn, lo`). -/
theorem t_cinc {d n : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.condSelect .W64 .CSINC (.gpr d) (.gpr n) (.gpr n) .CC))
    (hd : Ok d := by decide) (hn : Ok n := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + cv ps.c)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_condSelect]
  simp only [execCondSelect, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, mkS_pstate, ConditionHolds]
  cases ps.c <;> simp [wr_gpr _ _ _ _ _ _ _ hd, State.writeReg, cv] <;> refine mkS_upd_congr ?_ <;>
    simp [BitVec.toNat_add]

/-- `mul xd, xn, xm` (`madd xd, xn, xm, xzr`). -/
theorem t_mul {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.dataProc3 .W64 .MADD (.gpr d) (.gpr n) (.gpr k) .xzr))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat * (r k.toNat).toNat)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_dataProc3]
  simp only [execDataProc3, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk, rd_xzr,
    State.writeReg, wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  refine mkS_upd_congr ?_
  simp [BitVec.toNat_mul]

/-- `umulh xd, xn, xm`. -/
theorem t_umulh {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.dataProc3 .W64 .UMULH (.gpr d) (.gpr n) (.gpr k) .xzr))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat * (r k.toNat).toNat / 2 ^ 64)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_dataProc3]
  simp only [execDataProc3, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    State.writeReg, wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  refine mkS_upd_congr ?_
  have hxy : (r n.toNat).toNat * (r k.toNat).toNat < 340282366920938463463374607431768211456 := by
    have := Nat.mul_lt_mul'' (r n.toNat).isLt (r k.toNat).isLt
    simpa using this
  simp [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hxy]

/-- `extr xd, xn, xm, #lsb`: bits `lsb ..< lsb + 64` of `xn:xm`. -/
theorem t_extr {d n k : BitVec 5} {lsb : Nat} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.extr .W64 (.gpr d) (.gpr n) (.gpr k) lsb))
    (hl : 0 < lsb ∧ lsb < 64 := by decide)
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r k.toNat).toNat / 2 ^ lsb + (r n.toNat).toNat * 2 ^ (64 - lsb))))) := by
  refine step_mkS hrun hf ?_
  rw [ex_extr]
  simp only [State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    State.writeReg, wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  refine mkS_upd_congr ?_
  have hk' := (r k.toNat).isLt
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl.2, Nat.shiftRight_eq_div_pow]
  rw [← Nat.shiftLeft_add_eq_or_of_lt hk', Nat.shiftLeft_eq, extr_nat _ _ _ hl.2.le]

/-- `and xd, xn, #(2^k - 1)`. -/
theorem t_andMask {d n : BitVec 5} {mask : BitVec 64} (k : Nat) (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.logicalImm .W64 .AND (.gpr d) (.gpr n) mask))
    (hm : mask = BitVec.ofNat 64 (2 ^ k - 1) := by decide) (hk : k < 64 := by decide)
    (hd : Ok d := by decide) (hn : Ok n := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat % 2 ^ k)))) := by
  subst hm
  refine step_mkS hrun hf ?_
  rw [ex_logicalImm]
  simp only [execLogicalImm, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, evalLogical,
    State.writeReg, wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  refine mkS_upd_congr ?_
  have h1 : 2 ^ k - 1 < 2 ^ 64 := by
    have := Nat.pow_lt_pow_right (show 1 < 2 by decide) hk
    omega
  have h2 := (r n.toNat).isLt
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
    Nat.and_two_pow_sub_one_eq_mod]
  have : (r n.toNat).toNat % 2 ^ k < 2 ^ 64 := lt_of_le_of_lt (Nat.mod_le _ _) h2
  rw [Nat.mod_eq_of_lt this]

/-- `lsl xd, xn, #2` (`ubfm xd, xn, #62, #61`). -/
theorem t_lsl2 {d n : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bitfield .W64 .UBFM (.gpr d) (.gpr n) 62 61))
    (hd : Ok d := by decide) (hn : Ok n := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat * 4)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_bitfield]
  simp only [execBitfield, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, evalBitfield, State.writeReg,
    wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  simp only [Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, beq_self_eq_true, Bool.and_self, if_true,
    show (BitfieldOp.UBFM == BitfieldOp.UBFM) = true from rfl]
  simp
  refine mkS_upd_congr ?_
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-! ## Branches -/

theorem t_ret (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ret (.gpr 0x1e#5))) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (s0.readReg64 (.gpr 0x1e#5)) sp m ps r) :=
  step_mkS hrun hf (by
    rw [ex_ret, rd_hi _ _ _ _ _ _ _ (by decide)]; simp)

/-! ## Loads and stores (64-bit) -/

/-- `ldp xt1, xt2, [xb, #off]`. -/
theorem t_ldp64 {t1 t2 b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldp .W64 false (.gpr t1) (.gpr t2) (.Offset (.gpr b) off)))
    (hb : b ≠ 31#5 := by decide)
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hr1 : m.canRead a 8 = true) (hr2 : m.canRead (a + 8#64) 8 = true)
    (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd (upd r t1.toNat (m.read64 a)) t2.toNat (m.read64 (a + 8#64)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_ldp]
  simp only [execLdp, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hr1, hr2, Bool.and_self,
    MemWidth.bytes, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ h1,
    wr_gpr _ _ _ _ _ _ _ h2, mkS_advancePC]

/-- `ldp xt1, xt2, [xb], #16` (post-index; `b ∉ {t1, t2}`). -/
theorem t_ldpPost {t1 t2 b : BitVec 5} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldp .W64 false (.gpr t1) (.gpr t2) (.PostIndex (.gpr b) off)))
    (hr1 : m.canRead (r b.toNat) 8 = true) (hr2 : m.canRead (r b.toNat + 8#64) 8 = true)
    (hb : Ok b := by decide) (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd (upd (upd r b.toNat (r b.toNat + off)) t1.toNat (m.read64 (r b.toNat))) t2.toNat (m.read64 (r b.toNat + 8#64)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_ldp]
  simp only [execLdp, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, rd_gpr _ _ _ _ _ _ _ hb, hr1, hr2,
    Bool.and_self, MemWidth.bytes, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ hb,
    wr_gpr _ _ _ _ _ _ _ h1, wr_gpr _ _ _ _ _ _ _ h2, mkS_advancePC]

/-- `ldrb wt, [xb, #off]`. -/
theorem t_ldrb {t b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldr .W32 .B8 false (.gpr t) (.Offset (.gpr b) off)))
    (hb : b ≠ 31#5 := by decide)
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hr : m.canRead a 1 = true) (ht : Ok t := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r t.toNat (BitVec.ofNat 64 (m.read8 a).toNat))) := by
  refine step_mkS hrun hf ?_
  rw [ex_ldr]
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hr,
    MemWidth.bytes, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ ht, mkS_advancePC]
  refine mkS_upd_congr ?_
  simp [BitVec.toNat_setWidth]

/-- `stp xt1, xt2, [xb, #off]`. -/
theorem t_stp64 {t1 t2 b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.Offset (.gpr b) off)))
    (hb : b ≠ 31#5 := by decide)
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hw1 : m.canWrite a 8 = true) (hw2 : m.canWrite (a + 8#64) 8 = true)
    (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp ((m.write64 a (r t1.toNat)).write64 (a + 8#64) (r t2.toNat)) ps r) := by
  refine step_mkS hrun hf ?_
  rw [ex_stp]
  simp only [execStp, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hw1, hw2, Bool.and_self,
    MemWidth.bytes, Memory.writeSized, rd_gpr _ _ _ _ _ _ _ h1, rd_gpr _ _ _ _ _ _ _ h2,
    mkS_setMem, mkS_advancePC]

/-- `str xt, [xb, #off]`. -/
theorem t_str64 {t b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.str .X64 (.gpr t) (.Offset (.gpr b) off)))
    (hb : b ≠ 31#5 := by decide)
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hw : m.canWrite a 8 = true) (ht : Ok t := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp (m.write64 a (r t.toNat)) ps r) := by
  refine step_mkS hrun hf ?_
  rw [ex_str]
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hw,
    MemWidth.bytes, Memory.writeSized, rd_gpr _ _ _ _ _ _ _ ht, mkS_setMem, mkS_advancePC]

/-! ## Instructions only the GCC build uses -/

/-- `cset xd, eq` (`csinc xd, xzr, xzr, ne`). -/
theorem t_cset {d : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.condSelect .W64 .CSINC (.gpr d) .xzr .xzr .NE))
    (hd : Ok d := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 (if ps.z then 1 else 0)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_condSelect]
  simp only [execCondSelect, State.readReg, rd_xzr, mkS_pstate, ConditionHolds]
  by_cases hz : ps.z = true <;> simp [hz, wr_gpr _ _ _ _ _ _ _ hd, State.writeReg]


/-- `adds xd, xn, xm`. -/
theorem t_adds {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubShift .W64 .ADDS (.gpr d) (.gpr n) (.gpr k) .LSL 0))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m
      (AddWithCarry64 (r n.toNat) (r k.toNat) false).2
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_addSubShift]
  simp only [execAddSubShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, shiftVal, shift64, Nat.zero_mod, BitVec.shiftLeft_zero]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_setPState, mkS_advancePC]
  refine mkS_upd_congr ?_
  simp [AddWithCarry64, BitVec.toNat_add, BitVec.toNat_setWidth]
  omega

/-- `cmp wn, #0`. -/
theorem t_cmpW0 {n : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubImm .W32 .SUBS .xzr (.gpr n) 0x000#12 false))
    (hn : Ok n := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m
      (AddWithCarry32 ((r n.toNat).setWidth 32)
        (~~~((0x000#12).setWidth 64 : BitVec 64).setWidth 32) true).2 r) := by
  refine step_mkS hrun hf ?_
  rw [ex_addSubImm]
  simp only [execAddSubImm, State.readReg, State.readReg32, rd_gpr _ _ _ _ _ _ _ hn, evalAddSub,
    State.writeReg, wr_xzr, mkS_setPState, mkS_advancePC]
  simp [BitVec.toNat_setWidth]

/-- `cmp xn, xm`. -/
theorem t_cmpReg {n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubShift .W64 .SUBS .xzr (.gpr n) (.gpr k) .LSL 0))
    (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m
      (AddWithCarry64 (r n.toNat) (~~~(r k.toNat)) true).2 r) := by
  refine step_mkS hrun hf ?_
  rw [ex_addSubShift]
  simp only [execAddSubShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, shiftVal, shift64, Nat.zero_mod, BitVec.shiftLeft_zero]
  simp

theorem t_bCond_t {c : CondCode} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bCond c off)) (hc : ConditionHolds c ps = true) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + off) sp m ps r) :=
  step_mkS hrun hf (by rw [ex_bCond]; simp [hc])

theorem t_bCond_f {c : CondCode} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bCond c off)) (hc : ConditionHolds c ps = false) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps r) :=
  step_mkS hrun hf (by rw [ex_bCond]; simp [hc])

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Two runs of `poly1305_blocks` in lock step

The relational lemma `blocks_rel` is stated in continuation-passing form so that callers
(`poly1305_update`, `poly1305_finish`) use it at their `bl poly1305_blocks`: the two runs enter with
equal `x0`, `x1`, `x2`, `lr`, `sp`, equal `final` byte, and anything in `x3..x17`; they return to
`lr` with `sp` unchanged, all registers outside `x1..x17` as at entry, and memory changed only in
the accumulator bytes (`MemOk`). The loop reveals the message addresses `x1 + 16 k` and the state
addresses `x0 + 0, 8, …, 40, 88`; it branches only on `x1 = x2`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtBlocks

open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw

theorem pc4 (b : BitVec 64) (x y : Nat) (h : x + 4 = y := by decide) :
    b + BitVec.ofNat 64 x + 4#64 = b + BitVec.ofNat 64 y := by
  rw [pc_add, h]

theorem rd_x0 (s0 : State) (pc sp : BitVec 64) (m : Memory) (ps : PState) (r : Nat → BitVec 64) :
    (mkS s0 pc sp m ps r).readReg64 (.gpr 0#5) = X0 s0 := rfl

/-- What the precondition gives about a run's entry state (no values). -/
structure CtFacts (pl : Placement) (X : String → Option (State → State)) (s0 : State) : Prop where
  good : Good pl X s0 s0.mem
  rs : ∀ k < 24, ¬ W s0 (X0 s0 + BitVec.ofNat 64 k) ∧
    (s0.mem.perm (X0 s0 + BitVec.ofNat 64 k)).r = true ∧
    s0.mem.isLazyFree (X0 s0 + BitVec.ofNat 64 k) = false
  fn : ¬ W s0 (X0 s0 + BitVec.ofNat 64 88) ∧ (s0.mem.perm (X0 s0 + BitVec.ofNat 64 88)).r = true ∧
    s0.mem.isLazyFree (X0 s0 + BitVec.ofNat 64 88) = false

theorem rs_canRead' {pl : Placement} {X : String → Option (State → State)} {s0 : State} {m : Memory}
    (F : CtFacts pl X s0) (hm : MemOk s0 m) (off : Nat) (h : off + 8 ≤ 24) :
    m.canRead (X0 s0 + BitVec.ofNat 64 off) 8 = true :=
  canRead_notW hm fun k hk => by rw [pc_add]; exact F.rs (off + k) (by omega)

theorem fin_canRead' {pl : Placement} {X : String → Option (State → State)} {s0 : State} {m : Memory}
    (F : CtFacts pl X s0) (hm : MemOk s0 m) :
    m.canRead (X0 s0 + BitVec.ofNat 64 88) 1 = true :=
  canRead_notW hm fun k hk => by
    have : k = 0 := by omega
    subst this; simpa using F.fn

theorem cmpReg_z (a b : BitVec 64) : (AddWithCarry64 a (~~~b) true).2.z = decide (a = b) := by
  simp only [AddWithCarry64]
  rw [Bool.eq_iff_iff]; simp; bv_omega

section rel

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

/-- One instruction in both runs, as `Step` facts of the abstract states `mkS`. -/
theorem rb (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State} (hst : c₁.status = c₂.status)
    {pc sp₁ sp₂ : BitVec 64} (hsp : sp₁ = sp₂) {m₁ m₂ : Memory} {ps₁ ps₂ : PState}
    {r₁ r₂ : Nat → BitVec 64} {i : Instr} {t₁ t₂ : State}
    (hf1 : (prog pl X).fetchMem m₁ pc = some i) (hf2 : (prog pl X).fetchMem m₂ pc = some i)
    (st1 : Step (prog pl X) (mkS c₁ pc sp₁ m₁ ps₁ r₁) t₁)
    (st2 : Step (prog pl X) (mkS c₂ pc sp₂ m₂ ps₂ r₂) t₂)
    (hl : leakedValues i (mkS c₁ pc sp₁ m₁ ps₁ r₁) = leakedValues i (mkS c₂ pc sp₂ m₂ ps₂ r₂))
    (h : ObsEquiv (prog pl X) arity stop₁ stop₂ t₁ t₂) :
    ObsEquiv (prog pl X) arity stop₁ stop₂ (mkS c₁ pc sp₁ m₁ ps₁ r₁) (mkS c₂ pc sp₂ m₂ ps₂ r₂) := by
  refine oe_step hc rfl hsp hst st1 st2 ?_ h
  rw [stepObs_exec (s := mkS c₁ pc sp₁ m₁ ps₁ r₁) hf1,
    stepObs_exec (s := mkS c₂ pc sp₂ m₂ ps₂ r₂) hf2, hl]
  rfl

/-- An instruction of the block loop's body in both runs: only `x1` and `x2` are tracked. -/
theorem rbody (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State} (hst : c₁.status = c₂.status)
    {pc sp₁ sp₂ : BitVec 64} (hsp : sp₁ = sp₂) {m₁ m₂ : Memory} {ps₁ ps₂ ps₁' ps₂' : PState}
    {r₁ r₂ r₁' r₂' : Nat → BitVec 64} {i : Instr} {P Q : BitVec 64}
    (hf1 : (prog pl X).fetchMem m₁ pc = some i) (hf2 : (prog pl X).fetchMem m₂ pc = some i)
    (st1 : Step (prog pl X) (mkS c₁ pc sp₁ m₁ ps₁ r₁) (mkS c₁ (pc + 4#64) sp₁ m₁ ps₁' r₁'))
    (st2 : Step (prog pl X) (mkS c₂ pc sp₂ m₂ ps₂ r₂) (mkS c₂ (pc + 4#64) sp₂ m₂ ps₂' r₂'))
    (hl : leakedValues i (mkS c₁ pc sp₁ m₁ ps₁ r₁) = leakedValues i (mkS c₂ pc sp₂ m₂ ps₂ r₂))
    (e1 : r₁' 1 = P) (e2 : r₂' 1 = P) (e3 : r₁' 2 = Q) (e4 : r₂' 2 = Q)
    (h : ∀ (ρ₁ ρ₂ : PState) (q₁ q₂ : Nat → BitVec 64), q₁ 1 = P → q₂ 1 = P → q₁ 2 = Q → q₂ 2 = Q →
      ObsEquiv (prog pl X) arity stop₁ stop₂ (mkS c₁ (pc + 4#64) sp₁ m₁ ρ₁ q₁)
        (mkS c₂ (pc + 4#64) sp₂ m₂ ρ₂ q₂)) :
    ObsEquiv (prog pl X) arity stop₁ stop₂ (mkS c₁ pc sp₁ m₁ ps₁ r₁) (mkS c₂ pc sp₂ m₂ ps₂ r₂) :=
  rb hc hst hsp hf1 hf2 st1 st2 hl (h _ _ _ _ e1 e2 e3 e4)

end rel

section body

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

set_option maxHeartbeats 4000000 in
/-- One iteration of the block loop's body (offsets 0x2c..0xf8), in both runs. -/
theorem body2 (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State} (hst : c₁.status = c₂.status)
    (hrun₁ : c₁.status = .Running) (hrun₂ : c₂.status = .Running)
    {m₁ m₂ : Memory} (hg₁ : Good pl X c₁ m₁) (hg₂ : Good pl X c₂ m₂)
    {sp₁ sp₂ : BitVec 64} (hsp : sp₁ = sp₂) {ps₁ ps₂ : PState} {r₁ r₂ : Nat → BitVec 64}
    {P Q : BitVec 64} (e1₁ : r₁ 1 = P) (e1₂ : r₂ 1 = P) (e2₁ : r₁ 2 = Q) (e2₂ : r₂ 2 = Q)
    (hr1₁ : m₁.canRead P 8 = true) (hr2₁ : m₁.canRead (P + 8#64) 8 = true)
    (hr1₂ : m₂.canRead P 8 = true) (hr2₂ : m₂.canRead (P + 8#64) 8 = true)
    (k : ∀ (ρ₁ ρ₂ : PState) (q₁ q₂ : Nat → BitVec 64), q₁ 1 = P + 16#64 → q₂ 1 = P + 16#64 →
      q₁ 2 = Q → q₂ 2 = Q →
      ObsEquiv (prog pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 668#64) sp₁ m₁ ρ₁ q₁)
        (mkS c₂ (pl.base + 668#64) sp₂ m₂ ρ₂ q₂)) :
    ObsEquiv (prog pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 460#64) sp₁ m₁ ps₁ r₁)
      (mkS c₂ (pl.base + 460#64) sp₂ m₂ ps₂ r₂) := by
  have b1 : (0x01#5 : BitVec 5).toNat = 1 := rfl
  -- ldp x4, x5, [x1], #16
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_2c hg₁) (f_2c hg₂)
    (t_ldpPost hrun₁ (f_2c hg₁) (by rw [b1, e1₁]; exact hr1₁) (by rw [b1, e1₁]; exact hr2₁))
    (t_ldpPost hrun₂ (f_2c hg₂) (by rw [b1, e1₂]; exact hr1₂) (by rw [b1, e1₂]; exact hr2₂))
    (by simp [leakedValues, evalAddrMode, rd_gpr _ _ _ _ _ _ _ (show Ok 1#5 by decide), e1₁, e1₂])
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 460 464]
  -- andMask at 464
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_30 hg₁) (f_30 hg₂) (t_andMask 44 hrun₁ (f_30 hg₁)) (t_andMask 44 hrun₂ (f_30 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 464 468]
  -- extr at 468
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_34 hg₁) (f_34 hg₂) (t_extr hrun₁ (f_34 hg₁)) (t_extr hrun₂ (f_34 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 468 472]
  -- andMask at 472
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_38 hg₁) (f_38 hg₂) (t_andMask 44 hrun₁ (f_38 hg₁)) (t_andMask 44 hrun₂ (f_38 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 472 476]
  -- extr at 476
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_3c hg₁) (f_3c hg₂) (t_extr hrun₁ (f_3c hg₁)) (t_extr hrun₂ (f_3c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 476 480]
  -- addLsl at 480
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_40 hg₁) (f_40 hg₂) (t_addLsl hrun₁ (f_40 hg₁)) (t_addLsl hrun₂ (f_40 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 480 484]
  -- addLsl at 484
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_44 hg₁) (f_44 hg₂) (t_addLsl hrun₁ (f_44 hg₁)) (t_addLsl hrun₂ (f_44 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 484 488]
  -- addLsl at 488
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_48 hg₁) (f_48 hg₂) (t_addLsl hrun₁ (f_48 hg₁)) (t_addLsl hrun₂ (f_48 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 488 492]
  -- mul at 492
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_4c hg₁) (f_4c hg₂) (t_mul hrun₁ (f_4c hg₁)) (t_mul hrun₂ (f_4c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 492 496]
  -- mul at 496
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_50 hg₁) (f_50 hg₂) (t_mul hrun₁ (f_50 hg₁)) (t_mul hrun₂ (f_50 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 496 500]
  -- umulh at 500
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_54 hg₁) (f_54 hg₂) (t_umulh hrun₁ (f_54 hg₁)) (t_umulh hrun₂ (f_54 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 500 504]
  -- mul at 504
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_58 hg₁) (f_58 hg₂) (t_mul hrun₁ (f_58 hg₁)) (t_mul hrun₂ (f_58 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 504 508]
  -- adds at 508
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_5c hg₁) (f_5c hg₂) (t_adds hrun₁ (f_5c hg₁)) (t_adds hrun₂ (f_5c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 508 512]
  -- umulh at 512
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_60 hg₁) (f_60 hg₂) (t_umulh hrun₁ (f_60 hg₁)) (t_umulh hrun₂ (f_60 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 512 516]
  -- umulh at 516
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_64 hg₁) (f_64 hg₂) (t_umulh hrun₁ (f_64 hg₁)) (t_umulh hrun₂ (f_64 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 516 520]
  -- adc at 520
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_68 hg₁) (f_68 hg₂) (t_adc hrun₁ (f_68 hg₁)) (t_adc hrun₂ (f_68 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 520 524]
  -- adds at 524
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_6c hg₁) (f_6c hg₂) (t_adds hrun₁ (f_6c hg₁)) (t_adds hrun₂ (f_6c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 524 528]
  -- mul at 528
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_70 hg₁) (f_70 hg₂) (t_mul hrun₁ (f_70 hg₁)) (t_mul hrun₂ (f_70 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 528 532]
  -- adc at 532
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_74 hg₁) (f_74 hg₂) (t_adc hrun₁ (f_74 hg₁)) (t_adc hrun₂ (f_74 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 532 536]
  -- mul at 536
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_78 hg₁) (f_78 hg₂) (t_mul hrun₁ (f_78 hg₁)) (t_mul hrun₂ (f_78 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 536 540]
  -- umulh at 540
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_7c hg₁) (f_7c hg₂) (t_umulh hrun₁ (f_7c hg₁)) (t_umulh hrun₂ (f_7c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 540 544]
  -- extr at 544
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_80 hg₁) (f_80 hg₂) (t_extr hrun₁ (f_80 hg₁)) (t_extr hrun₂ (f_80 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 544 548]
  -- umulh at 548
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_84 hg₁) (f_84 hg₂) (t_umulh hrun₁ (f_84 hg₁)) (t_umulh hrun₂ (f_84 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 548 552]
  -- adds at 552
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_88 hg₁) (f_88 hg₂) (t_adds hrun₁ (f_88 hg₁)) (t_adds hrun₂ (f_88 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 552 556]
  -- mul at 556
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_8c hg₁) (f_8c hg₂) (t_mul hrun₁ (f_8c hg₁)) (t_mul hrun₂ (f_8c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 556 560]
  -- adc at 560
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_90 hg₁) (f_90 hg₂) (t_adc hrun₁ (f_90 hg₁)) (t_adc hrun₂ (f_90 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 560 564]
  -- mul at 564
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_94 hg₁) (f_94 hg₂) (t_mul hrun₁ (f_94 hg₁)) (t_mul hrun₂ (f_94 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 564 568]
  -- umulh at 568
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_98 hg₁) (f_98 hg₂) (t_umulh hrun₁ (f_98 hg₁)) (t_umulh hrun₂ (f_98 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 568 572]
  -- umulh at 572
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_9c hg₁) (f_9c hg₂) (t_umulh hrun₁ (f_9c hg₁)) (t_umulh hrun₂ (f_9c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 572 576]
  -- adds at 576
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_a0 hg₁) (f_a0 hg₂) (t_adds hrun₁ (f_a0 hg₁)) (t_adds hrun₂ (f_a0 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 576 580]
  -- andMask at 580
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_a4 hg₁) (f_a4 hg₂) (t_andMask 44 hrun₁ (f_a4 hg₁)) (t_andMask 44 hrun₂ (f_a4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 580 584]
  -- mul at 584
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_a8 hg₁) (f_a8 hg₂) (t_mul hrun₁ (f_a8 hg₁)) (t_mul hrun₂ (f_a8 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 584 588]
  -- adc at 588
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_ac hg₁) (f_ac hg₂) (t_adc hrun₁ (f_ac hg₁)) (t_adc hrun₂ (f_ac hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 588 592]
  -- umulh at 592
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_b0 hg₁) (f_b0 hg₂) (t_umulh hrun₁ (f_b0 hg₁)) (t_umulh hrun₂ (f_b0 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 592 596]
  -- adds at 596
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_b4 hg₁) (f_b4 hg₂) (t_adds hrun₁ (f_b4 hg₁)) (t_adds hrun₂ (f_b4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 596 600]
  -- cinc at 600
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_b8 hg₁) (f_b8 hg₂) (t_cinc hrun₁ (f_b8 hg₁)) (t_cinc hrun₂ (f_b8 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 600 604]
  -- adds at 604
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_bc hg₁) (f_bc hg₂) (t_adds hrun₁ (f_bc hg₁)) (t_adds hrun₂ (f_bc hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 604 608]
  -- adc at 608
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_c0 hg₁) (f_c0 hg₂) (t_adc hrun₁ (f_c0 hg₁)) (t_adc hrun₂ (f_c0 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 608 612]
  -- andMask at 612
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_c4 hg₁) (f_c4 hg₂) (t_andMask 44 hrun₁ (f_c4 hg₁)) (t_andMask 44 hrun₂ (f_c4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 612 616]
  -- extr at 616
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_c8 hg₁) (f_c8 hg₂) (t_extr hrun₁ (f_c8 hg₁)) (t_extr hrun₂ (f_c8 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 616 620]
  -- mul at 620
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_cc hg₁) (f_cc hg₂) (t_mul hrun₁ (f_cc hg₁)) (t_mul hrun₂ (f_cc hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 620 624]
  -- umulh at 624
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_d0 hg₁) (f_d0 hg₂) (t_umulh hrun₁ (f_d0 hg₁)) (t_umulh hrun₂ (f_d0 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 624 628]
  -- adds at 628
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_d4 hg₁) (f_d4 hg₂) (t_adds hrun₁ (f_d4 hg₁)) (t_adds hrun₂ (f_d4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 628 632]
  -- cinc at 632
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_d8 hg₁) (f_d8 hg₂) (t_cinc hrun₁ (f_d8 hg₁)) (t_cinc hrun₂ (f_d8 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 632 636]
  -- adds at 636
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_dc hg₁) (f_dc hg₂) (t_adds hrun₁ (f_dc hg₁)) (t_adds hrun₂ (f_dc hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 636 640]
  -- adc at 640
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_e0 hg₁) (f_e0 hg₂) (t_adc hrun₁ (f_e0 hg₁)) (t_adc hrun₂ (f_e0 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 640 644]
  -- andMask at 644
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_e4 hg₁) (f_e4 hg₂) (t_andMask 42 hrun₁ (f_e4 hg₁)) (t_andMask 42 hrun₂ (f_e4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 644 648]
  -- extr at 648
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_e8 hg₁) (f_e8 hg₂) (t_extr hrun₁ (f_e8 hg₁)) (t_extr hrun₂ (f_e8 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 648 652]
  -- addLsl at 652
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_ec hg₁) (f_ec hg₂) (t_addLsl hrun₁ (f_ec hg₁)) (t_addLsl hrun₂ (f_ec hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 652 656]
  -- addLsl at 656
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_f0 hg₁) (f_f0 hg₂) (t_addLsl hrun₁ (f_f0 hg₁)) (t_addLsl hrun₂ (f_f0 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 656 660]
  -- andMask at 660
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_f4 hg₁) (f_f4 hg₂) (t_andMask 44 hrun₁ (f_f4 hg₁)) (t_andMask 44 hrun₂ (f_f4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 660 664]
  -- addLsr at 664
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_f8 hg₁) (f_f8 hg₂) (t_addLsr hrun₁ (f_f8 hg₁)) (t_addLsr hrun₂ (f_f8 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 664 668]
  exact k _ _ _ _ e1₁ e1₂ e2₁ e2₂

end body

section loop

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

set_option maxHeartbeats 4000000 in
/-- The block loop from its head (0x2c) in both runs, then the epilogue and the return. -/
theorem loop2 (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State} (hst : c₁.status = c₂.status)
    (hrun₁ : c₁.status = .Running) (hrun₂ : c₂.status = .Running)
    (F₁ : CtFacts pl X c₁) (F₂ : CtFacts pl X c₂) (hsp : c₁.sp = c₂.sp) (hX0 : X0 c₁ = X0 c₂)
    (K : ∀ (m₁ m₂ : Memory) (ps₁ ps₂ : PState) (r₁ r₂ : Nat → BitVec 64), MemOk c₁ m₁ → MemOk c₂ m₂ →
      ObsEquiv (prog pl X) arity stop₁ stop₂
        (mkS c₁ (c₁.readReg64 (.gpr 0x1e#5)) c₁.sp m₁ ps₁ r₁)
        (mkS c₂ (c₂.readReg64 (.gpr 0x1e#5)) c₂.sp m₂ ps₂ r₂)) :
    ∀ d (n : Nat) (X1 : BitVec 64) (r₁ r₂ : Nat → BitVec 64) (ps₁ ps₂ : PState),
      n ≤ d → 16 ≤ n → n % 16 = 0 → n < 2 ^ 64 → MsgOk c₁ X1 n → MsgOk c₂ X1 n →
      r₁ 1 = X1 → r₂ 1 = X1 → r₁ 2 = X1 + BitVec.ofNat 64 n → r₂ 2 = X1 + BitVec.ofNat 64 n →
      ObsEquiv (prog pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 460#64) c₁.sp c₁.mem ps₁ r₁)
        (mkS c₂ (pl.base + 460#64) c₂.sp c₂.mem ps₂ r₂) := by
  intro d
  induction d with
  | zero => intro n _ _ _ _ _ hl h16; omega
  | succ d ih =>
    intro n X1 r₁ r₂ ps₁ ps₂ hl h16 h16d h64 hmsg₁ hmsg₂ e1₁ e1₂ e2₁ e2₂
    have hg₁ := F₁.good
    have hg₂ := F₂.good
    have hcr₁ : ∀ o, o + 8 ≤ 16 → c₁.mem.canRead (X1 + BitVec.ofNat 64 o) 8 = true := fun o ho =>
      canRead_notW hg₁.2.2 fun k hk => by rw [pc_add]; exact hmsg₁ _ (by omega)
    have hcr₂ : ∀ o, o + 8 ≤ 16 → c₂.mem.canRead (X1 + BitVec.ofNat 64 o) 8 = true := fun o ho =>
      canRead_notW hg₂.2.2 fun k hk => by rw [pc_add]; exact hmsg₂ _ (by omega)
    refine body2 hc hst hrun₁ hrun₂ hg₁ hg₂ hsp e1₁ e1₂ e2₁ e2₂ (by simpa using hcr₁ 0 (by decide))
      (hcr₁ 8 (by decide)) (by simpa using hcr₂ 0 (by decide)) (hcr₂ 8 (by decide)) ?_
    intro ρ₁ ρ₂ q₁ q₂ f1₁ f1₂ f2₁ f2₂
    have b1 : (0x01#5 : BitVec 5).toNat = 1 := rfl
    have b2 : (0x02#5 : BitVec 5).toNat = 2 := rfl
    -- cmp x1, x2
    refine rb hc hst hsp (f_fc hg₁) (f_fc hg₂) (t_cmpReg hrun₁ (f_fc hg₁)) (t_cmpReg hrun₂ (f_fc hg₂))
      rfl ?_
    rw [pc4 pl.base 668 672]
    simp only [b1, b2, f1₁, f1₂, f2₁, f2₂]
    have hz := cmpReg_z (X1 + 16#64) (X1 + BitVec.ofNat 64 n)
    have hz' : (AddWithCarry64 (X1 + 16#64) (~~~(X1 + BitVec.ofNat 64 n)) true).2.z =
        decide (16 = n) := by
      rw [hz, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl]
      exact Bool.decide_congr (add_ofNat_inj X1 (by decide) h64)
    by_cases hmore : 16 ≤ n - 16
    · have hcnd : ConditionHolds .NE (AddWithCarry64 (X1 + 16#64) (~~~(X1 + BitVec.ofNat 64 n)) true).2
          = true := by simp only [ConditionHolds, hz']; simp; omega
      refine rb hc hst hsp (f_100 hg₁) (f_100 hg₂) (t_bCond_t hrun₁ (f_100 hg₁) hcnd)
        (t_bCond_t hrun₂ (f_100 hg₂) hcnd) rfl ?_
      rw [show pl.base + 672#64 + 0xffffffffffffff2c#64 = pl.base + 460#64 by
        rw [BitVec.add_assoc]; rfl]
      have hn' : X1 + BitVec.ofNat 64 n = (X1 + 16#64) + BitVec.ofNat 64 (n - 16) := by
        rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, pc_add]; congr 2; omega
      refine ih (n - 16) (X1 + 16#64) q₁ q₂ _ _ (by omega) hmore (by omega) (by omega) ?_ ?_ f1₁ f1₂
        (by rw [f2₁, hn']) (by rw [f2₂, hn'])
      · intro j hj
        rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, pc_add]
        exact hmsg₁ _ (by omega)
      · intro j hj
        rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, pc_add]
        exact hmsg₂ _ (by omega)
    · have hcnd : ConditionHolds .NE (AddWithCarry64 (X1 + 16#64) (~~~(X1 + BitVec.ofNat 64 n)) true).2
          = false := by simp only [ConditionHolds, hz']; simp; omega
      refine rb hc hst hsp (f_100 hg₁) (f_100 hg₂) (t_bCond_f hrun₁ (f_100 hg₁) hcnd)
        (t_bCond_f hrun₂ (f_100 hg₂) hcnd) rfl ?_
      rw [pc4 pl.base 672 676]
      -- stp x7, x3, [x0, #0x18]
      refine rb hc hst hsp (f_104 hg₁) (f_104 hg₂)
        (t_stp64 hrun₁ (f_104 hg₁) (a := X0 c₁ + BitVec.ofNat 64 24) (ha := by rw [rd_x0]) (hw1 := h_canWrite hg₁.2.2 24 (by decide) (by decide)) (hw2 := by rw [add8]; exact h_canWrite hg₁.2.2 32 (by decide) (by decide)))
        (t_stp64 hrun₂ (f_104 hg₂) (a := X0 c₂ + BitVec.ofNat 64 24) (ha := by rw [rd_x0]) (hw1 := h_canWrite hg₂.2.2 24 (by decide) (by decide)) (hw2 := by rw [add8]; exact h_canWrite hg₂.2.2 32 (by decide) (by decide)))
        (by simp [leakedValues, evalAddrMode, rd_x0, hX0]) ?_
      rw [pc4 pl.base 676 680]
      simp only [add8]
      have hg2₁ := good_h (good_h hg₁ 24 (by decide) (by decide) (q₁ (0x07#5).toNat)) (24 + 8)
        (by decide) (by decide) (q₁ (0x03#5).toNat)
      have hg2₂ := good_h (good_h hg₂ 24 (by decide) (by decide) (q₂ (0x07#5).toNat)) (24 + 8)
        (by decide) (by decide) (q₂ (0x03#5).toNat)
      -- str x15, [x0, #0x28]
      refine rb hc hst hsp (f_108 hg2₁) (f_108 hg2₂)
        (t_str64 hrun₁ (f_108 hg2₁) (a := X0 c₁ + BitVec.ofNat 64 40) (ha := by rw [rd_x0]) (hw := h_canWrite hg2₁.2.2 40 (by decide) (by decide)))
        (t_str64 hrun₂ (f_108 hg2₂) (a := X0 c₂ + BitVec.ofNat 64 40) (ha := by rw [rd_x0]) (hw := h_canWrite hg2₂.2.2 40 (by decide) (by decide)))
        (by simp [leakedValues, evalAddrMode, rd_x0, hX0]) ?_
      rw [pc4 pl.base 680 684]
      have hg3₁ := good_h hg2₁ 40 (by decide) (by decide) (q₁ (0x0f#5).toNat)
      have hg3₂ := good_h hg2₂ 40 (by decide) (by decide) (q₂ (0x0f#5).toNat)
      -- ret
      refine rb hc hst hsp (f_10c hg3₁) (f_10c hg3₂) (t_ret hrun₁ (f_10c hg3₁))
        (t_ret hrun₂ (f_10c hg3₂)) rfl ?_
      exact K _ _ _ _ _ _ hg3₁.2.2 hg3₂.2.2

end loop

section top

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

set_option maxHeartbeats 4000000 in
/-- `poly1305_blocks` in both runs, in continuation-passing form: entered at its address with equal
`x0`, `x1`, `x2`, `lr`, `sp` (`x3..x17` and the flags arbitrary), a nonzero multiple of 16 bytes
of message readable at `x1` outside the accumulator, both runs return to `lr` with `sp` unchanged,
registers outside `x1..x17` as at entry (`mkS`), and memory changed only in the accumulator
(`MemOk`). -/
theorem blocks_rel (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State}
    (hrun₁ : c₁.status = .Running) (hrun₂ : c₂.status = .Running)
    (hpc₁ : c₁.pc = pl.base + 416#64) (hpc₂ : c₂.pc = pl.base + 416#64)
    (F₁ : CtFacts pl X c₁) (F₂ : CtFacts pl X c₂) (hsp : c₁.sp = c₂.sp) (hX0 : X0 c₁ = X0 c₂)
    (hx1 : c₁.readReg64 (.gpr 1#5) = c₂.readReg64 (.gpr 1#5))
    (hx2 : c₁.readReg64 (.gpr 2#5) = c₂.readReg64 (.gpr 2#5))
    (h16 : 16 ≤ (c₁.readReg64 (.gpr 2#5)).toNat) (h16d : (c₁.readReg64 (.gpr 2#5)).toNat % 16 = 0)
    (hmsg₁ : MsgOk c₁ (c₁.readReg64 (.gpr 1#5)) (c₁.readReg64 (.gpr 2#5)).toNat)
    (hmsg₂ : MsgOk c₂ (c₁.readReg64 (.gpr 1#5)) (c₁.readReg64 (.gpr 2#5)).toNat)
    (K : ∀ (m₁ m₂ : Memory) (ps₁ ps₂ : PState) (r₁ r₂ : Nat → BitVec 64), MemOk c₁ m₁ → MemOk c₂ m₂ →
      ObsEquiv (prog pl X) arity stop₁ stop₂
        (mkS c₁ (c₁.readReg64 (.gpr 0x1e#5)) c₁.sp m₁ ps₁ r₁)
        (mkS c₂ (c₂.readReg64 (.gpr 0x1e#5)) c₂.sp m₂ ps₂ r₂)) :
    ObsEquiv (prog pl X) arity stop₁ stop₂ c₁ c₂ := by
  have hst : c₁.status = c₂.status := hrun₁.trans hrun₂.symm
  have hg₁ := F₁.good
  have hg₂ := F₂.good
  refine oe_congr (mkS_self c₁).symm (mkS_self c₂).symm ?_
  rw [hpc₁, hpc₂]
  set P := c₁.readReg64 (.gpr 1#5) with hP
  set Q := c₁.readReg64 (.gpr 2#5) with hQ
  have e1₁ : r0 c₁ 1 = P := r0_eq c₁ 1
  have e1₂ : r0 c₂ 1 = P := (r0_eq c₂ 1).trans hx1.symm
  have e2₁ : r0 c₁ 2 = Q := r0_eq c₁ 2
  have e2₂ : r0 c₂ 2 = Q := (r0_eq c₂ 2).trans hx2.symm
  generalize r0 c₁ = r₁ at e1₁ e2₁ ⊢
  generalize r0 c₂ = r₂ at e1₂ e2₂ ⊢
  generalize c₁.pstate = ps₁
  generalize c₂.pstate = ps₂
  -- ldp x12, x7, [x0, #0x10]
  refine rbody (P := P) (Q := Q) hc hst hsp (f_0 hg₁) (f_0 hg₂)
    (t_ldp64 hrun₁ (f_0 hg₁) (a := X0 c₁ + BitVec.ofNat 64 16) (ha := by rw [rd_x0])
      (hr1 := rs_canRead' F₁ hg₁.2.2 16 (by decide))
      (hr2 := by rw [add8]; exact h_canRead hg₁.2.2 24 (by decide) (by decide)))
    (t_ldp64 hrun₂ (f_0 hg₂) (a := X0 c₂ + BitVec.ofNat 64 16) (ha := by rw [rd_x0])
      (hr1 := rs_canRead' F₂ hg₂.2.2 16 (by decide))
      (hr2 := by rw [add8]; exact h_canRead hg₂.2.2 24 (by decide) (by decide)))
    (by simp [leakedValues, evalAddrMode, rd_x0, hX0])
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 416 420]
  -- add x2, x1, x2
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_4 hg₁) (f_4 hg₂)
    (t_addLsl hrun₁ (f_4 hg₁)) (t_addLsl hrun₂ (f_4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e1₁, e2₁]) (by simp [upd, e1₂, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 420 424]
  -- ldp x8, x9, [x0]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_8 hg₁) (f_8 hg₂)
    (t_ldp64 hrun₁ (f_8 hg₁) (a := X0 c₁ + BitVec.ofNat 64 0) (ha := by rw [rd_x0])
      (hr1 := rs_canRead' F₁ hg₁.2.2 0 (by decide))
      (hr2 := by rw [add8]; exact rs_canRead' F₁ hg₁.2.2 8 (by decide)))
    (t_ldp64 hrun₂ (f_8 hg₂) (a := X0 c₂ + BitVec.ofNat 64 0) (ha := by rw [rd_x0])
      (hr1 := rs_canRead' F₂ hg₂.2.2 0 (by decide))
      (hr2 := by rw [add8]; exact rs_canRead' F₂ hg₂.2.2 8 (by decide)))
    (by simp [leakedValues, evalAddrMode, rd_x0, hX0])
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 424 428]
  -- ldrb w3, [x0, #0x58]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_c hg₁) (f_c hg₂)
    (t_ldrb hrun₁ (f_c hg₁) (a := X0 c₁ + BitVec.ofNat 64 88) (ha := by rw [rd_x0])
      (hr := fin_canRead' F₁ hg₁.2.2))
    (t_ldrb hrun₂ (f_c hg₂) (a := X0 c₂ + BitVec.ofNat 64 88) (ha := by rw [rd_x0])
      (hr := fin_canRead' F₂ hg₂.2.2))
    (by simp [leakedValues, evalAddrMode, rd_x0, hX0])
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 428 432]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_10 hg₁) (f_10 hg₂)
    (t_cmpW0 hrun₁ (f_10 hg₁)) (t_cmpW0 hrun₂ (f_10 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 432 436]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_14 hg₁) (f_14 hg₂)
    (t_addLsl hrun₁ (f_14 hg₁)) (t_addLsl hrun₂ (f_14 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 436 440]
  -- ldp x3, x15, [x0, #0x20]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_18 hg₁) (f_18 hg₂)
    (t_ldp64 hrun₁ (f_18 hg₁) (a := X0 c₁ + BitVec.ofNat 64 32) (ha := by rw [rd_x0])
      (hr1 := h_canRead hg₁.2.2 32 (by decide) (by decide))
      (hr2 := by rw [add8]; exact h_canRead hg₁.2.2 40 (by decide) (by decide)))
    (t_ldp64 hrun₂ (f_18 hg₂) (a := X0 c₂ + BitVec.ofNat 64 32) (ha := by rw [rd_x0])
      (hr1 := h_canRead hg₂.2.2 32 (by decide) (by decide))
      (hr2 := by rw [add8]; exact h_canRead hg₂.2.2 40 (by decide) (by decide)))
    (by simp [leakedValues, evalAddrMode, rd_x0, hX0])
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 440 444]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_1c hg₁) (f_1c hg₂)
    (t_addLsl hrun₁ (f_1c hg₁)) (t_addLsl hrun₂ (f_1c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 444 448]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_20 hg₁) (f_20 hg₂)
    (t_cset hrun₁ (f_20 hg₁)) (t_cset hrun₂ (f_20 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 448 452]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_24 hg₁) (f_24 hg₂)
    (t_lsl2 hrun₁ (f_24 hg₁)) (t_lsl2 hrun₂ (f_24 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 452 456]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_28 hg₁) (f_28 hg₂)
    (t_lsl2 hrun₁ (f_28 hg₁)) (t_lsl2 hrun₂ (f_28 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 456 460]
  have h64 : Q.toNat < 2 ^ 64 := Q.isLt
  have eQ : BitVec.ofNat 64 (P.toNat + Q.toNat) = P + BitVec.ofNat 64 Q.toNat := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  rw [eQ] at e2₁ e2₂
  exact loop2 hc hst hrun₁ hrun₂ F₁ F₂ hsp hX0 K _ _ P _ _ _ _ le_rfl h16 h16d h64 hmsg₁ hmsg₂
    e1₁ e1₂ e2₁ e2₂

end top

end Poly1305DebianCtBlocks

end
end

section
section
/-! # `poly1305_blocks` is constant-time (`ctInternalOk`)

The precondition `blocksPre` gives each run its entry facts (`ctfacts_of_pre`, adapted from the
heap extraction of the functional proof); `blocks_rel` with the continuation "both runs have
returned" gives `ct_subroutine_ok`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At bytesIn)
open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw

/-- What `blocksPre` gives about an entry state. -/
theorem ctfacts_of_pre {pl : Placement} {X : String → Option (State → State)}
    (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl) {s0 : State} {R : SepProp}
    {ro : Bool} {rh : List (BitVec 8)} {fin : BitVec 8} {msg : List (BitVec 8)}
    (hCL : (prog pl X).CodeLoaded s0.mem)
    (hpre : s0.mem ⊨ blocksPre pl (ro, rh, fin, msg) s0 ∗ R) :
    CtFacts pl X s0 ∧ (s0.readReg64 (.gpr 2#5)).toNat = msg.length ∧ 16 ≤ msg.length ∧
      msg.length % 16 = 0 ∧ MsgOk s0 (s0.readReg64 (.gpr 1#5)) msg.length := by
  obtain ⟨H, hH, hm⟩ := hpre
  obtain ⟨h1, h2, hd12, rfl, hpre1, hR⟩ := hH
  obtain ⟨g1, gA, dg, rfl, ⟨rfl, hφ⟩, hrest⟩ := hpre1
  obtain ⟨q1, qB, d1, rfl, hq1, hqB⟩ := hrest
  obtain ⟨qF, q3, dF, rfl, hqF, hq3⟩ := hqB
  obtain ⟨hl48, hlen, h16, h16d⟩ := hφ
  have hx0 : s0.readReg64 Reg.x0 = X0 s0 := rfl
  rw [hx0] at hq1 hqF
  set X1 := s0.readReg64 Reg.x1 with hX1
  set hh := Heap.empty.union (q1.union (qF.union q3)) with hhh
  have c1 : ∀ j (hj : j < rh.length), q1.phys (X0 s0 + BitVec.ofNat 64 j) = some (.rw rh[j]) :=
    fun j hj => bytes_rw rh _ q1 hq1 j hj
  have cF : qF.phys (X0 s0 + BitVec.ofNat 64 88) = some (.rw fin) := by
    have := bytes_rw [fin] _ qF hqF 0 (by simp)
    simpa using this
  have cM : ∀ j (hj : j < msg.length), Own (q3.phys (X1 + BitVec.ofNat 64 j)) msg[j] := by
    intro j hj
    have := bytesIn_cell hq3 j hj
    cases ro
    · exact Or.inl this
    · exact Or.inr this
  have cS : ∀ j (hj : j < rh.length), hh.phys (X0 s0 + BitVec.ofNat 64 j) = some (.rw rh[j]) :=
    fun j hj => cell_union_right_rw dg (cell_union_left (c1 j hj))
  have cF' : hh.phys (X0 s0 + BitVec.ofNat 64 88) = some (.rw fin) :=
    cell_union_right_rw dg (cell_union_right_rw d1 (cell_union_left cF))
  have cM' : ∀ j (hj : j < msg.length), Own (hh.phys (X1 + BitVec.ofNat 64 j)) msg[j] := fun j hj =>
    own_right dg (own_right d1 (own_right dF (cM j hj)))
  have mt : ∀ a b, Own (hh.phys a) b → s0.mem.read8 a = b ∧ (s0.mem.perm a).r = true ∧
      s0.mem.isLazyFree a = false := fun a b hc => own_matches hm (own_left hc)
  have wdom : ∀ a, W s0 a → ∃ b, hh.phys a = some (.rw b) := by
    intro a w
    obtain ⟨e, ht⟩ := inRegion_eq w
    rw [e, show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, pc_add]
    exact ⟨_, cS _ (by omega)⟩
  have F : CtFacts pl X s0 := {
    good := ⟨hP, hCL, fun a _ => rfl, fun a w => by
      obtain ⟨b, hb⟩ := wdom a w
      have := hm.1 a _ (cell_union_left hb)
      exact ⟨this.2.1, this.2.2, rfl, this.2.1⟩⟩
    rs := fun k hk => ⟨not_inRegion_h (X0 s0) k (Or.inl hk),
      (mt _ _ (Or.inl (cS k (by omega)))).2.1, (mt _ _ (Or.inl (cS k (by omega)))).2.2⟩
    fn := ⟨not_inRegion_h (X0 s0) 88 (Or.inr ⟨by omega, by omega⟩),
      (mt _ _ (Or.inl cF')).2.1, (mt _ _ (Or.inl cF')).2.2⟩ }
  have hmsg : MsgOk s0 X1 msg.length := fun j hj => ⟨by
      intro w
      obtain ⟨e, ht⟩ := inRegion_eq w
      rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, pc_add] at e
      have h := c1 (24 + (X1 + BitVec.ofNat 64 j - (X0 s0 + BitVec.ofNat 64 24)).toNat) (by omega)
      rw [← e] at h
      exact disj_own d1 h (own_right dF (cM j hj)),
    (mt _ _ (cM' j hj)).2.1, (mt _ _ (cM' j hj)).2.2⟩
  exact ⟨F, hlen, h16, h16d, hmsg⟩

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Calling `poly1305_blocks` from a caller that keeps memory in separation logic

`blocks_rel_sep` is `blocks_rel` with the entry facts given as `c.mem ⊨ blocksPre … c ∗ F` (any
frame `F`) and the continuation given the same assertion again on the return memory, with new
accumulator bytes `rh'` (`post_of_memOk`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At bytesIn)
open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw

/-- After a run that changed memory only in the accumulator (`MemOk c m`), the precondition holds
again with the accumulator bytes read from `m`. -/
theorem post_of_memOk {pl : Placement} {c : State} {F : SepProp}
    {ro : Bool} {rh : List (BitVec 8)} {fin : BitVec 8} {msg : List (BitVec 8)}
    (hpre : c.mem ⊨ blocksPre pl (ro, rh, fin, msg) c ∗ F) {m : Memory} (hok : MemOk c m) :
    ∃ rh' : List (BitVec 8), m ⊨ blocksPre pl (ro, rh', fin, msg) c ∗ F := by
  obtain ⟨H, hH, hm⟩ := hpre
  obtain ⟨h1, h2, hd12, rfl, hpre1, hR⟩ := hH
  obtain ⟨g1, gA, dg, rfl, ⟨rfl, hφ⟩, hrest⟩ := hpre1
  obtain ⟨q1, qB, d1, rfl, hq1, hqB⟩ := hrest
  obtain ⟨qF, q3, dF, rfl, hqF, hq3⟩ := hqB
  obtain ⟨hl48, hlen, h16, h16d⟩ := hφ
  have hx0 : c.readReg64 Reg.x0 = X0 c := rfl
  rw [hx0] at hq1 hqF
  set X1 := c.readReg64 Reg.x1 with hX1
  set hh := Heap.empty.union (q1.union (qF.union q3)) with hhh
  have c1 : ∀ j (hj : j < rh.length), q1.phys (X0 c + BitVec.ofNat 64 j) = some (.rw rh[j]) :=
    fun j hj => bytes_rw rh _ q1 hq1 j hj
  have cF : qF.phys (X0 c + BitVec.ofNat 64 88) = some (.rw fin) := by
    have := bytes_rw [fin] _ qF hqF 0 (by simp)
    simpa using this
  have cM : ∀ j (hj : j < msg.length), Own (q3.phys (X1 + BitVec.ofNat 64 j)) msg[j] := by
    intro j hj
    have := bytesIn_cell hq3 j hj
    cases ro
    · exact Or.inl this
    · exact Or.inr this
  have cS : ∀ j (hj : j < rh.length), hh.phys (X0 c + BitVec.ofNat 64 j) = some (.rw rh[j]) :=
    fun j hj => cell_union_right_rw dg (cell_union_left (c1 j hj))
  have cF' : hh.phys (X0 c + BitVec.ofNat 64 88) = some (.rw fin) :=
    cell_union_right_rw dg (cell_union_right_rw d1 (cell_union_left cF))
  have cM' : ∀ j (hj : j < msg.length), Own (hh.phys (X1 + BitVec.ofNat 64 j)) msg[j] := fun j hj =>
    own_right dg (own_right d1 (own_right dF (cM j hj)))
  have mt : ∀ a b, Own (hh.phys a) b → c.mem.read8 a = b ∧ (c.mem.perm a).r = true ∧
      c.mem.isLazyFree a = false := fun a b hc => own_matches hm (own_left hc)
  have wdom : ∀ a, W c a → ∃ b, hh.phys a = some (.rw b) := by
    intro a w
    obtain ⟨e, ht⟩ := inRegion_eq w
    rw [e, show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, pc_add]
    exact ⟨_, cS _ (by omega)⟩
  have fnW : ¬ W c (X0 c + BitVec.ofNat 64 88) :=
    not_inRegion_h (X0 c) 88 (Or.inr ⟨by omega, by omega⟩)
  have hmsgW : ∀ j < msg.length, ¬ W c (X1 + BitVec.ofNat 64 j) := fun j hj => by
    intro w
    obtain ⟨e, ht⟩ := inRegion_eq w
    rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, pc_add] at e
    have h := c1 (24 + (X1 + BitVec.ofNat 64 j - (X0 c + BitVec.ofNat 64 24)).toNat) (by omega)
    rw [← e] at h
    exact disj_own d1 h (own_right dF (cM j hj))
  have h2eq := modHeap_frame hd12 hm hok wdom
  have D := modHeap_disjoint hd12 m
  have D0 := modHeap_disjoint dg m
  have D1 := modHeap_disjoint d1 m
  have DF := modHeap_disjoint dF m
  rw [h2eq, modHeap_union, modHeap_empty] at D
  simp only [modHeap_union, modHeap_empty] at D0
  rw [modHeap_union] at D1
  refine ⟨(List.range rh.length).map fun j => m.read8 (X0 c + BitVec.ofNat 64 j),
    modHeap (hh.union h2) m, ?_,
    modHeap_matches hm hok fun a w => by
      obtain ⟨b, hb⟩ := wdom a w; exact ⟨b, cell_union_left hb⟩⟩
  rw [modHeap_union, h2eq, hhh, modHeap_union, modHeap_empty]
  simp only [modHeap_union] at D ⊢
  refine ⟨_, h2, D, rfl, ?_, hR⟩
  refine ⟨Heap.empty, _, D0, rfl, ⟨rfl, by simp [hl48], hlen, h16, h16d⟩, ?_⟩
  refine ⟨modHeap q1 m, _, D1, rfl, modHeap_bytes rh _ q1 m hq1, modHeap qF m, _, DF, rfl, ?_, ?_⟩
  · exact bytesIn_mod (ro := false) m (a := X0 c + 88#64) (bs := [fin]) hqF (fun k hk => by
      have : k = 0 := by simp at hk; omega
      subst this
      simpa [read8_of_notW hok fnW] using (mt _ _ (Or.inl cF')).1)
  · exact bytesIn_mod m hq3 (fun k hk => by
      rw [read8_of_notW hok (hmsgW k hk)]; exact (mt _ _ (cM' k hk)).1)

end Poly1305DebianCtBlocks

end
end

section
section
/-! # The final block of `poly1305_finish` (offsets 0x50..0x68), two runs

`final := 1`, then `poly1305_blocks(st, st->buffer, 16)` through the relational lemma of
`poly1305_blocks` (`Poly1305DebianCtBlocks.blocks_rel`), then the reduction and the tail call. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFinish

open Arm64 Arm64.Obj Leakage Poly1305DebianCt Poly1305DebianCtFw
open Poly1305Libsodium (bytesIn)

/-! ## Memory facts -/

section mem
variable {A M SP : BitVec 64} {sk : List (BitVec 8)} {F : SepProp} {m : Memory}

theorem memI_write_c (h : MemI A M SP sk F m) (j : Nat) (hj : j < 16) (v : BitVec 8) :
    m.canWrite (A + 72#64 + BitVec.ofNat 64 j) 1 = true ∧
    MemI A M SP sk F (m.write8 (A + 72#64 + BitVec.ofNat 64 j) v) := by
  obtain ⟨a, b, c, d, e, mac, la, lb, lc, le, lm, hm⟩ := h
  have hC : m ⊨ ((A + 72#64) ↦ₛ c) ∗ ((A ↦ₛ a) ∗ ((A + 48#64) ↦ₛ b) ∗ ((A + 88#64) ↦ₛ [d]) ∗
      ((A + 89#64) ↦ₛ e) ∗ (M ↦ₛ mac) ∗ ((SP - 32#64) ↦ₛ sk) ∗ memRegion (SP - 4128#64) 4096 ∗ F) :=
    Satisfies.of_eq hm (by ac_rfl)
  refine ⟨canWrite_of (fun i hi => by
    have : i = 0 := by omega
    subst this; rw [BitVec.add_zero]; exact (sat_bytes_read hC j (by omega)).2.1), ?_⟩
  have w := sat_bytes_write hC j (by omega) v
  exact ⟨a, b, c.set j v, d, e, mac, la, lb, by simp [lc], le, lm, Satisfies.of_eq w (by ac_rfl)⟩

theorem memI_write_d (h : MemI A M SP sk F m) (v : BitVec 8) :
    m.canWrite (A + 0x58#64) 1 = true ∧ MemI A M SP sk F (m.write8 (A + 0x58#64) v) := by
  obtain ⟨a, b, c, d, e, mac, la, lb, lc, le, lm, hm⟩ := h
  have hD : m ⊨ ((A + 88#64) ↦ₛ [d]) ∗ ((A ↦ₛ a) ∗ ((A + 48#64) ↦ₛ b) ∗ ((A + 72#64) ↦ₛ c) ∗
      ((A + 89#64) ↦ₛ e) ∗ (M ↦ₛ mac) ∗ ((SP - 32#64) ↦ₛ sk) ∗ memRegion (SP - 4128#64) 4096 ∗ F) :=
    Satisfies.of_eq hm (by ac_rfl)
  have r := (sat_bytes_read hD 0 (by simp)).2.1
  have w := sat_bytes_write hD 0 (by simp) v
  rw [BitVec.add_zero] at r w
  refine ⟨canWrite_of (fun i hi => by
    have : i = 0 := by omega
    subst this; rw [BitVec.add_zero]; exact r), ?_⟩
  exact ⟨a, b, c, v, e, mac, la, lb, lc, le, lm, Satisfies.of_eq w (by ac_rfl)⟩

/-- The precondition of `poly1305_blocks(A, A + 72, 16)`, and the invariant again afterwards. -/
theorem blocks_pre_of {pl : Placement} {s : State} (h0 : s.readReg64 Reg.x0 = A)
    (h1 : s.readReg64 Reg.x1 = A + 72#64) (h2 : (s.readReg64 Reg.x2).toNat = 16)
    (h : MemI A M SP sk F s.mem) :
    ∃ (a c : List (BitVec 8)) (d : BitVec 8) (R : SepProp),
      (s.mem ⊨ blocksPre pl (false, a, d, c) s ∗ R) ∧
      ∀ (m : Memory) (a' : List (BitVec 8)), (m ⊨ blocksPre pl (false, a', d, c) s ∗ R) →
        MemI A M SP sk F m := by
  obtain ⟨a, b, c, d, e, mac, la, lb, lc, le, lm, hm⟩ := h
  refine ⟨a, c, d, ((A + 48#64) ↦ₛ b) ∗ ((A + 89#64) ↦ₛ e) ∗ (M ↦ₛ mac) ∗ ((SP - 32#64) ↦ₛ sk) ∗
    memRegion (SP - 4128#64) 4096 ∗ F, ?_, ?_⟩
  · simp only [blocksPre, bytesIn, Bool.false_eq_true, if_false]
    rw [h0, h1, h2, sepConj_assoc, sat_pure_sep]
    exact ⟨⟨la, lc.symm, by omega, by omega⟩, Satisfies.of_eq hm (by ac_rfl)⟩
  · intro m a' hm'
    simp only [blocksPre, bytesIn, Bool.false_eq_true, if_false] at hm'
    rw [h0, h1, sepConj_assoc, sat_pure_sep] at hm'
    obtain ⟨⟨la', -⟩, hm'⟩ := hm'
    exact ⟨a', b, c, d, e, mac, la', lb, lc, le, lm, Satisfies.of_eq hm' (by ac_rfl)⟩

end mem

theorem kp_mkRegs {c₀ : State} {A M : BitVec 64} {q : BitVec 5 → BitVec 64} (h : Kp c₀ A M q)
    (r : Nat → BitVec 64) : Kp c₀ A M (Poly1305DebianCtBlocks.mkRegs ⟨q⟩ r).regs := by
  obtain ⟨h19, h20, hcs⟩ := h
  refine ⟨by simp [Poly1305DebianCtBlocks.mkRegs, h19], by simp [Poly1305DebianCtBlocks.mkRegs, h20],
    fun k h1 h2 => ?_⟩
  simp only [Poly1305DebianCtBlocks.mkRegs]
  rw [if_neg (by omega)]
  exact hcs k h1 h2

section
variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

/-- A byte store `strb wt, [xn, #off]` in both runs, to the same address `a`. -/
theorem rstrb (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State}
    (hr1 : c₁.status = .Running) (hr2 : c₂.status = .Running)
    {pc sp pcn : BitVec 64} {r₁ r₂ : BitVec 5 → BitVec 64}
    {ps₁ ps₂ : PState} {m₁ m₂ : Memory} {v₁ v₂ : BitVec 5 → BitVec 128}
    {t n : BitVec 5} {off a : BitVec 64} (ht : t ≠ 31#5) (hn : n ≠ 31#5)
    (hf1 : (P pl X).fetchMem m₁ pc = some (.str .B8 (.gpr t) (.Offset (.gpr n) off)))
    (hf2 : (P pl X).fetchMem m₂ pc = some (.str .B8 (.gpr t) (.Offset (.gpr n) off)))
    (ha₁ : r₁ n + off = a) (ha₂ : r₂ n + off = a)
    (hw₁ : m₁.canWrite a 1 = true) (hw₂ : m₂.canWrite a 1 = true)
    (H₁ : (P pl X).CodeLoaded m₁) (H₂ : (P pl X).CodeLoaded m₂) (hpc : pc + 4#64 = pcn)
    (h : (P pl X).CodeLoaded (m₁.write8 a ((r₁ t).truncate 8)) →
      (P pl X).CodeLoaded (m₂.write8 a ((r₂ t).truncate 8)) →
      ObsEquiv (P pl X) arity stop₁ stop₂
        (mkS c₁ pcn r₁ sp ps₁ (m₁.write8 a ((r₁ t).truncate 8)) v₁)
        (mkS c₂ pcn r₂ sp ps₂ (m₂.write8 a ((r₂ t).truncate 8)) v₂)) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pc r₁ sp ps₁ m₁ v₁) (mkS c₂ pc r₂ sp ps₂ m₂ v₂) := by
  subst hpc
  have e₁ := ex_strb_off (svc := evalSvc (P pl X).svc) (s0 := c₁) (pc := pc) (sp := sp) (ps := ps₁)
    (v := v₁) (r := r₁) (m := m₁) t n ht hn off (by rw [ha₁]; exact hw₁)
  have e₂ := ex_strb_off (svc := evalSvc (P pl X).svc) (s0 := c₂) (pc := pc) (sp := sp) (ps := ps₂)
    (v := v₂) (r := r₂) (m := m₂) t n ht hn off (by rw [ha₂]; exact hw₂)
  rw [ha₁] at e₁
  rw [ha₂] at e₂
  exact rs hc hr1 hr2 hf1 hf2 e₁ e₂ (by simp [leakedValues, evalAddrMode, hn, ha₁, ha₂])
    (h (cl_exec hr1 hf1 e₁ H₁) (cl_exec hr2 hf2 e₂ H₂))

/-- `poly1305_blocks(A, A + 72, 16)` in both runs, with the invariant `MemI` as frame. -/
theorem blocks_call (hc : StopCompat stop₁ stop₂) (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {cb₁ cb₂ : State} (hrun₁ : cb₁.status = .Running) (hrun₂ : cb₂.status = .Running)
    (hpc₁ : cb₁.pc = pl.base + 416#64) (hpc₂ : cb₂.pc = pl.base + 416#64)
    (hcl₁ : (P pl X).CodeLoaded cb₁.mem) (hcl₂ : (P pl X).CodeLoaded cb₂.mem)
    (hsp : cb₁.sp = cb₂.sp) {A M SP : BitVec 64}
    (h0₁ : cb₁.readReg64 Reg.x0 = A) (h0₂ : cb₂.readReg64 Reg.x0 = A)
    (h1₁ : cb₁.readReg64 Reg.x1 = A + 72#64) (h1₂ : cb₂.readReg64 Reg.x1 = A + 72#64)
    (h2₁ : (cb₁.readReg64 Reg.x2).toNat = 16) (h2₂ : (cb₂.readReg64 Reg.x2).toNat = 16)
    {sk₁ sk₂ : List (BitVec 8)} {F₁ F₂ : SepProp}
    (M₁ : MemI A M SP sk₁ F₁ cb₁.mem) (M₂ : MemI A M SP sk₂ F₂ cb₂.mem)
    (K : ∀ (m₁ m₂ : Memory) (ps₁ ps₂ : PState) (r₁ r₂ : Nat → BitVec 64),
      MemI A M SP sk₁ F₁ m₁ → MemI A M SP sk₂ F₂ m₂ →
      (P pl X).CodeLoaded m₁ → (P pl X).CodeLoaded m₂ →
      ObsEquiv (P pl X) arity stop₁ stop₂
        (Poly1305DebianCtBlocks.mkS cb₁ (cb₁.readReg64 (.gpr 0x1e#5)) cb₁.sp m₁ ps₁ r₁)
        (Poly1305DebianCtBlocks.mkS cb₂ (cb₂.readReg64 (.gpr 0x1e#5)) cb₂.sp m₂ ps₂ r₂)) :
    ObsEquiv (P pl X) arity stop₁ stop₂ cb₁ cb₂ := by
  obtain ⟨a₁, c₁, d₁, R₁, hpre₁, back₁⟩ := blocks_pre_of (pl := pl) h0₁ h1₁ h2₁ M₁
  obtain ⟨a₂, c₂, d₂, R₂, hpre₂, back₂⟩ := blocks_pre_of (pl := pl) h0₂ h1₂ h2₂ M₂
  obtain ⟨F₁', hlen₁, h16, h16d, hmsg₁⟩ := Poly1305DebianCtBlocks.ctfacts_of_pre (X := X) hP hcl₁ hpre₁
  obtain ⟨F₂', hlen₂, -, -, hmsg₂⟩ := Poly1305DebianCtBlocks.ctfacts_of_pre (X := X) hP hcl₂ hpre₂
  have hx1 : cb₁.readReg64 (.gpr 1#5) = cb₂.readReg64 (.gpr 1#5) := h1₁.trans h1₂.symm
  have hx2 : cb₁.readReg64 (.gpr 2#5) = cb₂.readReg64 (.gpr 2#5) :=
    BitVec.eq_of_toNat_eq (h2₁.trans h2₂.symm)
  have hl₂ : c₂.length = c₁.length := by rw [← hlen₁, ← hlen₂, hx2]
  rw [hl₂, ← hx1] at hmsg₂
  rw [← hlen₁] at h16 h16d hmsg₁ hmsg₂
  refine Poly1305DebianCtBlocks.blocks_rel hc hrun₁ hrun₂ hpc₁ hpc₂ F₁' F₂' hsp
    (h0₁.trans h0₂.symm) hx1 hx2 h16 h16d hmsg₁ hmsg₂ ?_
  intro m₁ m₂ ps₁ ps₂ r₁ r₂ ok₁ ok₂
  obtain ⟨rh₁', q₁⟩ := Poly1305DebianCtBlocks.post_of_memOk hpre₁ ok₁
  obtain ⟨rh₂', q₂⟩ := Poly1305DebianCtBlocks.post_of_memOk hpre₂ ok₂
  exact K m₁ m₂ ps₁ ps₂ r₁ r₂ (back₁ _ _ q₁) (back₂ _ _ q₂)
    (Poly1305DebianCtBlocks.Good.codeLoaded ⟨hP, hcl₁, ok₁⟩)
    (Poly1305DebianCtBlocks.Good.codeLoaded ⟨hP, hcl₂, ok₂⟩)

/-- The common hypotheses of both runs from +0x50 on. -/
structure Common (pl : Placement) (X : String → Option (State → State)) (c₀₁ c₀₂ : State)
    (A M SP : BitVec 64) : Prop where
  hP : libsodiumDebianOnetimeauthCtLib.Placeable pl
  hz : ∃ fz, (P pl X).externAt? (pl.ρ "sodium_memzero") = some fz ∧ HookOk fz Libc.explicitBzeroSpec
  hna : ∀ n, hookName? (P pl X) (pl.ρ "sodium_memzero") = some n → arity n ≤ 2
  hal : SP &&& 0b1111#64 = 0#64
  hSP₁ : c₀₁.sp = SP
  hSP₂ : c₀₂.sp = SP
  hA₁ : c₀₁.readReg64 Reg.x0 = A
  hA₂ : c₀₂.readReg64 Reg.x0 = A
  hM₁ : c₀₁.readReg64 Reg.x1 = M
  hM₂ : c₀₂.readReg64 Reg.x1 = M

/-- One run's facts at a point after the prologue. -/
structure RunI (pl : Placement) (X : String → Option (State → State)) (c₀ : State)
    (A M SP : BitVec 64) (F : SepProp) (c : State) (q : BitVec 5 → BitVec 64) (m : Memory)
    (v : BitVec 5 → BitVec 128) : Prop where
  run : c.status = .Running
  kp : Kp c₀ A M q
  cl : (P pl X).CodeLoaded m
  mem : MemI A M SP (stk c₀) F m
  vr : VRegFile.calleeSaved ⟨v⟩ = calleeSavedVRegs c₀

/-- From +0x68 to the return. -/
theorem at1160 (hc : StopCompat stop₁ stop₂) {c₀₁ c₀₂ : State} {A M SP : BitVec 64}
    (C : Common pl X c₀₁ c₀₂ A M SP) {F₁ F₂ : SepProp} {c₁ c₂ : State}
    {q₁ q₂ : BitVec 5 → BitVec 64} {ρ₁ ρ₂ : PState} {m₁ m₂ : Memory} {v₁ v₂ : BitVec 5 → BitVec 128}
    (I₁ : RunI pl X c₀₁ A M SP F₁ c₁ q₁ m₁ v₁) (I₂ : RunI pl X c₀₂ A M SP F₂ c₂ q₂ m₂ v₂)
    (K : ∀ f₁ f₂ : State, FinishPost pl X c₀₁ F₁ f₁ → FinishPost pl X c₀₂ F₂ f₂ →
      ObsEquiv (P pl X) arity stop₁ stop₂ f₁ f₂) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 1160#64) q₁ (SP - 32#64) ρ₁ m₁ v₁)
      (mkS c₂ (pl.base + 1160#64) q₂ (SP - 32#64) ρ₂ m₂ v₂) := by
  obtain ⟨fz, hzat, hzok⟩ := C.hz
  exact red_rel hc C.hP I₁.run I₂.run I₁.kp I₂.kp I₁.cl I₂.cl I₁.mem I₂.mem
    fun q₁ q₂ ρ₁ ρ₂ m₁ m₂ k₁ k₂ H₁ H₂ M₁ M₂ =>
      tail_rel hc C.hP hzok hzat C.hna I₁.run I₂.run C.hal C.hSP₁ C.hSP₂ C.hA₁ C.hA₂ C.hM₁ C.hM₂
        k₁ k₂ I₁.vr I₂.vr H₁ H₂ M₁ M₂ K

set_option maxHeartbeats 2000000 in
/-- From +0x50 (`final := 1`, the last block) to the return. -/
theorem at1136 (hc : StopCompat stop₁ stop₂) {c₀₁ c₀₂ : State} {A M SP : BitVec 64}
    (C : Common pl X c₀₁ c₀₂ A M SP) {F₁ F₂ : SepProp} {c₁ c₂ : State}
    {q₁ q₂ : BitVec 5 → BitVec 64} {ρ₁ ρ₂ : PState} {m₁ m₂ : Memory} {v₁ v₂ : BitVec 5 → BitVec 128}
    (I₁ : RunI pl X c₀₁ A M SP F₁ c₁ q₁ m₁ v₁) (I₂ : RunI pl X c₀₂ A M SP F₂ c₂ q₂ m₂ v₂)
    (K : ∀ f₁ f₂ : State, FinishPost pl X c₀₁ F₁ f₁ → FinishPost pl X c₀₂ F₂ f₂ →
      ObsEquiv (P pl X) arity stop₁ stop₂ f₁ f₂) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 1136#64) q₁ (SP - 32#64) ρ₁ m₁ v₁)
      (mkS c₂ (pl.base + 1136#64) q₂ (SP - 32#64) ρ₂ m₂ v₂) := by
  have hP := C.hP
  obtain ⟨hr1, k₁, H₁, M₁, hv₁⟩ := I₁
  obtain ⟨hr2, k₂, H₂, M₂, hv₂⟩ := I₂
  -- +0x50: mov w0, #1
  refine rk hc hr1 hr2 (f_50 hP H₁) (f_50 hP H₂) (ex_movz32 0#5 (by decide) _)
    (ex_movz32 0#5 (by decide) _) (lv0 fun _ => rfl) (Kp_upd k₁ _) (Kp_upd k₂ _) (a4 _ 1136 1140) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂; intro q₁ q₂ ρ₁ ρ₂ k₁ k₂
  -- +0x54: strb w0, [x19, #0x58]
  obtain ⟨W₁, M₁'⟩ := memI_write_d M₁ ((q₁ 0#5).truncate 8)
  obtain ⟨W₂, M₂'⟩ := memI_write_d M₂ ((q₂ 0#5).truncate 8)
  refine rstrb hc hr1 hr2 (by decide) (by decide) (f_54 hP H₁) (f_54 hP H₂) (by rw [k₁.1])
    (by rw [k₂.1]) W₁ W₂ H₁ H₂ (a4 _ 1140 1144) ?_
  intro H₁' H₂'
  clear W₁ W₂ M₁ M₂ H₁ H₂
  generalize (m₁.write8 (A + 0x58#64) ((q₁ 0#5).truncate 8)) = m₁ at M₁' H₁' ⊢
  generalize (m₂.write8 (A + 0x58#64) ((q₂ 0#5).truncate 8)) = m₂ at M₂' H₂' ⊢
  -- +0x58: add x1, x19, #0x48
  refine rn hc hr1 hr2 (f_58 hP H₁') (f_58 hP H₂') (ex_add_imm 1#5 19#5 (by decide) (by decide) _)
    (ex_add_imm 1#5 19#5 (by decide) (by decide) _) (lv0 fun _ => rfl) (a4 _ 1144 1148) ?_
  -- +0x5c: mov x0, x19
  refine rn hc hr1 hr2 (f_5c hP H₁') (f_5c hP H₂') (ex_mov 0#5 19#5 (by decide) (by decide))
    (ex_mov 0#5 19#5 (by decide) (by decide)) (lv0 fun _ => rfl) (a4 _ 1148 1152) ?_
  -- +0x60: mov x2, #16
  refine rn hc hr1 hr2 (f_60 hP H₁') (f_60 hP H₂') (ex_movz64 2#5 (by decide) _)
    (ex_movz64 2#5 (by decide) _) (lv0 fun _ => rfl) (a4 _ 1152 1156) ?_
  -- +0x64: bl poly1305_blocks
  refine rs hc hr1 hr2 (f_64 hP H₁') (f_64 hP H₂') (ex_bl _) (ex_bl _) (lv0 fun _ => rfl) ?_
  rw [show pl.base + 1156#64 + 0xfffffffffffffd1c#64 = pl.base + 416#64 by bv_omega]
  refine blocks_call hc hP hr1 hr2 rfl rfl H₁' H₂' rfl (A := A)
    (by simp [Reg.x0, k₁.1]) (by simp [Reg.x0, k₂.1])
    (by simp [Reg.x1, k₁.1]) (by simp [Reg.x1, k₂.1])
    (by simp [Reg.x2]) (by simp [Reg.x2]) M₁' M₂' ?_
  intro m₁ m₂ ps₁ ps₂ r₁ r₂ N₁ N₂ G₁ G₂
  have conv : ∀ (cb : State) (m : Memory) (ps : PState) (r : Nat → BitVec 64),
      Poly1305DebianCtBlocks.mkS cb (cb.readReg64 (.gpr 0x1e#5)) cb.sp m ps r =
        mkS cb (cb.readReg64 (.gpr 0x1e#5)) (Poly1305DebianCtBlocks.mkRegs cb.regs r).regs cb.sp
          ps m cb.vregs.regs := fun _ _ _ _ => rfl
  rw [conv, conv]
  simp only [mkS_readGpr, mkS_sp, mkS_regs', mkS_vregs', BitVec.reduceEq, ite_false, upd_apply,
    ite_true]
  rw [a4 _ 1156 1160]
  exact at1160 hc C ⟨hr1, kp_mkRegs (Kp_upd (Kp_upd (Kp_upd (Kp_upd k₁ _) _) _) _) _, G₁, N₁, hv₁⟩
    ⟨hr2, kp_mkRegs (Kp_upd (Kp_upd (Kp_upd (Kp_upd k₂ _) _) _) _) _, G₂, N₂, hv₂⟩ K

end

end Poly1305DebianCtFinish

end
end

section
section
/-! # Padding the last partial block (offsets 0x20..0x4c), two runs

`buffer[leftover] = 1`, then, unless `leftover = 15`, `memset(buffer + leftover + 1, 0,
15 - leftover)`. The branch and the `memset` arguments depend only on the public `leftover`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFinish

open Arm64 Arm64.Obj Leakage Poly1305DebianCt Poly1305DebianCtFw

theorem sh0 (x : BitVec 64) : shift64 x .LSL 0 = x := by simp [shift64]

theorem kp_kept {c₀ f : State} {A M : BitVec 64} {r : BitVec 5 → BitVec 64} (hk : KeptRegs f r)
    (h : Kp c₀ A M r) : Kp c₀ A M f.regs.regs := by
  obtain ⟨h19, h20, hcs⟩ := h
  refine ⟨by rw [hk 19#5 (by decide) (by decide), h19], by rw [hk 20#5 (by decide) (by decide), h20],
    fun k h1 h2 => ?_⟩
  rw [hk k (by omega) (by omega), hcs k h1 h2]

/-- The `memset` region `[A + 72 + j, A + 88)` and the hook's stack, and the invariant afterwards. -/
theorem memI_memset {A M SP : BitVec 64} {sk : List (BitVec 8)} {F : SepProp} {m : Memory}
    (h : MemI A M SP sk F m) (j : Nat) (hj : j ≤ 16) :
    ∃ R : SepProp,
      (m ⊨ memRegion (A + 72#64 + BitVec.ofNat 64 j) (16 - j) ∗ memRegion (SP - 4128#64) 4096 ∗ R) ∧
      ∀ m' : Memory, (m' ⊨ ((A + 72#64 + BitVec.ofNat 64 j) ↦ₛ List.replicate (16 - j) 0#8) ∗
        memRegion (SP - 4128#64) 4096 ∗ R) → MemI A M SP sk F m' := by
  obtain ⟨a, b, c, d, e, mac, la, lb, lc, le, lm, hm⟩ := h
  have ec : ∀ c' : List (BitVec 8), c'.length = 16 → ((A + 72#64) ↦ₛ c') =
      ((A + 72#64) ↦ₛ c'.take j) ∗ ((A + 72#64 + BitVec.ofNat 64 j) ↦ₛ c'.drop j) := by
    intro c' hc'
    conv_lhs => rw [← List.take_append_drop j c']
    rw [pointsToBytes_append, List.length_take, Nat.min_eq_left (by omega)]
  have hdl : (c.drop j).length = 16 - j := by simp [lc]
  refine ⟨(A ↦ₛ a) ∗ ((A + 48#64) ↦ₛ b) ∗ ((A + 72#64) ↦ₛ c.take j) ∗ ((A + 88#64) ↦ₛ [d]) ∗
    ((A + 89#64) ↦ₛ e) ∗ (M ↦ₛ mac) ∗ ((SP - 32#64) ↦ₛ sk) ∗ F, ?_, ?_⟩
  · rw [ec c lc] at hm
    have h1 : m ⊨ ((A + 72#64 + BitVec.ofNat 64 j) ↦ₛ c.drop j) ∗ (memRegion (SP - 4128#64) 4096 ∗
        ((A ↦ₛ a) ∗ ((A + 48#64) ↦ₛ b) ∗ ((A + 72#64) ↦ₛ c.take j) ∗ ((A + 88#64) ↦ₛ [d]) ∗
        ((A + 89#64) ↦ₛ e) ∗ (M ↦ₛ mac) ∗ ((SP - 32#64) ↦ₛ sk) ∗ F)) :=
      Satisfies.of_eq hm (by ac_rfl)
    have h2 := sat_sep_mono h1 (bytes_entails_memRegion _ _)
    rw [hdl] at h2
    exact h2
  · intro m' hm'
    have hl' : (c.take j ++ List.replicate (16 - j) 0#8).length = 16 := by simp [lc]; omega
    refine ⟨a, b, c.take j ++ List.replicate (16 - j) 0#8, d, e, mac, la, lb, hl', le, lm, ?_⟩
    rw [ec _ hl', List.take_left' (by simp [lc]; omega), List.drop_left' (by simp [lc]; omega)]
    exact Satisfies.of_eq hm' (by ac_rfl)

section
variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

/-- One step to the next instruction, then forget the registers up to the invariants `I₁`, `I₂`,
and the flags. -/
theorem rq (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State}
    (hr1 : c₁.status = .Running) (hr2 : c₂.status = .Running)
    {pc sp pcn : BitVec 64} {r₁ r₂ r₁' r₂' : BitVec 5 → BitVec 64}
    {ps₁ ps₂ ps₁' ps₂' : PState} {m₁ m₂ : Memory} {v₁ v₂ : BitVec 5 → BitVec 128}
    {i : Instr} (I₁ I₂ : (BitVec 5 → BitVec 64) → Prop)
    (hf1 : (P pl X).fetchMem m₁ pc = some i) (hf2 : (P pl X).fetchMem m₂ pc = some i)
    (e1 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) =
      mkS c₁ (pc + 4#64) r₁' sp ps₁' m₁ v₁)
    (e2 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₂ pc r₂ sp ps₂ m₂ v₂) =
      mkS c₂ (pc + 4#64) r₂' sp ps₂' m₂ v₂)
    (hl : leakedValues i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) = leakedValues i (mkS c₂ pc r₂ sp ps₂ m₂ v₂))
    (k₁ : I₁ r₁') (k₂ : I₂ r₂') (hpc : pc + 4#64 = pcn)
    (h : ∀ (q₁ q₂ : BitVec 5 → BitVec 64) (ρ₁ ρ₂ : PState), I₁ q₁ → I₂ q₂ →
      ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pcn q₁ sp ρ₁ m₁ v₁) (mkS c₂ pcn q₂ sp ρ₂ m₂ v₂)) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pc r₁ sp ps₁ m₁ v₁) (mkS c₂ pc r₂ sp ps₂ m₂ v₂) := by
  subst hpc
  exact rs hc hr1 hr2 hf1 hf2 e1 e2 hl (h _ _ _ _ k₁ k₂)

/-- A byte store to the same address in both runs, keeping memory invariants `Q₁`, `Q₂`. -/
theorem rstrbM (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State}
    (hr1 : c₁.status = .Running) (hr2 : c₂.status = .Running)
    {pc sp pcn : BitVec 64} {r₁ r₂ : BitVec 5 → BitVec 64}
    {ps₁ ps₂ : PState} {m₁ m₂ : Memory} {v₁ v₂ : BitVec 5 → BitVec 128}
    {t n : BitVec 5} {off a : BitVec 64} (Q₁ Q₂ : Memory → Prop) (ht : t ≠ 31#5) (hn : n ≠ 31#5)
    (hf1 : (P pl X).fetchMem m₁ pc = some (.str .B8 (.gpr t) (.Offset (.gpr n) off)))
    (hf2 : (P pl X).fetchMem m₂ pc = some (.str .B8 (.gpr t) (.Offset (.gpr n) off)))
    (ha₁ : r₁ n + off = a) (ha₂ : r₂ n + off = a)
    (hw₁ : m₁.canWrite a 1 = true) (hw₂ : m₂.canWrite a 1 = true)
    (hq₁ : ∀ x, Q₁ (m₁.write8 a x)) (hq₂ : ∀ x, Q₂ (m₂.write8 a x))
    (H₁ : (P pl X).CodeLoaded m₁) (H₂ : (P pl X).CodeLoaded m₂) (hpc : pc + 4#64 = pcn)
    (h : ∀ m₁' m₂' : Memory, Q₁ m₁' → Q₂ m₂' → (P pl X).CodeLoaded m₁' → (P pl X).CodeLoaded m₂' →
      ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pcn r₁ sp ps₁ m₁' v₁) (mkS c₂ pcn r₂ sp ps₂ m₂' v₂)) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pc r₁ sp ps₁ m₁ v₁) (mkS c₂ pc r₂ sp ps₂ m₂ v₂) :=
  rstrb hc hr1 hr2 ht hn hf1 hf2 ha₁ ha₂ hw₁ hw₂ H₁ H₂ hpc fun G₁ G₂ =>
    h _ _ (hq₁ _) (hq₂ _) G₁ G₂

/-- The `memset(A + 72 + j, 0, 16 - j)` hook in both runs, returning to +0x50. -/
theorem memset_rel (hc : StopCompat stop₁ stop₂) {c₀₁ c₀₂ : State} {A M SP : BitVec 64}
    (C : Common pl X c₀₁ c₀₂ A M SP) {fm : State → State}
    (hmok : HookOk fm VerifiedLibraries.Musl.cryptoMemsetSpec)
    (hmat : (P pl X).externAt? (pl.ρ "memset") = some fm)
    {F₁ F₂ : SepProp} {c₁ c₂ : State}
    {r₁ r₂ : BitVec 5 → BitVec 64} {ρ₁ ρ₂ : PState} {m₁ m₂ : Memory} {v₁ v₂ : BitVec 5 → BitVec 128}
    (I₁ : RunI pl X c₀₁ A M SP F₁ c₁ r₁ m₁ v₁) (I₂ : RunI pl X c₀₂ A M SP F₂ c₂ r₂ m₂ v₂)
    (j : Nat) (hj : j ≤ 16)
    (f0₁ : r₁ 0#5 = A + 72#64 + BitVec.ofNat 64 j) (f0₂ : r₂ 0#5 = A + 72#64 + BitVec.ofNat 64 j)
    (f1₁ : r₁ 1#5 = 0#64) (f1₂ : r₂ 1#5 = 0#64)
    (f2₁ : r₁ 2#5 = BitVec.ofNat 64 (16 - j)) (f2₂ : r₂ 2#5 = BitVec.ofNat 64 (16 - j))
    (f30₁ : r₁ 30#5 = pl.base + 1136#64) (f30₂ : r₂ 30#5 = pl.base + 1136#64)
    (K : ∀ f₁ f₂ : State, FinishPost pl X c₀₁ F₁ f₁ → FinishPost pl X c₀₂ F₂ f₂ →
      ObsEquiv (P pl X) arity stop₁ stop₂ f₁ f₂) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (pl.ρ "memset") r₁ (SP - 32#64) ρ₁ m₁ v₁)
      (mkS c₂ (pl.ρ "memset") r₂ (SP - 32#64) ρ₂ m₂ v₂) := by
  have hal32 : (SP - 32#64) &&& 0b1111#64 = 0#64 := al16_sub SP 32 (by decide) (by decide) C.hal
  obtain ⟨R₁, pre₁, back₁⟩ := memI_memset I₁.mem j hj
  obtain ⟨R₂, pre₂, back₂⟩ := memI_memset I₂.mem j hj
  have ha : ∀ (c : State) (r : BitVec 5 → BitVec 64) (ρ : PState) (m : Memory)
      (v : BitVec 5 → BitVec 128), (mkS c (pl.ρ "memset") r (SP - 32#64) ρ m v).spAligned = true :=
    fun c r ρ m v => by simp [hal32]
  have es : SP - 32#64 - BitVec.ofNat 64 4096 = SP - 4128#64 := by bv_omega
  have hn : (BitVec.ofNat 64 (16 - j)).toNat = 16 - j := by
    simp only [BitVec.toNat_ofNat]; omega
  have hpre : ∀ (c : State) (r : BitVec 5 → BitVec 64) (ρ : PState) (m : Memory)
      (v : BitVec 5 → BitVec 128) (R : SepProp), r 0#5 = A + 72#64 + BitVec.ofNat 64 j →
      r 1#5 = 0#64 → r 2#5 = BitVec.ofNat 64 (16 - j) →
      (m ⊨ memRegion (A + 72#64 + BitVec.ofNat 64 j) (16 - j) ∗ memRegion (SP - 4128#64) 4096 ∗ R) →
      (mkS c (pl.ρ "memset") r (SP - 32#64) ρ m v).mem ⊨
        VerifiedLibraries.Musl.cryptoMemsetSpec.pre (A + 72#64 + BitVec.ofNat 64 j, 0#8, 16 - j)
          (mkS c (pl.ρ "memset") r (SP - 32#64) ρ m v) ∗ R := by
    intro c r ρ m v R h0 h1 h2 hm
    simp only [VerifiedLibraries.Musl.cryptoMemsetSpec, VerifiedLibraries.Musl.cExtern,
      ProofLib.stackAt, VerifiedLibraries.Musl.externStack]
    rw [sepConj_assoc, sat_pure_sep, sepConj_assoc]
    refine ⟨⟨by simp [Reg.x0, h0], by simp [Reg.x1, State.readReg32, h1], by simp [Reg.x2, h2, hn]⟩,
      ?_⟩
    simp only [mkS_sp, mkS_mem]
    rw [es]
    exact hm
  have post : ∀ (c c₀ : State) (r : BitVec 5 → BitVec 64) (ρ : PState) (m : Memory)
      (v : BitVec 5 → BitVec 128) (R : SepProp) (F : SepProp),
      Kp c₀ A M r → r 30#5 = pl.base + 1136#64 →
      VRegFile.calleeSaved ⟨v⟩ = calleeSavedVRegs c₀ →
      (∀ m' : Memory, (m' ⊨ ((A + 72#64 + BitVec.ofNat 64 j) ↦ₛ List.replicate (16 - j) 0#8) ∗
        memRegion (SP - 4128#64) 4096 ∗ R) → MemI A M SP (stk c₀) F m') →
      SubroutineOutcome VerifiedLibraries.Musl.cryptoMemsetSpec
        (A + 72#64 + BitVec.ofNat 64 j, 0#8, 16 - j) R
        (mkS c (pl.ρ "memset") r (SP - 32#64) ρ m v) (fm (mkS c (pl.ρ "memset") r (SP - 32#64) ρ m v)) →
      (P pl X).CodeLoaded (fm (mkS c (pl.ρ "memset") r (SP - 32#64) ρ m v)).mem →
      ∃ f : State, f = fm (mkS c (pl.ρ "memset") r (SP - 32#64) ρ m v) ∧
        f.pc = pl.base + 1136#64 ∧ f.sp = SP - 32#64 ∧
        RunI pl X c₀ A M SP F f f.regs.regs f.mem f.vregs.regs := by
    intro c c₀ r ρ m v R F k h30 hv back o G
    rcases o with ⟨⟨hpc, hsp, hst⟩, ⟨-, hcs⟩, hpost⟩ | ⟨-, p⟩ | ⟨_, -, p⟩ | ⟨-, p⟩
    rotate_left
    · exact absurd p not_sat_false'
    · exact absurd p not_sat_false'
    · exact absurd p not_sat_false'
    refine ⟨_, rfl, by rw [hpc]; simp [Reg.lr, h30], hsp, hst, kp_kept (kept_of_cs hcs) k, G,
      back _ ?_, hcs.2.2.2.2.2.2.2.2.2.2.2.trans hv⟩
    simp only [VerifiedLibraries.Musl.cryptoMemsetSpec, VerifiedLibraries.Musl.cExtern,
      ProofLib.stackAt, VerifiedLibraries.Musl.externStack, mkS_sp] at hpost
    rw [sepConj_assoc, sepConj_assoc, sat_pure_sep, es] at hpost
    exact Satisfies.of_eq hpost.2 (by ac_rfl)
  refine oe_hk hc hmok rfl rfl I₁.run I₂.run (ha _ _ _ _ _) (ha _ _ _ _ _) hmat ?_
    (A + 72#64 + BitVec.ofNat 64 j, 0#8, 16 - j) (A + 72#64 + BitVec.ofNat 64 j, 0#8, 16 - j) R₁ R₂
    (hpre _ _ _ _ _ _ f0₁ f1₁ f2₁ pre₁) (hpre _ _ _ _ _ _ f0₂ f1₂ f2₂ pre₂) I₁.cl I₂.cl ?_
  · intro n _
    refine args_eq_of arity_le3 (fun i hi => ?_) n
    interval_cases i
    · simp [f0₁, f0₂]
    · simp [f1₁, f1₂]
    · simp [f2₁, f2₂]
  · intro o₁ o₂ G₁ G₂
    obtain ⟨g₁, rfl, P₁, S₁, J₁⟩ := post _ _ _ _ _ _ _ _ I₁.kp f30₁ I₁.vr back₁ o₁ G₁
    obtain ⟨g₂, rfl, P₂, S₂, J₂⟩ := post _ _ _ _ _ _ _ _ I₂.kp f30₂ I₂.vr back₂ o₂ G₂
    refine oe_congr (mkS_self _).symm (mkS_self _).symm ?_
    rw [P₁, S₁, P₂, S₂]
    exact at1136 hc C J₁ J₂ K

theorem hi15 (L : BitVec 64) (hL : L.toNat < 16) :
    ConditionHolds .HI (AddWithCarry64 (L + BitVec.zeroExtend 64 0x001#12)
      (~~~(BitVec.zeroExtend 64 0x00f#12)) true).2 = decide (L.toNat = 15) := by
  rw [hi_cmp]
  have : (L + BitVec.zeroExtend 64 0x001#12).toNat = L.toNat + 1 := by
    rw [BitVec.toNat_add]; simp; omega
  rw [this]
  simp only [BitVec.toNat_setWidth, BitVec.zeroExtend_eq_setWidth]
  simp only [decide_eq_decide]
  constructor <;> intro h <;> simp at * <;> omega

set_option maxHeartbeats 4000000 in
/-- From +0x20 (`leftover = L ≠ 0`) to the return. -/
theorem pad_rel (hc : StopCompat stop₁ stop₂) {c₀₁ c₀₂ : State} {A M SP : BitVec 64}
    (C : Common pl X c₀₁ c₀₂ A M SP) {fm : State → State}
    (hmok : HookOk fm VerifiedLibraries.Musl.cryptoMemsetSpec)
    (hmat : (P pl X).externAt? (pl.ρ "memset") = some fm)
    {F₁ F₂ : SepProp} {c₁ c₂ : State}
    {q₁ q₂ : BitVec 5 → BitVec 64} {ρ₁ ρ₂ : PState} {m₁ m₂ : Memory} {v₁ v₂ : BitVec 5 → BitVec 128}
    (I₁ : RunI pl X c₀₁ A M SP F₁ c₁ q₁ m₁ v₁) (I₂ : RunI pl X c₀₂ A M SP F₂ c₂ q₂ m₂ v₂)
    {L : BitVec 64} (hL1 : 1 ≤ L.toNat) (hL2 : L.toNat < 16)
    (e0₁ : q₁ 0#5 = A) (e0₂ : q₂ 0#5 = A) (e1₁ : q₁ 1#5 = L) (e1₂ : q₂ 1#5 = L)
    (K : ∀ f₁ f₂ : State, FinishPost pl X c₀₁ F₁ f₁ → FinishPost pl X c₀₂ F₂ f₂ →
      ObsEquiv (P pl X) arity stop₁ stop₂ f₁ f₂) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 1088#64) q₁ (SP - 32#64) ρ₁ m₁ v₁)
      (mkS c₂ (pl.base + 1088#64) q₂ (SP - 32#64) ρ₂ m₂ v₂) := by
  have hP := C.hP
  obtain ⟨hr1, k₁, H₁, M₁, hv₁⟩ := I₁
  obtain ⟨hr2, k₂, H₂, M₂, hv₂⟩ := I₂
  have eL : BitVec.ofNat 64 L.toNat = L := by simp
  -- +0x20: add x0, x0, x1
  refine rn hc hr1 hr2 (f_20 hP H₁) (f_20 hP H₂)
    (ex_add_shift 0#5 0#5 1#5 (by decide) (by decide) (by decide) .LSL 0)
    (ex_add_shift 0#5 0#5 1#5 (by decide) (by decide) (by decide) .LSL 0) (lv0 fun _ => rfl) (a4 _ 1088 1092) ?_
  -- +0x24: mov w2, #1
  refine rn hc hr1 hr2 (f_24 hP H₁) (f_24 hP H₂) (ex_movz32 2#5 (by decide) _)
    (ex_movz32 2#5 (by decide) _) (lv0 fun _ => rfl) (a4 _ 1092 1096) ?_
  -- +0x28: strb w2, [x0, #0x48]
  refine rstrbM hc hr1 hr2 (MemI A M SP (stk c₀₁) F₁) (MemI A M SP (stk c₀₂) F₂) (by decide)
    (by decide) (f_28 hP H₁) (f_28 hP H₂) (a := A + 72#64 + BitVec.ofNat 64 L.toNat)
    (by simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, e0₁, e1₁, sh0]; rw [eL]; bv_omega)
    (by simp only [upd_apply, BitVec.reduceEq, ite_true, ite_false, e0₂, e1₂, sh0]; rw [eL]; bv_omega)
    (memI_write_c M₁ L.toNat hL2 0).1 (memI_write_c M₂ L.toNat hL2 0).1
    (fun x => (memI_write_c M₁ L.toNat hL2 x).2) (fun x => (memI_write_c M₂ L.toNat hL2 x).2)
    H₁ H₂ (a4 _ 1096 1100) ?_
  clear M₁ M₂ H₁ H₂
  intro m₁ m₂ M₁ M₂ H₁ H₂
  -- +0x2c: add x0, x1, #1
  refine rq hc hr1 hr2 (fun q => Kp c₀₁ A M q ∧ q 0#5 = L + BitVec.zeroExtend 64 0x001#12 ∧ q 1#5 = L)
    (fun q => Kp c₀₂ A M q ∧ q 0#5 = L + BitVec.zeroExtend 64 0x001#12 ∧ q 1#5 = L)
    (f_2c hP H₁) (f_2c hP H₂) (ex_add_imm 0#5 1#5 (by decide) (by decide) _)
    (ex_add_imm 0#5 1#5 (by decide) (by decide) _) (lv0 fun _ => rfl)
    ⟨Kp_upd (Kp_upd (Kp_upd k₁ _) _) _, by simp [e1₁], by simp [e1₁]⟩
    ⟨Kp_upd (Kp_upd (Kp_upd k₂ _) _) _, by simp [e1₂], by simp [e1₂]⟩ (a4 _ 1100 1104) ?_
  clear k₁ k₂ q₁ q₂ ρ₁ ρ₂ e0₁ e0₂ e1₁ e1₂
  rintro q₁ q₂ ρ₁ ρ₂ ⟨k₁, x0₁, x1₁⟩ ⟨k₂, x0₂, x1₂⟩
  -- +0x30: cmp x0, #15
  have c₁e := ex_cmp_imm (svc := evalSvc (P pl X).svc) (s0 := c₁) (pc := pl.base + 1104#64) (r := q₁)
    (sp := SP - 32#64) (ps := ρ₁) (m := m₁) (v := v₁) 0#5 (by decide) 0x00f#12
  have c₂e := ex_cmp_imm (svc := evalSvc (P pl X).svc) (s0 := c₂) (pc := pl.base + 1104#64) (r := q₂)
    (sp := SP - 32#64) (ps := ρ₂) (m := m₂) (v := v₂) 0#5 (by decide) 0x00f#12
  rw [x0₁] at c₁e
  rw [x0₂] at c₂e
  refine rn hc hr1 hr2 (f_30 hP H₁) (f_30 hP H₂) c₁e c₂e (lv0 fun _ => rfl) (a4 _ 1104 1108) ?_
  -- +0x34: b.hi +0x1c
  refine rs hc hr1 hr2 (f_34 hP H₁) (f_34 hP H₂) (ex_bcond _ _) (ex_bcond _ _) (lv0 fun _ => rfl) ?_
  rw [hi15 L hL2]
  by_cases h15 : L.toNat = 15
  · simp only [h15, decide_true, if_true]
    rw [show pl.base + 1108#64 + 0x1c#64 = pl.base + 1136#64 by rw [BitVec.add_assoc]; rfl]
    exact at1136 hc C ⟨hr1, k₁, H₁, M₁, hv₁⟩ ⟨hr2, k₂, H₂, M₂, hv₂⟩ K
  simp only [h15, decide_false, Bool.false_eq_true, if_false]
  rw [a4 _ 1108 1112]
  -- +0x38: add x0, x1, #0x49
  refine rn hc hr1 hr2 (f_38 hP H₁) (f_38 hP H₂) (ex_add_imm 0#5 1#5 (by decide) (by decide) _)
    (ex_add_imm 0#5 1#5 (by decide) (by decide) _) (lv0 fun _ => rfl) (a4 _ 1112 1116) ?_
  -- +0x3c: mov x2, #15
  refine rn hc hr1 hr2 (f_3c hP H₁) (f_3c hP H₂) (ex_movz64 2#5 (by decide) _)
    (ex_movz64 2#5 (by decide) _) (lv0 fun _ => rfl) (a4 _ 1116 1120) ?_
  -- +0x40: add x0, x19, x0
  refine rn hc hr1 hr2 (f_40 hP H₁) (f_40 hP H₂)
    (ex_add_shift 0#5 19#5 0#5 (by decide) (by decide) (by decide) .LSL 0)
    (ex_add_shift 0#5 19#5 0#5 (by decide) (by decide) (by decide) .LSL 0) (lv0 fun _ => rfl) (a4 _ 1120 1124) ?_
  -- +0x44: sub x2, x2, x1
  refine rn hc hr1 hr2 (f_44 hP H₁) (f_44 hP H₂)
    (ex_sub_shift0 2#5 2#5 1#5 (by decide) (by decide) (by decide))
    (ex_sub_shift0 2#5 2#5 1#5 (by decide) (by decide) (by decide)) (lv0 fun _ => rfl) (a4 _ 1124 1128) ?_
  -- +0x48: mov w1, #0
  refine rn hc hr1 hr2 (f_48 hP H₁) (f_48 hP H₂) (ex_movz32 1#5 (by decide) _)
    (ex_movz32 1#5 (by decide) _) (lv0 fun _ => rfl) (a4 _ 1128 1132) ?_
  -- +0x4c: bl memset
  refine rs hc hr1 hr2 (f_4c hP H₁) (f_4c hP H₂) (ex_bl _) (ex_bl _) (lv0 fun _ => rfl) ?_
  rw [show pl.base + 1132#64 + (pl.ρ "memset" - (pl.base + 1132#64)) = pl.ρ "memset" by bv_omega]
  have h0 : A + (L + 73#64) = A + 72#64 + BitVec.ofNat 64 (L.toNat + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h2 : 15#64 - L = BitVec.ofNat 64 (15 - L.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    omega
  have h30 : pl.base + 1132#64 + 4#64 = pl.base + 1136#64 := a4 _ 1132 1136
  exact memset_rel hc C hmok hmat
    ⟨hr1, Kp_upd (Kp_upd (Kp_upd (Kp_upd (Kp_upd (Kp_upd k₁ _) _) _) _) _) _, H₁, M₁, hv₁⟩
    ⟨hr2, Kp_upd (Kp_upd (Kp_upd (Kp_upd (Kp_upd (Kp_upd k₂ _) _) _) _) _) _, H₂, M₂, hv₂⟩
    (L.toNat + 1) (by omega)
    (by simp [x1₁, k₁.1, sh0, h0]) (by simp [x1₂, k₂.1, sh0, h0])
    (by simp) (by simp)
    (by simp [x1₁, h2]) (by simp [x1₂, h2])
    (by simp [h30]) (by simp [h30]) K

end

end Poly1305DebianCtFinish

end
end

section
section
/-! # `poly1305_finish` in two runs: the relational lemma `finish_rel`

The prologue saves `x29, x30, x19, x20` in the 32-byte frame, loads the public `leftover` and
branches on it (`cbz`): to +0x68 when it is zero, to the padding (`pad_rel`) otherwise. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFinish

open Arm64 Arm64.Obj Leakage Poly1305DebianCt Poly1305DebianCtFw
open Poly1305Libsodium (u64At)

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

theorem split5 (st : List (BitVec 8)) (h : st.length = 96) :
    ∃ (a b c : List (BitVec 8)) (d : BitVec 8) (e : List (BitVec 8)),
      a.length = 48 ∧ b.length = 24 ∧ c.length = 16 ∧ e.length = 7 ∧
      a ++ b ++ c ++ [d] ++ e = st ∧ u64At st 64 = u64At b 16 := by
  refine ⟨st.take 48, (st.drop 48).take 24, (st.drop 72).take 16, st[88], st.drop 89,
    by simp [h], by simp [h], by simp [h], by simp [h], ?_, ?_⟩
  · simp only [List.append_assoc, List.singleton_append]
    rw [← List.drop_eq_getElem_cons (by omega),
      show st.drop 88 = (st.drop 72).drop 16 by simp [List.drop_drop], List.take_append_drop,
      show st.drop 72 = (st.drop 48).drop 24 by simp [List.drop_drop], List.take_append_drop,
      List.take_append_drop]
  · simp [u64At, List.drop_take, List.take_take, List.drop_drop]

/-- The entry memory, the frame stores of the prologue, and the load of `leftover`. -/
theorem pro_mem {pl : Placement} {c : State} {st mac : List (BitVec 8)} {F : SepProp}
    (hpre : c.mem ⊨ finishPre pl (st, mac) c ∗ F) (x29 x30 x19 x20 : BitVec 64) :
    c.mem.canWrite (c.sp - 32#64) 8 = true ∧ c.mem.canWrite (c.sp - 32#64 + 8#64) 8 = true ∧
    ((c.mem.write64 (c.sp - 32#64) x29).write64 (c.sp - 32#64 + 8#64) x30).canWrite
      (c.sp - 32#64 + 0x10#64) 8 = true ∧
    ((c.mem.write64 (c.sp - 32#64) x29).write64 (c.sp - 32#64 + 8#64) x30).canWrite
      (c.sp - 32#64 + 0x10#64 + 8#64) 8 = true ∧
    MemI (c.readReg64 Reg.x0) (c.readReg64 Reg.x1) c.sp
      (unpack64 x29 ++ unpack64 x30 ++ unpack64 x19 ++ unpack64 x20) F
      ((((c.mem.write64 (c.sp - 32#64) x29).write64 (c.sp - 32#64 + 8#64) x30).write64
        (c.sp - 32#64 + 0x10#64) x19).write64 (c.sp - 32#64 + 0x10#64 + 8#64) x20) ∧
    (((((c.mem.write64 (c.sp - 32#64) x29).write64 (c.sp - 32#64 + 8#64) x30).write64
        (c.sp - 32#64 + 0x10#64) x19).write64 (c.sp - 32#64 + 0x10#64 + 8#64) x20).read64
        (c.readReg64 Reg.x0 + 0x40#64)).toNat = u64At st 64 ∧
    ((((c.mem.write64 (c.sp - 32#64) x29).write64 (c.sp - 32#64 + 8#64) x30).write64
        (c.sp - 32#64 + 0x10#64) x19).write64 (c.sp - 32#64 + 0x10#64 + 8#64) x20).canRead
        (c.readReg64 Reg.x0 + 0x40#64) 8 = true ∧
    u64At st 64 < 16 := by
  simp only [finishPre, stackFrame] at hpre
  rw [sepConj_assoc, sat_pure_sep] at hpre
  obtain ⟨⟨hl96, hL16, hl16⟩, hpre⟩ := hpre
  generalize c.readReg64 Reg.x0 = A at hpre ⊢
  generalize c.readReg64 Reg.x1 = M at hpre ⊢
  generalize c.sp = SP at hpre ⊢
  generalize c.mem = m at hpre ⊢
  have hs1 : m ⊨ memRegion (SP - 4128#64) (4096 + 32) ∗ ((A ↦ₛ st) ∗ (M ↦ₛ mac) ∗ F) :=
    Satisfies.of_eq hpre (by ac_rfl)
  have hs2 := sat_sep_mono hs1 (memRegion_split (SP - 4128#64) 4096 32 (by decide))
  rw [show SP - 4128#64 + BitVec.ofNat 64 4096 = SP - 32#64 by bv_omega] at hs2
  have hs3 : m ⊨ memRegion (SP - 32#64) 32 ∗ (memRegion (SP - 4128#64) 4096 ∗
      (A ↦ₛ st) ∗ (M ↦ₛ mac) ∗ F) := Satisfies.of_eq hs2 (by ac_rfl)
  have hs4 := sat_sep_mono hs3 (memRegion_entails_bytes (SP - 32#64) 32 (by decide))
  rw [sepExists_sepConj, sat_sepExists] at hs4
  obtain ⟨bs, hs4⟩ := hs4
  rw [sepConj_assoc, sat_pure_sep] at hs4
  obtain ⟨hbs, hs4⟩ := hs4
  have w0 := sat_bytes_write64 hs4 0 (by omega) x29
  have w8 := (sat_bytes_write64 hs4 8 (by omega) x30).1
  rw [BitVec.add_zero] at w0
  have w08 := sat_bytes_write64 w0.2 8 (by simp; omega) x30
  have w16 := sat_bytes_write64 w08.2 16 (by simp; omega) x19
  have w24 := (sat_bytes_write64 w08.2 24 (by simp; omega) x20).1
  have w1624 := sat_bytes_write64 w16.2 24 (by simp; omega) x20
  have hstk := stk_writes bs hbs x29 x30 x19 x20
  simp only at hstk
  rw [hstk] at w1624
  have e24 : SP - 32#64 + 0x10#64 + 8#64 = SP - 32#64 + BitVec.ofNat 64 24 := by rw [pc_add]
  rw [e24]
  obtain ⟨a, b, cc, d, e, la, lb, lc, le, hst, hu⟩ := split5 st hl96
  rw [← hst, assemble A a b cc d e la lb lc] at w1624
  have hB : _ ⊨ ((A + 48#64) ↦ₛ b) ∗ ((A ↦ₛ a) ∗ ((A + 72#64) ↦ₛ cc) ∗ ((A + 88#64) ↦ₛ [d]) ∗
      ((A + 89#64) ↦ₛ e) ∗ (M ↦ₛ mac) ∗ ((SP - 32#64) ↦ₛ
        (unpack64 x29 ++ unpack64 x30 ++ unpack64 x19 ++ unpack64 x20)) ∗
      memRegion (SP - 4128#64) 4096 ∗ F) := Satisfies.of_eq w1624.2 (by ac_rfl)
  have rL := sat_bytes_read64 hB 16 (by omega)
  rw [show A + 48#64 + BitVec.ofNat 64 16 = A + 0x40#64 by bv_omega] at rL
  refine ⟨w0.1, w8, w16.1, w24,
    ⟨a, b, cc, d, e, mac, la, lb, lc, le, hl16, Satisfies.of_eq w1624.2 (by ac_rfl)⟩,
    by rw [rL.1, hu], rL.2, hL16⟩

/-- At entry: one byte of the state and the 4096 bytes below `sp - 32`, for `no_both`. -/
theorem nb_mem {pl : Placement} {c : State} {st mac : List (BitVec 8)} {F : SepProp}
    (hpre : c.mem ⊨ finishPre pl (st, mac) c ∗ F) :
    ∃ R : SepProp, c.mem ⊨ memRegion (c.readReg64 Reg.x0) 1 ∗ memRegion (c.sp - 4096#64) 4096 ∗ R := by
  simp only [finishPre, stackFrame] at hpre
  rw [sepConj_assoc, sat_pure_sep] at hpre
  obtain ⟨⟨hl96, -, -⟩, hpre⟩ := hpre
  generalize c.readReg64 Reg.x0 = A at hpre ⊢
  generalize c.readReg64 Reg.x1 = M at hpre ⊢
  generalize c.sp = SP at hpre ⊢
  generalize c.mem = m at hpre ⊢
  have h1 := sat_sep_mono (Satisfies.of_eq hpre (Q := (A ↦ₛ st) ∗ ((M ↦ₛ mac) ∗
    memRegion (SP - 4128#64) (32 + 4096) ∗ F)) (by ac_rfl)) (bytes_entails_memRegion A st)
  rw [hl96] at h1
  have h2 := sat_sep_mono h1 (memRegion_split A 1 95 (by decide))
  have h3 := sat_sep_mono (Satisfies.of_eq h2 (Q := memRegion (SP - 4128#64) (32 + 4096) ∗
    ((memRegion A 1 ∗ memRegion (A + BitVec.ofNat 64 1) 95) ∗ (M ↦ₛ mac) ∗ F)) (by ac_rfl))
    (memRegion_split (SP - 4128#64) 32 4096 (by decide))
  rw [show SP - 4128#64 + BitVec.ofNat 64 32 = SP - 4096#64 by bv_omega] at h3
  exact ⟨memRegion (A + BitVec.ofNat 64 1) 95 ∗ memRegion (SP - 4128#64) 32 ∗ (M ↦ₛ mac) ∗ F,
    Satisfies.of_eq h3 (by ac_rfl)⟩

section
variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

/-- One step to the next instruction; the continuation also learns that the code is loaded. -/
theorem rnC (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State}
    (hr1 : c₁.status = .Running) (hr2 : c₂.status = .Running)
    {pc sp sp' pcn : BitVec 64} {r₁ r₂ r₁' r₂' : BitVec 5 → BitVec 64}
    {ps₁ ps₂ ps₁' ps₂' : PState} {m₁ m₂ m₁' m₂' : Memory} {v₁ v₂ : BitVec 5 → BitVec 128}
    {i : Instr}
    (hf1 : (P pl X).fetchMem m₁ pc = some i) (hf2 : (P pl X).fetchMem m₂ pc = some i)
    (e1 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) =
      mkS c₁ (pc + 4#64) r₁' sp' ps₁' m₁' v₁)
    (e2 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₂ pc r₂ sp ps₂ m₂ v₂) =
      mkS c₂ (pc + 4#64) r₂' sp' ps₂' m₂' v₂)
    (hl : leakedValues i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) = leakedValues i (mkS c₂ pc r₂ sp ps₂ m₂ v₂))
    (H₁ : (P pl X).CodeLoaded m₁) (H₂ : (P pl X).CodeLoaded m₂) (hpc : pc + 4#64 = pcn)
    (h : (P pl X).CodeLoaded m₁' → (P pl X).CodeLoaded m₂' →
      ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pcn r₁' sp' ps₁' m₁' v₁)
        (mkS c₂ pcn r₂' sp' ps₂' m₂' v₂)) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pc r₁ sp ps₁ m₁ v₁) (mkS c₂ pc r₂ sp ps₂ m₂ v₂) := by
  subst hpc
  exact rs hc hr1 hr2 hf1 hf2 e1 e2 hl (h (cl_exec hr1 hf1 e1 H₁) (cl_exec hr2 hf2 e2 H₂))

/-- `cbz xt, off` in both runs, with `xt = L` in both. -/
theorem rcbz (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State}
    (hr1 : c₁.status = .Running) (hr2 : c₂.status = .Running)
    {pc sp : BitVec 64} {r₁ r₂ : BitVec 5 → BitVec 64}
    {ps₁ ps₂ : PState} {m₁ m₂ : Memory} {v₁ v₂ : BitVec 5 → BitVec 128}
    {t : BitVec 5} {off L : BitVec 64} (ht : t ≠ 31#5)
    (hf1 : (P pl X).fetchMem m₁ pc = some (.cbz .W64 false (.gpr t) off))
    (hf2 : (P pl X).fetchMem m₂ pc = some (.cbz .W64 false (.gpr t) off))
    (h₁ : r₁ t = L) (h₂ : r₂ t = L)
    (h : ObsEquiv (P pl X) arity stop₁ stop₂
      (mkS c₁ (if L = 0#64 then pc + off else pc + 4#64) r₁ sp ps₁ m₁ v₁)
      (mkS c₂ (if L = 0#64 then pc + off else pc + 4#64) r₂ sp ps₂ m₂ v₂)) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pc r₁ sp ps₁ m₁ v₁) (mkS c₂ pc r₂ sp ps₂ m₂ v₂) :=
  rs hc hr1 hr2 hf1 hf2 (by rw [ex_cbz t ht off, h₁]) (by rw [ex_cbz t ht off, h₂]) rfl h

theorem chain_kp {c : State} {A M : BitVec 64} {q : BitVec 5 → BitVec 64} (h19 : q 19#5 = A)
    (h20 : q 20#5 = M) (hk : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat ≤ 28 → q k = c.regs.regs k) :
    Kp c A M q :=
  ⟨h19, h20, fun k h1 h2 => (hk k h1 h2).trans (readGpr_eq c k (by intro e; subst e; simp at h2)).symm⟩

set_option maxHeartbeats 4000000 in
/-- `poly1305_finish` in two runs, in continuation-passing form. Entered at its address with
`finishPre` (any frames `F₁`, `F₂`), equal `x0`, `x1`, `sp` and equal `leftover`, both runs
return (`FinishPost`: to `lr`, `sp` restored, callee-saved registers kept, code loaded, the state, the `mac`
and the 4128-byte frame owned again with unknown contents, `F` untouched). -/
theorem finish_rel (hc : StopCompat stop₁ stop₂) (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    (hz : Poly1305Libsodium.MemzeroOk X) (hs : MemsetOk X)
    (hL : Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthCtLib pl X)
    {c₁ c₂ : State} (hrun₁ : c₁.status = .Running) (hrun₂ : c₂.status = .Running)
    (hpc₁ : c₁.pc = pl.base + 1056#64) (hpc₂ : c₂.pc = pl.base + 1056#64)
    (hal : c₁.spAligned = true)
    (hcl₁ : (P pl X).CodeLoaded c₁.mem) (hcl₂ : (P pl X).CodeLoaded c₂.mem)
    (hsp : c₁.sp = c₂.sp) (hx0 : c₁.readReg64 Reg.x0 = c₂.readReg64 Reg.x0)
    (hx1 : c₁.readReg64 Reg.x1 = c₂.readReg64 Reg.x1)
    {F₁ F₂ : SepProp} {st₁ st₂ mac₁ mac₂ : List (BitVec 8)}
    (hpre₁ : c₁.mem ⊨ finishPre pl (st₁, mac₁) c₁ ∗ F₁)
    (hpre₂ : c₂.mem ⊨ finishPre pl (st₂, mac₂) c₂ ∗ F₂)
    (hpub : leftoverPub (st₁, mac₁) (st₂, mac₂))
    (K : ∀ f₁ f₂ : State, FinishPost pl X c₁ F₁ f₁ → FinishPost pl X c₂ F₂ f₂ →
      ObsEquiv (P pl X) arity stop₁ stop₂ f₁ f₂) :
    ObsEquiv (P pl X) arity stop₁ stop₂ c₁ c₂ := by
  have hal' : c₁.sp &&& 0b1111#64 = 0#64 := by simpa [State.spAligned] using hal
  have hal32 : (c₁.sp - 32#64) &&& 0b1111#64 = 0#64 := al16_sub _ 32 (by decide) (by decide) hal'
  -- the hooks
  have hna := hookName_memzero hL hz hs (fun f h1 h2 => by
    obtain ⟨R, hR⟩ := nb_mem hpre₁
    exact no_both h1 h2 hrun₁ hal hR)
  obtain ⟨fz, hfz, hzok⟩ := hz
  obtain ⟨fm, hfm, hmok⟩ := hs
  have hzat : (P pl X).externAt? (pl.ρ "sodium_memzero") = some fz :=
    (hookAt_of_linkOk hL "sodium_memzero" (by decide)).trans hfz
  have hmat : (P pl X).externAt? (pl.ρ "memset") = some fm :=
    (hookAt_of_linkOk hL "memset" (by decide)).trans hfm
  have C : Common pl X c₁ c₂ (c₁.readReg64 Reg.x0) (c₁.readReg64 Reg.x1) c₁.sp :=
    ⟨hP, ⟨fz, hzat, hzok⟩, hna, hal', rfl, hsp.symm, rfl, hx0.symm, rfl, hx1.symm⟩
  -- the memory of both runs
  obtain ⟨W0₁, W8₁, W16₁, W24₁, MI₁, RL₁, CL₁, hL16⟩ := pro_mem hpre₁ (c₁.regs.regs 29#5)
    (c₁.regs.regs 30#5) (c₁.regs.regs 19#5) (c₁.regs.regs 20#5)
  obtain ⟨W0₂, W8₂, W16₂, W24₂, MI₂, RL₂, CL₂, -⟩ := pro_mem hpre₂ (c₂.regs.regs 29#5)
    (c₂.regs.regs 30#5) (c₂.regs.regs 19#5) (c₂.regs.regs 20#5)
  rw [← hsp] at W0₂ W8₂ W16₂ W24₂ MI₂ RL₂ CL₂
  rw [← hx0, ← hx1] at MI₂
  rw [← hx0] at RL₂ CL₂
  have hstk : ∀ c : State, unpack64 (c.regs.regs 29#5) ++ unpack64 (c.regs.regs 30#5) ++
      unpack64 (c.regs.regs 19#5) ++ unpack64 (c.regs.regs 20#5) = stk c := fun c => by
    simp only [stk, readGpr_eq c _ (by decide : (29#5 : BitVec 5) ≠ 31#5),
      readGpr_eq c _ (by decide : (30#5 : BitVec 5) ≠ 31#5),
      readGpr_eq c _ (by decide : (19#5 : BitVec 5) ≠ 31#5),
      readGpr_eq c _ (by decide : (20#5 : BitVec 5) ≠ 31#5)]
  rw [hstk] at MI₁ MI₂
  have rA₁ : c₁.regs.regs 0#5 = c₁.readReg64 Reg.x0 := (readGpr_eq c₁ 0#5 (by decide)).symm
  have rA₂ : c₂.regs.regs 0#5 = c₁.readReg64 Reg.x0 :=
    (readGpr_eq c₂ 0#5 (by decide)).symm.trans hx0.symm
  have rM₁ : c₁.regs.regs 1#5 = c₁.readReg64 Reg.x1 := (readGpr_eq c₁ 1#5 (by decide)).symm
  have rM₂ : c₂.regs.regs 1#5 = c₁.readReg64 Reg.x1 :=
    (readGpr_eq c₂ 1#5 (by decide)).symm.trans hx1.symm
  generalize hA : c₁.readReg64 Reg.x0 = A at *
  generalize hM : c₁.readReg64 Reg.x1 = M at *
  have hP' := hP
  -- the states as `mkS`
  refine oe_congr (mkS_self c₁).symm (mkS_self c₂).symm ?_
  rw [hpc₁, hpc₂, ← hsp]
  -- +0x0: paciasp
  refine rn hc hrun₁ hrun₂ (f_0 hP hcl₁) (f_0 hP hcl₂) (ex_hint _) (ex_hint _) (lv0 fun _ => rfl) (a4 _ 1056 1060) ?_
  -- +0x4: stp x29, x30, [sp, #-0x20]!
  have e1 : c₁.sp + 0xffffffffffffffe0#64 = c₁.sp - 32#64 := by bv_omega
  refine rnC hc hrun₁ hrun₂ (f_4 hP hcl₁) (f_4 hP hcl₂)
    (ex_stp64_pre_sp 29#5 30#5 (by decide) (by decide) 0xffffffffffffffe0#64 hal'
      (by rw [e1]; exact W0₁) (by rw [e1]; exact W8₁))
    (ex_stp64_pre_sp 29#5 30#5 (by decide) (by decide) 0xffffffffffffffe0#64 hal'
      (by rw [e1]; exact W0₂) (by rw [e1]; exact W8₂))
    (by simp [leakedValues, evalAddrMode]) hcl₁ hcl₂ (a4 _ 1060 1064) ?_
  rw [e1]
  intro G₁ G₂
  -- +0x8: mov x29, sp
  refine rn hc hrun₁ hrun₂ (f_8 hP G₁) (f_8 hP G₂) (ex_add_gpr_sp 29#5 (by decide) 0#12)
    (ex_add_gpr_sp 29#5 (by decide) 0#12) (lv0 fun _ => rfl) (a4 _ 1064 1068) ?_
  -- +0xc: stp x19, x20, [sp, #0x10]
  refine rnC hc hrun₁ hrun₂ (f_c hP G₁) (f_c hP G₂)
    (ex_stp64_sp 19#5 20#5 (by decide) (by decide) 0x10#64 hal32 W16₁ W24₁)
    (ex_stp64_sp 19#5 20#5 (by decide) (by decide) 0x10#64 hal32 W16₂ W24₂)
    (by simp [leakedValues, evalAddrMode]) G₁ G₂ (a4 _ 1068 1072) ?_
  clear G₁ G₂
  intro G₁ G₂
  simp only [upd_apply, BitVec.reduceEq, ite_false] at G₁ G₂ ⊢
  -- +0x10: mov x20, x1
  refine rn hc hrun₁ hrun₂ (f_10 hP G₁) (f_10 hP G₂) (ex_mov 20#5 1#5 (by decide) (by decide))
    (ex_mov 20#5 1#5 (by decide) (by decide)) (lv0 fun _ => rfl) (a4 _ 1072 1076) ?_
  -- +0x14: mov x19, x0
  refine rn hc hrun₁ hrun₂ (f_14 hP G₁) (f_14 hP G₂) (ex_mov 19#5 0#5 (by decide) (by decide))
    (ex_mov 19#5 0#5 (by decide) (by decide)) (lv0 fun _ => rfl) (a4 _ 1076 1080) ?_
  -- +0x18: ldr x1, [x0, #0x40]  (leftover, public)
  have hpub' : u64At st₁ 64 = u64At st₂ 64 := hpub
  refine rq hc hrun₁ hrun₂
    (fun q => Kp c₁ A M q ∧ q 0#5 = A ∧ (q 1#5).toNat = u64At st₁ 64)
    (fun q => Kp c₂ A M q ∧ q 0#5 = A ∧ (q 1#5).toNat = u64At st₁ 64)
    (f_18 hP G₁) (f_18 hP G₂)
    (ex_ldr64_gpr 1#5 0#5 (by decide) (by decide) 0x40#64
      (by simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true]; rw [rA₁]; exact CL₁))
    (ex_ldr64_gpr 1#5 0#5 (by decide) (by decide) 0x40#64
      (by simp only [upd_apply, BitVec.reduceEq, ite_false, ite_true]; rw [rA₂]; exact CL₂))
    (by simp [leakedValues, evalAddrMode, upd_apply, rA₁, rA₂]) ?_ ?_ (a4 _ 1080 1084) ?_
  · refine ⟨chain_kp (by simp [upd_apply, rA₁]) (by simp [upd_apply, rM₁]) (fun k h1 h2 => ?_),
      by simp [upd_apply, rA₁], by simp [upd_apply, rA₁]; exact RL₁⟩
    have n1 : k ≠ 1#5 := by rintro rfl; simp at h1
    have n19 : k ≠ 19#5 := by rintro rfl; simp at h1
    have n20 : k ≠ 20#5 := by rintro rfl; simp at h1
    have n29 : k ≠ 29#5 := by rintro rfl; simp at h2
    simp [upd_apply, n1, n19, n20, n29]
  · refine ⟨chain_kp (by simp [upd_apply, rA₂]) (by simp [upd_apply, rM₂]) (fun k h1 h2 => ?_),
      by simp [upd_apply, rA₂], by simp [upd_apply, rA₂]; exact RL₂.trans hpub'.symm⟩
    have n1 : k ≠ 1#5 := by rintro rfl; simp at h1
    have n19 : k ≠ 19#5 := by rintro rfl; simp at h1
    have n20 : k ≠ 20#5 := by rintro rfl; simp at h1
    have n29 : k ≠ 29#5 := by rintro rfl; simp at h2
    simp [upd_apply, n1, n19, n20, n29]
  rintro q₁ q₂ ρ₁ ρ₂ ⟨k₁, x0₁, x1₁⟩ ⟨k₂, x0₂, x1₂⟩
  have x1₂' : q₂ 1#5 = q₁ 1#5 := BitVec.eq_of_toNat_eq (x1₂.trans x1₁.symm)
  -- +0x1c: cbz x1, +0x4c
  refine rcbz hc hrun₁ hrun₂ (by decide) (f_1c hP G₁) (f_1c hP G₂) rfl x1₂' ?_
  by_cases hL0 : q₁ 1#5 = 0#64
  · rw [if_pos hL0, show pl.base + 1084#64 + 0x4c#64 = pl.base + 1160#64 by
      rw [BitVec.add_assoc]; rfl]
    exact at1160 hc C ⟨hrun₁, k₁, G₁, MI₁, rfl⟩ ⟨hrun₂, k₂, G₂, MI₂, rfl⟩ K
  · rw [if_neg hL0, a4 _ 1084 1088]
    have hL1 : 1 ≤ (q₁ 1#5).toNat := by
      rcases Nat.eq_zero_or_pos (q₁ 1#5).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hL0
      · exact h
    exact pad_rel hc C hmok hmat ⟨hrun₁, k₁, G₁, MI₁, rfl⟩ ⟨hrun₂, k₂, G₂, MI₂, rfl⟩ hL1
      (by rw [x1₁]; exact hL16) x0₁ x0₂ rfl x1₂' K


end

end Poly1305DebianCtFinish

end
end

section
section
/-! # `relOk_poly1305_finish_v2` from plc-core's `Poly1305DebianCtFinish.finish_rel`

The accepted proof of the milestone `ctInternalOk_poly1305_finish` (batch q470, workspace
`Solutions/Poly1305DebianCtFinish`) proves the two-run contract `finish_rel` in continuation-passing
form, asking only for equal `x0`, `x1` and `sp` at entry and returning `FinishPost`. The published
contract asks more at entry and gives the state and tag back as plain regions. -/

set_option autoImplicit false

namespace Poly1305DebianCt

open Arm64 Arm64.Obj Leakage Poly1305DebianCtFw

theorem finLeaf_post {m : Memory} (a b : BitVec 64) (st mac : List (BitVec 8)) (S F : SepProp)
    (hs : st.length = 96) (hm : mac.length = 16) (h : m ⊨ ((a ↦ₛ st) ∗ (b ↦ₛ mac) ∗ S) ∗ F) :
    m ⊨ (memRegion a 96 ∗ memRegion b 16 ∗ S) ∗ F := by
  have e1 := bytes_entails_memRegion a st
  have e2 := bytes_entails_memRegion b mac
  rw [hs] at e1
  rw [hm] at e2
  exact Satisfies.mono (sepConj_mono (sepConj_mono e1 (sepConj_mono e2 (Entails.refl S)))
    (Entails.refl F)) h

theorem relOk_poly1305_finish_v2_dev :
    ∀ pl : Placement, lib.Placeable pl → GuardUniform pl →
    ∀ externs : String → Option (State → State), Poly1305Libsodium.MemzeroOk externs →
      MemsetOk externs → Link.PlacedLib.LinkOk lib pl externs →
    ∀ stop₁ stop₂ : State → Prop,
      (∀ a b : State, a.pc = b.pc → a.sp = b.sp → a.status = b.status → (stop₁ a ↔ stop₂ b)) →
    ∀ (x₁ x₂ : List (BitVec 8) × List (BitVec 8)) (R₁ R₂ : SepProp) (c₁ c₂ : State),
      c₁.pc = lib.fnAddr pl "poly1305_finish [libsodium_la_poly1305_donna]" →
      c₂.pc = c₁.pc → c₂.sp = c₁.sp →
      c₁.status = .Running → c₂.status = .Running → c₁.spAligned = true →
      (∀ i : BitVec 5, (i.toNat ≤ 1 ∨ (19 ≤ i.toNat ∧ i.toNat ≤ 30)) → c₂.regs.regs i = c₁.regs.regs i) →
      (lib.program pl externs).CodeLoaded c₁.mem → (lib.program pl externs).CodeLoaded c₂.mem →
      (c₁.mem ⊨ finishPre pl x₁ c₁ ∗ R₁) → (c₂.mem ⊨ finishPre pl x₂ c₂ ∗ R₂) →
      leftoverPub x₁ x₂ →
      (∀ f₁ f₂ : State,
        (Returned c₁ f₁ ∧ CalleeSavedPreserved c₁ f₁ ∧ (lib.program pl externs).CodeLoaded f₁.mem ∧
          (f₁.mem ⊨ (memRegion (c₁.readReg64 Reg.x0) 96 ∗ memRegion (c₁.readReg64 Reg.x1) 16 ∗
            stackFrame c₁ 4128) ∗ R₁)) →
        (Returned c₂ f₂ ∧ CalleeSavedPreserved c₂ f₂ ∧ (lib.program pl externs).CodeLoaded f₂.mem ∧
          (f₂.mem ⊨ (memRegion (c₂.readReg64 Reg.x0) 96 ∗ memRegion (c₂.readReg64 Reg.x1) 16 ∗
            stackFrame c₂ 4128) ∗ R₂)) →
        ObsEquiv (lib.program pl externs) arity stop₁ stop₂ f₁ f₂) →
      ObsEquiv (lib.program pl externs) arity stop₁ stop₂ c₁ c₂ := by
  intro pl hP _hG ex hZ hM hL stop₁ stop₂ hc x₁ x₂ R₁ R₂ c₁ c₂ hpc hpc₂ hsp₂ hr₁ hr₂ hal hreg
    hcl₁ hcl₂ hp₁ hp₂ hpub K
  obtain ⟨st₁, mac₁⟩ := x₁
  obtain ⟨st₂, mac₂⟩ := x₂
  have hc' : StopCompat stop₁ stop₂ := hc
  have h0 := hreg 0#5 (Or.inl (by decide))
  have h1 := hreg 1#5 (Or.inl (by decide))
  have hx0 : c₁.readReg64 Reg.x0 = c₂.readReg64 Reg.x0 := by
    simp only [Reg.x0, readGpr_unfold]; simp [h0]
  have hx1 : c₁.readReg64 Reg.x1 = c₂.readReg64 Reg.x1 := by
    simp only [Reg.x1, readGpr_unfold]; simp [h1]
  have hfa : lib.fnAddr pl "poly1305_finish [libsodium_la_poly1305_donna]" = pl.base + 1056#64 := rfl
  rw [hfa] at hpc
  refine Poly1305DebianCtFinish.finish_rel hc' hP hZ hM hL hr₁ hr₂ hpc (hpc₂.trans hpc) hal hcl₁ hcl₂
    hsp₂.symm hx0 hx1 hp₁ hp₂ hpub ?_
  intro f₁ f₂ F₁ F₂
  obtain ⟨ret₁, ccp₁, cl₁, s₁, m₁, ls₁, lm₁, hm₁⟩ := F₁
  obtain ⟨ret₂, ccp₂, cl₂, s₂, m₂, ls₂, lm₂, hm₂⟩ := F₂
  exact K f₁ f₂ ⟨ret₁, ccp₁.2, cl₁, finLeaf_post _ _ _ _ _ _ ls₁ lm₁ hm₁⟩
    ⟨ret₂, ccp₂.2, cl₂, finLeaf_post _ _ _ _ _ _ ls₂ lm₂ hm₂⟩

end Poly1305DebianCt

end
end

section
open Poly1305DebianCt

open Arm64 Arm64.Obj Leakage

theorem solution :
    ∀ pl : Placement, lib.Placeable pl → GuardUniform pl →
    ∀ externs : String → Option (State → State), Poly1305Libsodium.MemzeroOk externs →
      MemsetOk externs → Link.PlacedLib.LinkOk lib pl externs →
    ∀ stop₁ stop₂ : State → Prop,
      (∀ a b : State, a.pc = b.pc → a.sp = b.sp → a.status = b.status → (stop₁ a ↔ stop₂ b)) →
    ∀ (x₁ x₂ : List (BitVec 8) × List (BitVec 8)) (R₁ R₂ : SepProp) (c₁ c₂ : State),
      c₁.pc = lib.fnAddr pl "poly1305_finish [libsodium_la_poly1305_donna]" →
      c₂.pc = c₁.pc → c₂.sp = c₁.sp →
      c₁.status = .Running → c₂.status = .Running → c₁.spAligned = true →
      (∀ i : BitVec 5, (i.toNat ≤ 1 ∨ (19 ≤ i.toNat ∧ i.toNat ≤ 30)) → c₂.regs.regs i = c₁.regs.regs i) →
      (lib.program pl externs).CodeLoaded c₁.mem → (lib.program pl externs).CodeLoaded c₂.mem →
      (c₁.mem ⊨ finishPre pl x₁ c₁ ∗ R₁) → (c₂.mem ⊨ finishPre pl x₂ c₂ ∗ R₂) →
      leftoverPub x₁ x₂ →
      (∀ f₁ f₂ : State,
        (Returned c₁ f₁ ∧ CalleeSavedPreserved c₁ f₁ ∧ (lib.program pl externs).CodeLoaded f₁.mem ∧
          (f₁.mem ⊨ (memRegion (c₁.readReg64 Reg.x0) 96 ∗ memRegion (c₁.readReg64 Reg.x1) 16 ∗
            stackFrame c₁ 4128) ∗ R₁)) →
        (Returned c₂ f₂ ∧ CalleeSavedPreserved c₂ f₂ ∧ (lib.program pl externs).CodeLoaded f₂.mem ∧
          (f₂.mem ⊨ (memRegion (c₂.readReg64 Reg.x0) 96 ∗ memRegion (c₂.readReg64 Reg.x1) 16 ∗
            stackFrame c₂ 4128) ∗ R₂)) →
        ObsEquiv (lib.program pl externs) arity stop₁ stop₂ f₁ f₂) →
      ObsEquiv (lib.program pl externs) arity stop₁ stop₂ c₁ c₂ := by
  apply Poly1305DebianCt.relOk_poly1305_finish_v2_dev <;> assumption

end
