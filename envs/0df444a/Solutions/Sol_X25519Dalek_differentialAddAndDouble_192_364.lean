-- Prove2me | solution 1 for X25519Dalek.differentialAddAndDouble_192_364
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T19:52:29.35926+00:00
-- url     : https://prove2.me/submissions/136fb297-5974-4d94-a187-bb296cb1f605

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

theorem y_add {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubShift .W64 .ADD (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r a + r b)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, hb]
  exact h

theorem y_sub {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubShift .W64 .SUB (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r a - r b)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, hb]
  exact h

theorem y_addlsr {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubShift .W64 .ADD (.gpr d) (.gpr a) (.gpr b) .LSR 51))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r a + r b >>> 51)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, hb]
  exact h

theorem y_andi {d a : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) {k : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalImm .W64 .AND (.gpr d) (.gpr a) k))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r a &&& k)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha]
  exact h

theorem y_lsr51 {d a : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.bitfield .W64 .UBFM (.gpr d) (.gpr a) 51 63))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r a >>> 51)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha]
  exact h

theorem y_umaddl {d a b c : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hc : c ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.dataProc3 .W64 .UMADDL (.gpr d) (.gpr a) (.gpr b) (.gpr c)))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r c + ((r a).setWidth 32).setWidth 64 * ((r b).setWidth 32).setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, hb, hc]
  exact h

theorem y_ldp_r {d1 d2 b : BitVec 5} {off A A8 w1 w2 : BitVec 64} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5) (hb : b ≠ 31#5) (hA : r b + off = A) (hA8 : A + 8#64 = A8) (c1 : m.canRead A 8 = true) (c2 : m.canRead A8 8 = true) (e1 : m.read64 A = w1) (e2 : m.read64 A8 = w2) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) (upd (upd r d1 w1) d2 w2) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd1, hd2, hb, hA, hA8, c1, c2, e1, e2]
  exact h

theorem y_stp_sp {t1 t2 : BitVec 5} {off A A8 : BitVec 64} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (hA8 : A + 8#64 = A8) (c1 : m.canWrite A 8 = true) (c2 : m.canWrite A8 8 = true) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.Offset .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps ((m.write64 A (r t1)).write64 A8 (r t2)) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ht1, ht2, hal, hA, hA8, c1, c2]
  exact h

theorem y_str_sp {t : BitVec 5} {off A : BitVec 64} (ht : t ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (c : m.canWrite A 8 = true) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 (.gpr t) (.Offset .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps (m.write64 A (r t)) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ht, hal, hA, c]
  exact h

theorem y_addi_sp {d : BitVec 5} {k : BitVec 12} (hd : d ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD (.gpr d) .sp k false))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (sp + k.setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, BitVec.truncate_eq_setWidth]
  exact h

theorem y_movz32 {d : BitVec 5} {k : BitVec 16} (hd : d ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.moveWide .W32 .MOVZ (.gpr d) k 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (((k.setWidth 64).setWidth 32).setWidth 64)) sp ps m v) Q) :
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

theorem x_add {d a b : BitVec 5} {x y : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubShift .W64 .ADD (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (hpc : pc + 4#64 = pc') (ex : r a = x) (ey : r b = y)
    (h : ∀ t, t = x + y → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex ey; exact y_add hd ha hb hrun hf (h _ rfl)

theorem x_sub {d a b : BitVec 5} {x y : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubShift .W64 .SUB (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (hpc : pc + 4#64 = pc') (ex : r a = x) (ey : r b = y)
    (h : ∀ t, t = x - y → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex ey; exact y_sub hd ha hb hrun hf (h _ rfl)

theorem x_addlsr {d a b : BitVec 5} {x y : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubShift .W64 .ADD (.gpr d) (.gpr a) (.gpr b) .LSR 51))
    (hpc : pc + 4#64 = pc') (ex : r a = x) (ey : r b = y)
    (h : ∀ t, t = x + y >>> 51 → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex ey; exact y_addlsr hd ha hb hrun hf (h _ rfl)

theorem x_andi {d a : BitVec 5} {k x : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalImm .W64 .AND (.gpr d) (.gpr a) k))
    (hpc : pc + 4#64 = pc') (ex : r a = x)
    (h : ∀ t, t = x &&& k → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_andi hd ha hrun hf (h _ rfl)

theorem x_lsr51 {d a : BitVec 5} {x : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.bitfield .W64 .UBFM (.gpr d) (.gpr a) 51 63))
    (hpc : pc + 4#64 = pc') (ex : r a = x)
    (h : ∀ t, t = x >>> 51 → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_lsr51 hd ha hrun hf (h _ rfl)

theorem x_umaddl {d a b c : BitVec 5} {x y z : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hb : b ≠ 31#5) (hc : c ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.dataProc3 .W64 .UMADDL (.gpr d) (.gpr a) (.gpr b) (.gpr c)))
    (hpc : pc + 4#64 = pc') (ex : r a = x) (ey : r b = y) (ez : r c = z)
    (h : ∀ t, t = z + (x.setWidth 32).setWidth 64 * (y.setWidth 32).setWidth 64 →
      Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex ey ez; exact y_umaddl hd ha hb hc hrun hf (h _ rfl)

theorem x_movz32 {d : BitVec 5} {k : BitVec 16} (hd : d ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.moveWide .W32 .MOVZ (.gpr d) k 0))
    (hpc : pc + 4#64 = pc')
    (h : Reach p (mkS s0 pc' (upd r d (((k.setWidth 64).setWidth 32).setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; exact y_movz32 hd hrun hf h

/-- `ldp` from a general register base: the two words come with their read facts. -/
theorem x_ldp_r {d1 d2 b : BitVec 5} {off x a w1 w2 : BitVec 64} {i : Nat} {B : BitVec 64} (hd1 : d1 ≠ 31#5)
    (hd2 : d2 ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.Offset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (f1 : m.read64 (a + BitVec.ofNat 64 (8 * i)) = w1 ∧ m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true)
    (hB : a + BitVec.ofNat 64 (8 * (i + 1)) = B)
    (f2 : m.read64 B = w2 ∧ m.canRead B 8 = true)
    (h : Reach p (mkS s0 pc' (upd (upd r d1 w1) d2 w2) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_ldp_r hd1 hd2 hb hA ((w8 a i).trans hB) f1.2 f2.2 f1.1 f2.1 hrun hf h

/-- Stores into word `i` (and `i + 1`) of the word list at position 1. -/
theorem x_stp_sp {t1 t2 : BitVec 5} {off a v1 v2 : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    {i : Nat} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hi : i + 1 < ws.length) (e1 : r t1 = v1) (e2 : r t2 = v2)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (ws.set i v1).set (i + 1) v2) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc e1 e2
  obtain ⟨-, -, c1⟩ := sat_words_read hs i (by omega)
  obtain ⟨-, -, c2⟩ := sat_words_read hs (i + 1) hi
  refine y_stp_sp ht1 ht2 hal hA (w8 a i) c1 c2 hrun hf ?_
  exact Reach.wr64x2 i hs rfl rfl hi h

theorem x_str_sp {t : BitVec 5} {off a v1 : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    {i : Nat} (ht : t ≠ 31#5) (hal : (sp &&& 15#64) = 0#64)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 (.gpr t) (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hi : i < ws.length) (e1 : r t = v1)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* ws.set i v1) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc e1
  obtain ⟨-, -, c1⟩ := sat_words_read hs i hi
  refine y_str_sp ht hal hA c1 hrun hf ?_
  exact Reach.wr64 i hs rfl hi h

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

theorem blk12 : blk 12 = x25519CliBlk12 := rfl

theorem len12 : x25519CliBlk12.code.length = 952 := by decide +kernel

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (j : Nat) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem c12_192 : (bprog mpl j).fetchMem m (mpl.base 12 + 192#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0d#5) (Reg.gpr 0x10#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000030#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 192) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0d#5) (Reg.gpr 0x10#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000030#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_196 : (bprog mpl j).fetchMem m (mpl.base 12 + 196#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x00#5) (Reg.gpr 0x01#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 196) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x00#5) (Reg.gpr 0x01#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_200 : (bprog mpl j).fetchMem m (mpl.base 12 + 200#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 200) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_204 : (bprog mpl j).fetchMem m (mpl.base 12 + 204#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x09#5) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000000#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 204) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x09#5) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000000#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_208 : (bprog mpl j).fetchMem m (mpl.base 12 + 208#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0b#5) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000020#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 208) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0b#5) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000020#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_212 : (bprog mpl j).fetchMem m (mpl.base 12 + 212#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 212) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_216 : (bprog mpl j).fetchMem m (mpl.base 12 + 216#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x08#5) (Reg.gpr 0x0e#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000010#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 216) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x08#5) (Reg.gpr 0x0e#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000010#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_220 : (bprog mpl j).fetchMem m (mpl.base 12 + 220#64) =
    some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x01#5) 0x0001#16 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 220) (inst := (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x01#5) 0x0001#16 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_224 : (bprog mpl j).fetchMem m (mpl.base 12 + 224#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x12#5) (Reg.gpr 0x00#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 224) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x12#5) (Reg.gpr 0x00#5) (AddrMode.Offset (Reg.gpr 0x13#5) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_228 : (bprog mpl j).fetchMem m (mpl.base 12 + 228#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x11#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 228) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x11#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_232 : (bprog mpl j).fetchMem m (mpl.base 12 + 232#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0f#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 232) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0f#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_236 : (bprog mpl j).fetchMem m (mpl.base 12 + 236#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) (Reg.gpr 0x18#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 236) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) (Reg.gpr 0x18#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_240 : (bprog mpl j).fetchMem m (mpl.base 12 + 240#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x0d#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 240) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x0d#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_244 : (bprog mpl j).fetchMem m (mpl.base 12 + 244#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x0f#5) (Reg.gpr 0x11#5) (AddrMode.Offset (Reg.sp) 0x0000000000000058#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 244) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x0f#5) (Reg.gpr 0x11#5) (AddrMode.Offset (Reg.sp) 0x0000000000000058#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_248 : (bprog mpl j).fetchMem m (mpl.base 12 + 248#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0f#5) (Reg.gpr 0x10#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 248) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0f#5) (Reg.gpr 0x10#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_252 : (bprog mpl j).fetchMem m (mpl.base 12 + 252#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) (Reg.gpr 0x0c#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 252) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) (Reg.gpr 0x0c#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_256 : (bprog mpl j).fetchMem m (mpl.base 12 + 256#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x11#5) (Reg.gpr 0x12#5) (Reg.gpr 0x0e#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 256) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x11#5) (Reg.gpr 0x12#5) (Reg.gpr 0x0e#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_260 : (bprog mpl j).fetchMem m (mpl.base 12 + 260#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 260) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_264 : (bprog mpl j).fetchMem m (mpl.base 12 + 264#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x10#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 264) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x10#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_268 : (bprog mpl j).fetchMem m (mpl.base 12 + 268#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x0f#5) (Reg.gpr 0x11#5) (AddrMode.Offset (Reg.sp) 0x0000000000000068#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 268) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x0f#5) (Reg.gpr 0x11#5) (AddrMode.Offset (Reg.sp) 0x0000000000000068#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_272 : (bprog mpl j).fetchMem m (mpl.base 12 + 272#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0f#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 272) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0f#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_276 : (bprog mpl j).fetchMem m (mpl.base 12 + 276#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x00#5) (Reg.gpr 0x0b#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 276) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x00#5) (Reg.gpr 0x0b#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_280 : (bprog mpl j).fetchMem m (mpl.base 12 + 280#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0f#5) (Reg.gpr 0x0f#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 280) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0f#5) (Reg.gpr 0x0f#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_284 : (bprog mpl j).fetchMem m (mpl.base 12 + 284#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000078#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 284) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000078#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_288 : (bprog mpl j).fetchMem m (mpl.base 12 + 288#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 288) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_292 : (bprog mpl j).fetchMem m (mpl.base 12 + 292#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0f#5) 51 63) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 292) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0d#5) (Reg.gpr 0x0f#5) 51 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_296 : (bprog mpl j).fetchMem m (mpl.base 12 + 296#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0c#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 296) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0c#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_300 : (bprog mpl j).fetchMem m (mpl.base 12 + 300#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 300) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_304 : (bprog mpl j).fetchMem m (mpl.base 12 + 304#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 304) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_308 : (bprog mpl j).fetchMem m (mpl.base 12 + 308#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0e#5) (Reg.gpr 0x08#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 308) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0e#5) (Reg.gpr 0x08#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_312 : (bprog mpl j).fetchMem m (mpl.base 12 + 312#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x008#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 312) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x008#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_316 : (bprog mpl j).fetchMem m (mpl.base 12 + 316#64) =
    some (Instr.dataProc3 (RegWidth.W64) (DataProc3Op.UMADDL) (Reg.gpr 0x0b#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x19#5) (Reg.gpr 0x0b#5)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 316) (inst := (Instr.dataProc3 (RegWidth.W64) (DataProc3Op.UMADDL) (Reg.gpr 0x0b#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x19#5) (Reg.gpr 0x0b#5))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_320 : (bprog mpl j).fetchMem m (mpl.base 12 + 320#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 320) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_324 : (bprog mpl j).fetchMem m (mpl.base 12 + 324#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0a#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x0a#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 324) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0a#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x0a#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_328 : (bprog mpl j).fetchMem m (mpl.base 12 + 328#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 328) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_332 : (bprog mpl j).fetchMem m (mpl.base 12 + 332#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0d#5) (Reg.gpr 0x0c#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 332) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0d#5) (Reg.gpr 0x0c#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_336 : (bprog mpl j).fetchMem m (mpl.base 12 + 336#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 336) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_340 : (bprog mpl j).fetchMem m (mpl.base 12 + 340#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x0000000000000080#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 340) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x0000000000000080#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_344 : (bprog mpl j).fetchMem m (mpl.base 12 + 344#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0b#5) (Reg.gpr 0x0f#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 344) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0b#5) (Reg.gpr 0x0f#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_348 : (bprog mpl j).fetchMem m (mpl.base 12 + 348#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x0c#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 348) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x0c#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_352 : (bprog mpl j).fetchMem m (mpl.base 12 + 352#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x0000000000000090#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 352) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x0000000000000090#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_356 : (bprog mpl j).fetchMem m (mpl.base 12 + 356#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.sp) 0x0a8#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 356) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.sp) 0x0a8#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_360 : (bprog mpl j).fetchMem m (mpl.base 12 + 360#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 360) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64))) (by decide) rfl (by decide +kernel) hk
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

theorem pick2 (A1 A2 R : SepProp) : (A1 ∗ A2 ∗ R) = (A2 ∗ A1 ∗ R) := by ac_rfl
theorem pick3 (A1 A2 A3 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ R) = (A3 ∗ A1 ∗ A2 ∗ R) := by ac_rfl
theorem pick7 (A1 A2 A3 A4 A5 A6 A7 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ R) = (A7 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ R) := by ac_rfl
theorem pick8 (A1 A2 A3 A4 A5 A6 A7 A8 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ R) = (A8 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ R) := by ac_rfl
theorem pick24 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ R) = (A24 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ R) := by ac_rfl

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

theorem mask51_toNat (d : BitVec 64) :
    (d &&& 2251799813685247#64).toNat = d.toNat % 2 ^ 51 := by
  rw [BitVec.toNat_and, show (2251799813685247#64).toNat = 2 ^ 51 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem lsr51_toNat (d : BitVec 64) :
    (d >>> 51).toNat = d.toNat / 2 ^ 51 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem umaddl19_lsr51_toNat (d0 d4 : BitVec 64) :
    ((d0 &&& 2251799813685247#64) +
      BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64).toNat =
      d0.toNat % 2 ^ 51 + (d4.toNat / 2 ^ 51) * 19 := by
  have hd4 : d4.toNat < 2 ^ 64 := d4.isLt
  have hze : (BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51))).toNat = d4.toNat / 2 ^ 51 := by
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, lsr51_toNat]
    omega
  have hm := mask51_toNat d0
  rw [BitVec.toNat_add, BitVec.toNat_mul, hze, hm, show (19#64).toNat = 19 from rfl]
  omega

theorem add_mask51_lsr51_toNat (di dprev : BitVec 64) :
    ((di &&& 2251799813685247#64) + (dprev >>> 51)).toNat =
      di.toNat % 2 ^ 51 + dprev.toNat / 2 ^ 51 := by
  have hprev : dprev.toNat < 2 ^ 64 := dprev.isLt
  rw [BitVec.toNat_add, mask51_toNat, lsr51_toNat]
  omega

/-- Unconditional limb bound (`< 2^52`) for the 5-limb `FieldElement51::reduce` output. -/
theorem fe51Reduce_bounded (d0 d1 d2 d3 d4 : BitVec 64) :
    ((d0 &&& 2251799813685247#64) +
      BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64).toNat < 2 ^ 52 ∧
    ((d1 &&& 2251799813685247#64) + (d0 >>> 51)).toNat < 2 ^ 52 ∧
    ((d2 &&& 2251799813685247#64) + (d1 >>> 51)).toNat < 2 ^ 52 ∧
    ((d3 &&& 2251799813685247#64) + (d2 >>> 51)).toNat < 2 ^ 52 ∧
    ((d4 &&& 2251799813685247#64) + (d3 >>> 51)).toNat < 2 ^ 52 := by
  have h0 := d0.isLt; have h1 := d1.isLt; have h2 := d2.isLt; have h3 := d3.isLt; have h4 := d4.isLt
  rw [umaddl19_lsr51_toNat, add_mask51_lsr51_toNat, add_mask51_lsr51_toNat,
    add_mask51_lsr51_toNat, add_mask51_lsr51_toNat]
  omega

/-- Unconditional modular identity for `FieldElement51::reduce`: the reduced 5-limb value equals
    the unreduced 5-limb value modulo `p25519 = 2^255 - 19`. -/
theorem fe51Reduce_val_mod (d0 d1 d2 d3 d4 : BitVec 64) :
    fe51Val
      ((d0 &&& 2251799813685247#64) +
        BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64)
      ((d1 &&& 2251799813685247#64) + (d0 >>> 51))
      ((d2 &&& 2251799813685247#64) + (d1 >>> 51))
      ((d3 &&& 2251799813685247#64) + (d2 >>> 51))
      ((d4 &&& 2251799813685247#64) + (d3 >>> 51)) % p25519 =
    fe51Val d0 d1 d2 d3 d4 % p25519 := by
  have hid :
      fe51Val
        ((d0 &&& 2251799813685247#64) +
          BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64)
        ((d1 &&& 2251799813685247#64) + (d0 >>> 51))
        ((d2 &&& 2251799813685247#64) + (d1 >>> 51))
        ((d3 &&& 2251799813685247#64) + (d2 >>> 51))
        ((d4 &&& 2251799813685247#64) + (d3 >>> 51)) +
      p25519 * (d4.toNat / 2 ^ 51) =
      fe51Val d0 d1 d2 d3 d4 := by
    unfold fe51Val p25519
    rw [umaddl19_lsr51_toNat, add_mask51_lsr51_toNat, add_mask51_lsr51_toNat,
      add_mask51_lsr51_toNat, add_mask51_lsr51_toNat]
    omega
  rw [← hid, Nat.add_mul_mod_self_left]

theorem bv64_add_bias0_sub (a b : BitVec 64) :
    (a + 36028797018963664#64) - b = (a - b) + 36028797018963664#64 := by
  bv_omega

theorem sub_bias0_toNat (a b : BitVec 64) (ha : a.toNat < 2 ^ 54) (hb : b.toNat < 2 ^ 54) :
    ((a - b) + 36028797018963664#64).toNat = a.toNat + 36028797018963664 - b.toNat := by
  bv_omega

theorem sub_bias1_toNat (a b : BitVec 64) (ha : a.toNat < 2 ^ 54) (hb : b.toNat < 2 ^ 54) :
    ((a - b) + 36028797018963952#64).toNat = a.toNat + 36028797018963952 - b.toNat := by
  bv_omega

/-- Modulo `p25519` identity for biased 5-limb subtraction (`a + 16*p - b`). -/
theorem fe51Sub_val_mod (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64) {B1 B2 : Nat}
    (ha : a0.toNat < B1 ∧ a1.toNat < B1 ∧ a2.toNat < B1 ∧
          a3.toNat < B1 ∧ a4.toNat < B1)
    (hb : b0.toNat < B2 ∧ b1.toNat < B2 ∧ b2.toNat < B2 ∧
          b3.toNat < B2 ∧ b4.toNat < B2)
    (hB1 : decide (B1 ≤ 2 ^ 54) = true := by decide)
    (hB2 : decide (B2 ≤ 2 ^ 54) = true := by decide) :
    fe51Val
      ((a0 - b0) + 36028797018963664#64)
      ((a1 - b1) + 36028797018963952#64)
      ((a2 - b2) + 36028797018963952#64)
      ((a3 - b3) + 36028797018963952#64)
      ((a4 - b4) + 36028797018963952#64) % p25519 =
    fpSub (fe51Val a0 a1 a2 a3 a4 % p25519) (fe51Val b0 b1 b2 b3 b4 % p25519) := by
  have hle1 : B1 ≤ 2 ^ 54 := of_decide_eq_true hB1
  have hle2 : B2 ≤ 2 ^ 54 := of_decide_eq_true hB2
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4⟩
  have hval :
      fe51Val
        ((a0 - b0) + 36028797018963664#64)
        ((a1 - b1) + 36028797018963952#64)
        ((a2 - b2) + 36028797018963952#64)
        ((a3 - b3) + 36028797018963952#64)
        ((a4 - b4) + 36028797018963952#64) =
      fe51Val a0 a1 a2 a3 a4 + 16 * p25519 - fe51Val b0 b1 b2 b3 b4 := by
    unfold fe51Val p25519
    rw [sub_bias0_toNat a0 b0 (by omega) (by omega), sub_bias1_toNat a1 b1 (by omega) (by omega),
        sub_bias1_toNat a2 b2 (by omega) (by omega), sub_bias1_toNat a3 b3 (by omega) (by omega),
        sub_bias1_toNat a4 b4 (by omega) (by omega)]
    omega
  rw [hval]
  unfold fpSub
  have hlt : fe51Val b0 b1 b2 b3 b4 < 16 * p25519 := by
    unfold fe51Val p25519; omega
  have hdiv : fe51Val b0 b1 b2 b3 b4 =
      p25519 * (fe51Val b0 b1 b2 b3 b4 / p25519) + fe51Val b0 b1 b2 b3 b4 % p25519 :=
    (Nat.div_add_mod _ _).symm
  have hq : fe51Val b0 b1 b2 b3 b4 / p25519 ≤ 15 := by
    unfold p25519 at hlt ⊢; omega
  have hmodB_lt : fe51Val b0 b1 b2 b3 b4 % p25519 < p25519 :=
    Nat.mod_lt _ (by unfold p25519; omega)
  have hmodB : (fe51Val b0 b1 b2 b3 b4 % p25519) % p25519 = fe51Val b0 b1 b2 b3 b4 % p25519 :=
    Nat.mod_eq_of_lt hmodB_lt
  rw [hmodB]
  have hrew : fe51Val a0 a1 a2 a3 a4 + 16 * p25519 - fe51Val b0 b1 b2 b3 b4 =
      (fe51Val a0 a1 a2 a3 a4 + (p25519 - fe51Val b0 b1 b2 b3 b4 % p25519)) +
        p25519 * (15 - fe51Val b0 b1 b2 b3 b4 / p25519) := by
    unfold p25519 at hdiv hq hmodB_lt ⊢
    omega
  rw [hrew, Nat.add_mul_mod_self_left, Nat.add_sub_assoc (Nat.le_of_lt hmodB_lt),
      ← Nat.mod_add_mod]

/-- Limb bounds for 5-limb unreduced addition `a + b`. -/
theorem fe51Add_bounded (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64) (B : Nat) {B1 B2 : Nat}
    (ha : a0.toNat < B1 ∧ a1.toNat < B1 ∧ a2.toNat < B1 ∧ a3.toNat < B1 ∧ a4.toNat < B1)
    (hb : b0.toNat < B2 ∧ b1.toNat < B2 ∧ b2.toNat < B2 ∧ b3.toNat < B2 ∧ b4.toNat < B2)
    (hB : decide (B1 + B2 ≤ B ∧ B ≤ 2 ^ 64) = true := by decide) :
    (a0 + b0).toNat < B ∧ (a1 + b1).toNat < B ∧ (a2 + b2).toNat < B ∧
    (a3 + b3).toNat < B ∧ (a4 + b4).toNat < B := by
  have ⟨h1, h2⟩ := of_decide_eq_true hB
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4⟩
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

/-- Modulo `p25519` identity for 5-limb unreduced addition `a + b`. -/
theorem fe51Add_val_mod (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64) {B1 B2 : Nat}
    (ha : a0.toNat < B1 ∧ a1.toNat < B1 ∧ a2.toNat < B1 ∧
          a3.toNat < B1 ∧ a4.toNat < B1)
    (hb : b0.toNat < B2 ∧ b1.toNat < B2 ∧ b2.toNat < B2 ∧
          b3.toNat < B2 ∧ b4.toNat < B2)
    (hB1 : decide (B1 ≤ 2 ^ 54) = true := by decide)
    (hB2 : decide (B2 ≤ 2 ^ 54) = true := by decide) :
    fe51Val (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) (a4 + b4) % p25519 =
    fpAdd (fe51Val a0 a1 a2 a3 a4 % p25519) (fe51Val b0 b1 b2 b3 b4 % p25519) := by
  have hle1 : B1 ≤ 2 ^ 54 := of_decide_eq_true hB1
  have hle2 : B2 ≤ 2 ^ 54 := of_decide_eq_true hB2
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4⟩
  have h0 : (a0 + b0).toNat = a0.toNat + b0.toNat := by bv_omega
  have h1 : (a1 + b1).toNat = a1.toNat + b1.toNat := by bv_omega
  have h2 : (a2 + b2).toNat = a2.toNat + b2.toNat := by bv_omega
  have h3 : (a3 + b3).toNat = a3.toNat + b3.toNat := by bv_omega
  have h4 : (a4 + b4).toNat = a4.toNat + b4.toNat := by bv_omega
  have hval :
      fe51Val (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) (a4 + b4) =
      fe51Val a0 a1 a2 a3 a4 + fe51Val b0 b1 b2 b3 b4 := by
    unfold fe51Val
    rw [h0, h1, h2, h3, h4]
    omega
  rw [hval]
  unfold fpAdd
  exact Nat.add_mod _ _ _


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

theorem add_slot (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 t0 t1 t2 t3 t4 : BitVec 64)
    (e0 : t0 = x0 + y0) (e1 : t1 = x1 + y1) (e2 : t2 = x2 + y2) (e3 : t3 = x3 + y3) (e4 : t4 = x4 + y4)
    {B1 B2 B : Nat}
    (hx : fe51LimbsBounded ([x0, x1, x2, x3, x4].flatMap unpack64) B1)
    (hy : fe51LimbsBounded ([y0, y1, y2, y3, y4].flatMap unpack64) B2)
    (hB : decide (B1 + B2 ≤ B ∧ B ≤ 2 ^ 64) = true := by decide)
    (hB1 : decide (B1 ≤ 2 ^ 54) = true := by decide)
    (hB2 : decide (B2 ≤ 2 ^ 54) = true := by decide) :
    fe51LimbsBounded ([t0, t1, t2, t3, t4].flatMap unpack64) B ∧
      fe51ValOfBytes ([t0, t1, t2, t3, t4].flatMap unpack64) % p25519 =
        fpAdd (fe51ValOfBytes ([x0, x1, x2, x3, x4].flatMap unpack64) % p25519)
          (fe51ValOfBytes ([y0, y1, y2, y3, y4].flatMap unpack64) % p25519) := by
  subst e0 e1 e2 e3 e4
  rw [lbw] at hx hy ⊢
  rw [valw, valw, valw]
  exact ⟨fe51Add_bounded _ _ _ _ _ _ _ _ _ _ B hx hy hB, fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ hx hy hB1 hB2⟩

theorem k19 : (((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64).setWidth 32).setWidth 64 = 19#64 := by
  decide

theorem sub_reduce_slot (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64)
    (s0 d0 m0 x4 d4 c4 r0 x1 d1 m1 r1 x2 d2 m2 r2 x3 d3 m3 r3 m4 r4 : BitVec 64)
    (es0 : s0 = a0 + 36028797018963664#64) (ed0 : d0 = s0 - b0)
    (em0 : m0 = d0 &&& 0x0007ffffffffffff#64)
    (ex4 : x4 = a4 - b4) (ed4 : d4 = x4 + 0x007ffffffffffff0#64) (ec4 : c4 = d4 >>> 51)
    (er0 : r0 = m0 + (c4.setWidth 32).setWidth 64 *
      (((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64).setWidth 32).setWidth 64)
    (ex1 : x1 = a1 - b1) (ed1 : d1 = x1 + 0x007ffffffffffff0#64) (em1 : m1 = d1 &&& 0x0007ffffffffffff#64)
    (er1 : r1 = m1 + d0 >>> 51)
    (ex2 : x2 = a2 - b2) (ed2 : d2 = x2 + 0x007ffffffffffff0#64) (em2 : m2 = d2 &&& 0x0007ffffffffffff#64)
    (er2 : r2 = m2 + d1 >>> 51)
    (ex3 : x3 = a3 - b3) (ed3 : d3 = x3 + 0x007ffffffffffff0#64) (em3 : m3 = d3 &&& 0x0007ffffffffffff#64)
    (er3 : r3 = m3 + d2 >>> 51)
    (em4 : m4 = d4 &&& 0x0007ffffffffffff#64) (er4 : r4 = m4 + d3 >>> 51)
    {B1 B2 : Nat}
    (ha : fe51LimbsBounded ([a0, a1, a2, a3, a4].flatMap unpack64) B1)
    (hb : fe51LimbsBounded ([b0, b1, b2, b3, b4].flatMap unpack64) B2)
    (hB1 : decide (B1 ≤ 2 ^ 54) = true := by decide)
    (hB2 : decide (B2 ≤ 2 ^ 54) = true := by decide) :
    fe51LimbsBounded ([r0, r1, r2, r3, r4].flatMap unpack64) (2 ^ 52) ∧
      fe51ValOfBytes ([r0, r1, r2, r3, r4].flatMap unpack64) % p25519 =
        fpSub (fe51ValOfBytes ([a0, a1, a2, a3, a4].flatMap unpack64) % p25519)
          (fe51ValOfBytes ([b0, b1, b2, b3, b4].flatMap unpack64) % p25519) := by
  rw [k19] at er0
  subst er0 er1 er2 er3 er4 em0 em1 em2 em3 em4 ec4 ed4 ed1 ed2 ed3 ex1 ex2 ex3 ex4 ed0 es0
  rw [lbw] at ha hb ⊢
  rw [valw, valw, valw, bv64_add_bias0_sub]
  have hR := fe51Reduce_bounded ((a0 - b0) + 36028797018963664#64) ((a1 - b1) + 0x007ffffffffffff0#64)
    ((a2 - b2) + 0x007ffffffffffff0#64) ((a3 - b3) + 0x007ffffffffffff0#64)
    ((a4 - b4) + 0x007ffffffffffff0#64)
  have hV := fe51Reduce_val_mod ((a0 - b0) + 36028797018963664#64) ((a1 - b1) + 0x007ffffffffffff0#64)
    ((a2 - b2) + 0x007ffffffffffff0#64) ((a3 - b3) + 0x007ffffffffffff0#64)
    ((a4 - b4) + 0x007ffffffffffff0#64)
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth] at hR hV
  refine ⟨hR, ?_⟩
  rw [hV]
  exact fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ ha hb hB1 hB2

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
theorem d12_s2 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
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
    {v : BitVec 5 → BitVec 128} {t144 t164 b_2 b_3 b_4 t76 t96 t100 a_3 a_4 c_0 c_1 c_2 c_3 c_4 d_0 d_1 d_2 d_3 d_4 aa_0 aa_1 aa_2 aa_3 aa_4 bb_0 bb_1 bb_2 bb_3 bb_4 e_0 e_1 e_2 e_3 e_4 da_0 da_1 da_2 da_3 da_4 cb_0 cb_1 cb_2 cb_3 cb_4 sum_0 sum_1 sum_2 sum_3 sum_4 diff_0 diff_1 diff_2 diff_3 diff_4 u3_0 u3_1 u3_2 u3_3 u3_4 tmp_0 tmp_1 tmp_2 tmp_3 tmp_4 a24e_0 a24e_1 a24e_2 a24e_3 a24e_4 u2_0 u2_1 u2_2 u2_3 u2_4 a24epbb_0 a24epbb_1 a24epbb_2 a24epbb_3 a24epbb_4 w2_0 w2_1 w2_2 w2_3 w2_4 w3_0 w3_1 w3_2 w3_3 w3_4 g1 t120 t68 t188 t172 t176 t180 t156 t168 t160 t72 t84 t80 t104 t112 t136 t108 t132 t124 t140 t148 t152 : BitVec 64}
    (hrun : sb.status = .Running) (kf : m0.KeepsFrozen m) (hvs : VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩) (hr0 : r 0#5 = t120) (hr1 : r 1#5 = t68) (hr2 : r 2#5 = u1) (hr8 : r 8#5 = t188) (hr9 : r 9#5 = t172) (hr10 : r 10#5 = t176) (hr11 : r 11#5 = t180) (hr12 : r 12#5 = t144) (hr13 : r 13#5 = t156) (hr14 : r 14#5 = t168) (hr15 : r 15#5 = t160) (hr16 : r 16#5 = t100) (hr17 : r 17#5 = p8) (hr18 : r 18#5 = p9) (hr19 : r 19#5 = Qb) (hr20 : r 20#5 = Pb) (hr21 : r 21#5 = c21) (hr22 : r 22#5 = 0x007ffffffffffff0#64) (hr23 : r 23#5 = c23) (hr24 : r 24#5 = 36028797018963664#64) (hr25 : r 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64)) (hr26 : r 26#5 = c26) (hr27 : r 27#5 = c27) (hr28 : r 28#5 = c28) (hr29 : r 29#5 = (S - 96#64)) (hr30 : r 30#5 = c30) (e68 : t68 = p9 + p4) (e72 : t72 = p4 - p9) (e76 : t76 = p5 + p0) (e80 : t80 = p0 + 36028797018963664#64) (e84 : t84 = t72 + 0x007ffffffffffff0#64) (e96 : t96 = p6 + p1) (e100 : t100 = p7 + p2) (e104 : t104 = p1 - p6) (e108 : t108 = t84 >>> 51) (e112 : t112 = t80 - p5) (e120 : t120 = p8 + p3) (e124 : t124 = t104 + 0x007ffffffffffff0#64) (e132 : t132 = p2 - p7) (e136 : t136 = t112 &&& 0x0007ffffffffffff#64) (e140 : t140 = p3 - p8) (e144 : t144 = t136 + (t108.setWidth 32).setWidth 64 * (((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64).setWidth 32).setWidth 64) (e148 : t148 = t132 + 0x007ffffffffffff0#64) (e152 : t152 = t124 &&& 0x0007ffffffffffff#64) (e156 : t156 = t140 + 0x007ffffffffffff0#64) (e160 : t160 = t148 &&& 0x0007ffffffffffff#64) (e164 : t164 = t152 + t112 >>> 51) (e168 : t168 = t156 &&& 0x0007ffffffffffff#64) (e172 : t172 = t160 + t124 >>> 51) (e176 : t176 = t84 &&& 0x0007ffffffffffff#64) (e180 : t180 = t168 + t148 >>> 51) (e188 : t188 = t176 + t156 >>> 51) (hs : m ⊨ ((S - 784#64) ↦₆₄* [t144, t164, b_2, b_3, b_4]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, a_3, a_4]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F)
    (hcont : ∀ (sb : State) (r : BitVec 5 → BitVec 64) (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128) (t316 t328 t324 t336 t348 t232 t228 t248 t256 t276 t344 t304 t332 t308 t280 : BitVec 64), (sb.status = .Running) → (m0.KeepsFrozen m) → (VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩) → (r 0#5 = (S - 824#64)) → (r 1#5 = ((((1#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64)) → (r 2#5 = u1) → (r 8#5 = (S - 664#64)) → (r 9#5 = t348) → (r 10#5 = t324) → (r 11#5 = t344) → (r 12#5 = t304) → (r 13#5 = t332) → (r 14#5 = t308) → (r 15#5 = t280) → (r 16#5 = q7) → (r 17#5 = t256) → (r 18#5 = q8) → (r 19#5 = Qb) → (r 20#5 = Pb) → (r 21#5 = c21) → (r 22#5 = 0x007ffffffffffff0#64) → (r 23#5 = c23) → (r 24#5 = 36028797018963664#64) → (r 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64)) → (r 26#5 = c26) → (r 27#5 = c27) → (r 28#5 = c28) → (r 29#5 = (S - 96#64)) → (r 30#5 = c30) → (fe51LimbsBounded ([t316, t328, t324, t336, t348].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([t232, t228, t248, t256, t276].flatMap unpack64) (2 ^ 54)) → (fe51LimbsBounded ([t144, t164, t172, t180, t188].flatMap unpack64) (2 ^ 52)) → (fe51LimbsBounded ([t76, t96, t100, t120, t68].flatMap unpack64) (2 ^ 54)) → (fe51LimbsBounded ([t316, t328, t324, t336, t348].flatMap unpack64) (2 ^ 52) ∧ fe51ValOfBytes ([t316, t328, t324, t336, t348].flatMap unpack64) % p25519 = fpSub (fe51ValOfBytes ([q0, q1, q2, q3, q4].flatMap unpack64) % p25519) (fe51ValOfBytes ([q5, q6, q7, q8, q9].flatMap unpack64) % p25519)) → (fe51LimbsBounded ([t232, t228, t248, t256, t276].flatMap unpack64) (2 ^ 54) ∧ fe51ValOfBytes ([t232, t228, t248, t256, t276].flatMap unpack64) % p25519 = fpAdd (fe51ValOfBytes ([q5, q6, q7, q8, q9].flatMap unpack64) % p25519) (fe51ValOfBytes ([q0, q1, q2, q3, q4].flatMap unpack64) % p25519)) → (fe51LimbsBounded ([t144, t164, t172, t180, t188].flatMap unpack64) (2 ^ 52) ∧ fe51ValOfBytes ([t144, t164, t172, t180, t188].flatMap unpack64) % p25519 = fpSub (fe51ValOfBytes ([p0, p1, p2, p3, p4].flatMap unpack64) % p25519) (fe51ValOfBytes ([p5, p6, p7, p8, p9].flatMap unpack64) % p25519)) → (fe51LimbsBounded ([t76, t96, t100, t120, t68].flatMap unpack64) (2 ^ 54) ∧ fe51ValOfBytes ([t76, t96, t100, t120, t68].flatMap unpack64) % p25519 = fpAdd (fe51ValOfBytes ([p5, p6, p7, p8, p9].flatMap unpack64) % p25519) (fe51ValOfBytes ([p0, p1, p2, p3, p4].flatMap unpack64) % p25519)) → (m ⊨ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F) → Reach (bprog mpl 12) (mkS sb (mpl.base 12 + BitVec.ofNat 64 364) r (S - 832#64) ps m v) Q) :
    Reach (bprog mpl 12) (mkS sb (mpl.base 12 + BitVec.ofNat 64 192) r (S - 832#64) ps m v) Q := by
  refine reach_reg (i := 0#5) hr0 ?_
  refine reach_reg (i := 1#5) hr1 ?_
  refine reach_reg (i := 2#5) hr2 ?_
  refine reach_reg (i := 8#5) hr8 ?_
  refine reach_reg (i := 9#5) hr9 ?_
  refine reach_reg (i := 10#5) hr10 ?_
  refine reach_reg (i := 11#5) hr11 ?_
  refine reach_reg (i := 12#5) hr12 ?_
  refine reach_reg (i := 13#5) hr13 ?_
  refine reach_reg (i := 14#5) hr14 ?_
  refine reach_reg (i := 15#5) hr15 ?_
  refine reach_reg (i := 16#5) hr16 ?_
  refine reach_reg (i := 17#5) hr17 ?_
  refine reach_reg (i := 18#5) hr18 ?_
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
  refine reach_reg (i := 30#5) hr30 ?_
  rw [pick24] at hs
  refine x_ldp_r (d1 := 13#5) (d2 := 16#5) (b := 19#5) (x := Qb) (a := Qb) (i := 6) (by decide) (by decide) (by decide) hrun (c12_192 hP hCL 12 kf) (pc4 _ 192 196 rfl) rfl rfl (wf1 hs 6 (by exact (by decide : 6 < 10)) : m.read64 _ = q6 ∧ _) rfl (wf1 hs 7 (by exact (by decide : 7 < 10)) : m.read64 _ = q7 ∧ _) ?_
  rw [pick3] at hs
  refine x_stp_sp (t1 := 0#5) (t2 := 1#5) (v1 := t120) (v2 := t68) (i := 3) (by decide) (by decide) (aligned_sub hal 832 (by decide) (by decide)) hrun (c12_196 hP hCL 12 kf) (pc4 _ 196 200 rfl) (aSS S 832 32 824 (8 * 3) (by decide)) hs (by exact (by decide : 4 < 5)) rfl rfl (fun m28 hs29 kf30 => ?_)
  replace hs29 : m28 ⊨ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, b_2, b_3, b_4]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs29
  replace kf30 := kf.trans kf30
  clear hs kf
  rw [pick3] at hs29
  refine x_stp_sp (t1 := 9#5) (t2 := 11#5) (v1 := t172) (v2 := t180) (i := 2) (by decide) (by decide) (aligned_sub hal 832 (by decide) (by decide)) hrun (c12_200 hP hCL 12 kf30) (pc4 _ 200 204 rfl) (aSS S 832 64 784 (8 * 2) (by decide)) hs29 (by exact (by decide : 3 < 5)) rfl rfl (fun m31 hs32 kf33 => ?_)
  replace hs32 : m31 ⊨ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, b_4]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs32
  replace kf33 := kf30.trans kf33
  clear hs29 kf30
  rw [pick3] at hs32
  refine x_ldp_r (d1 := 9#5) (d2 := 10#5) (b := 19#5) (x := Qb) (a := Qb) (i := 0) (by decide) (by decide) (by decide) hrun (c12_204 hP hCL 12 kf33) (pc4 _ 204 208 rfl) rfl rfl (wf1 hs32 0 (by exact (by decide : 0 < 10)) : m31.read64 _ = q0 ∧ _) rfl (wf1 hs32 1 (by exact (by decide : 1 < 10)) : m31.read64 _ = q1 ∧ _) ?_
  refine x_ldp_r (d1 := 11#5) (d2 := 12#5) (b := 19#5) (x := Qb) (a := Qb) (i := 4) (by decide) (by decide) (by decide) hrun (c12_208 hP hCL 12 kf33) (pc4 _ 208 212 rfl) rfl rfl (wf1 hs32 4 (by exact (by decide : 4 < 10)) : m31.read64 _ = q4 ∧ _) rfl (wf1 hs32 5 (by exact (by decide : 5 < 10)) : m31.read64 _ = q5 ∧ _) ?_
  rw [pick2] at hs32
  refine x_str_sp (t := 8#5) (v1 := t188) (i := 4) (by decide) (aligned_sub hal 832 (by decide) (by decide)) hrun (c12_212 hP hCL 12 kf33) (pc4 _ 212 216 rfl) (aSS S 832 80 784 (8 * 4) (by decide)) hs32 (by exact (by decide : 4 < 5)) rfl (fun m34 hs35 kf36 => ?_)
  replace hs35 : m34 ⊨ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs35
  replace kf36 := kf33.trans kf36
  clear hs32 kf33
  rw [pick2] at hs35
  refine x_ldp_r (d1 := 8#5) (d2 := 14#5) (b := 19#5) (x := Qb) (a := Qb) (i := 2) (by decide) (by decide) (by decide) hrun (c12_216 hP hCL 12 kf36) (pc4 _ 216 220 rfl) rfl rfl (wf1 hs35 2 (by exact (by decide : 2 < 10)) : m34.read64 _ = q2 ∧ _) rfl (wf1 hs35 3 (by exact (by decide : 3 < 10)) : m34.read64 _ = q3 ∧ _) ?_
  refine x_movz32 (d := 1#5) (by decide) hrun (c12_220 hP hCL 12 kf36) (pc4 _ 220 224 rfl) ?_
  refine x_ldp_r (d1 := 18#5) (d2 := 0#5) (b := 19#5) (x := Qb) (a := Qb) (i := 8) (by decide) (by decide) (by decide) hrun (c12_224 hP hCL 12 kf36) (pc4 _ 224 228 rfl) rfl rfl (wf1 hs35 8 (by exact (by decide : 8 < 10)) : m34.read64 _ = q8 ∧ _) rfl (wf1 hs35 9 (by exact (by decide : 9 < 10)) : m34.read64 _ = q9 ∧ _) ?_
  refine x_add (d := 17#5) (a := 13#5) (b := 10#5) (x := q6) (y := q1) (by decide) (by decide) (by decide) hrun (c12_228 hP hCL 12 kf36) (pc4 _ 228 232 rfl) rfl rfl (fun t228 e228 => ?_)
  refine x_add (d := 15#5) (a := 12#5) (b := 9#5) (x := q5) (y := q0) (by decide) (by decide) (by decide) hrun (c12_232 hP hCL 12 kf36) (pc4 _ 232 236 rfl) rfl rfl (fun t232 e232 => ?_)
  refine x_add (d := 9#5) (a := 9#5) (b := 24#5) (x := q0) (y := 36028797018963664#64) (by decide) (by decide) (by decide) hrun (c12_236 hP hCL 12 kf36) (pc4 _ 236 240 rfl) rfl rfl (fun t236 e236 => ?_)
  refine x_sub (d := 10#5) (a := 10#5) (b := 13#5) (x := q1) (y := q6) (by decide) (by decide) (by decide) hrun (c12_240 hP hCL 12 kf36) (pc4 _ 240 244 rfl) rfl rfl (fun t240 e240 => ?_)
  rw [pick7] at hs35
  refine x_stp_sp (t1 := 15#5) (t2 := 17#5) (v1 := t232) (v2 := t228) (i := 0) (by decide) (by decide) (aligned_sub hal 832 (by decide) (by decide)) hrun (c12_244 hP hCL 12 kf36) (pc4 _ 244 248 rfl) (aSS S 832 88 744 (8 * 0) (by decide)) hs35 (by exact (by decide : 1 < 5)) rfl rfl (fun m37 hs38 kf39 => ?_)
  replace hs38 : m37 ⊨ ((S - 744#64) ↦₆₄* [t232, t228, c_2, c_3, c_4]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs38
  replace kf39 := kf36.trans kf39
  clear hs35 kf36
  refine x_add (d := 15#5) (a := 16#5) (b := 8#5) (x := q7) (y := q2) (by decide) (by decide) (by decide) hrun (c12_248 hP hCL 12 kf39) (pc4 _ 248 252 rfl) rfl rfl (fun t248 e248 => ?_)
  refine x_sub (d := 9#5) (a := 9#5) (b := 12#5) (x := t236) (y := q5) (by decide) (by decide) (by decide) hrun (c12_252 hP hCL 12 kf39) (pc4 _ 252 256 rfl) rfl rfl (fun t252 e252 => ?_)
  refine x_add (d := 17#5) (a := 18#5) (b := 14#5) (x := q8) (y := q3) (by decide) (by decide) (by decide) hrun (c12_256 hP hCL 12 kf39) (pc4 _ 256 260 rfl) rfl rfl (fun t256 e256 => ?_)
  refine x_add (d := 10#5) (a := 10#5) (b := 22#5) (x := t240) (y := 0x007ffffffffffff0#64) (by decide) (by decide) (by decide) hrun (c12_260 hP hCL 12 kf39) (pc4 _ 260 264 rfl) rfl rfl (fun t260 e260 => ?_)
  refine x_sub (d := 8#5) (a := 8#5) (b := 16#5) (x := q2) (y := q7) (by decide) (by decide) (by decide) hrun (c12_264 hP hCL 12 kf39) (pc4 _ 264 268 rfl) rfl rfl (fun t264 e264 => ?_)
  refine x_stp_sp (t1 := 15#5) (t2 := 17#5) (v1 := t248) (v2 := t256) (i := 2) (by decide) (by decide) (aligned_sub hal 832 (by decide) (by decide)) hrun (c12_268 hP hCL 12 kf39) (pc4 _ 268 272 rfl) (aSS S 832 104 744 (8 * 2) (by decide)) hs38 (by exact (by decide : 3 < 5)) rfl rfl (fun m40 hs41 kf42 => ?_)
  replace hs41 : m40 ⊨ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, c_4]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs41
  replace kf42 := kf39.trans kf42
  clear hs38 kf39
  refine x_sub (d := 15#5) (a := 11#5) (b := 0#5) (x := q4) (y := q9) (by decide) (by decide) (by decide) hrun (c12_272 hP hCL 12 kf42) (pc4 _ 272 276 rfl) rfl rfl (fun t272 e272 => ?_)
  refine x_add (d := 11#5) (a := 0#5) (b := 11#5) (x := q9) (y := q4) (by decide) (by decide) (by decide) hrun (c12_276 hP hCL 12 kf42) (pc4 _ 276 280 rfl) rfl rfl (fun t276 e276 => ?_)
  refine x_add (d := 15#5) (a := 15#5) (b := 22#5) (x := t272) (y := 0x007ffffffffffff0#64) (by decide) (by decide) (by decide) hrun (c12_280 hP hCL 12 kf42) (pc4 _ 280 284 rfl) rfl rfl (fun t280 e280 => ?_)
  refine x_str_sp (t := 11#5) (v1 := t276) (i := 4) (by decide) (aligned_sub hal 832 (by decide) (by decide)) hrun (c12_284 hP hCL 12 kf42) (pc4 _ 284 288 rfl) (aSS S 832 120 744 (8 * 4) (by decide)) hs41 (by exact (by decide : 4 < 5)) rfl (fun m43 hs44 kf45 => ?_)
  replace hs44 : m43 ⊨ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs44
  replace kf45 := kf42.trans kf45
  clear hs41 kf42
  refine x_andi (d := 11#5) (a := 9#5) (x := t252) (by decide) (by decide) hrun (c12_288 hP hCL 12 kf45) (pc4 _ 288 292 rfl) rfl (fun t288 e288 => ?_)
  refine x_lsr51 (d := 13#5) (a := 15#5) (x := t280) (by decide) (by decide) hrun (c12_292 hP hCL 12 kf45) (pc4 _ 292 296 rfl) rfl (fun t292 e292 => ?_)
  refine x_sub (d := 12#5) (a := 14#5) (b := 18#5) (x := q3) (y := q8) (by decide) (by decide) (by decide) hrun (c12_296 hP hCL 12 kf45) (pc4 _ 296 300 rfl) rfl rfl (fun t296 e296 => ?_)
  refine x_add (d := 8#5) (a := 8#5) (b := 22#5) (x := t264) (y := 0x007ffffffffffff0#64) (by decide) (by decide) (by decide) hrun (c12_300 hP hCL 12 kf45) (pc4 _ 300 304 rfl) rfl rfl (fun t300 e300 => ?_)
  refine x_add (d := 12#5) (a := 12#5) (b := 22#5) (x := t296) (y := 0x007ffffffffffff0#64) (by decide) (by decide) (by decide) hrun (c12_304 hP hCL 12 kf45) (pc4 _ 304 308 rfl) rfl rfl (fun t304 e304 => ?_)
  refine x_andi (d := 14#5) (a := 8#5) (x := t300) (by decide) (by decide) hrun (c12_308 hP hCL 12 kf45) (pc4 _ 308 312 rfl) rfl (fun t308 e308 => ?_)
  refine x_addi_sp2 (d := 0#5) (by decide) hrun (c12_312 hP hCL 12 kf45) (pc4 _ 312 316 rfl) (aSk S 832 824 _ (by decide)) ?_
  refine x_umaddl (d := 11#5) (a := 13#5) (b := 25#5) (c := 11#5) (x := t292) (y := ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64)) (z := t288) (by decide) (by decide) (by decide) (by decide) hrun (c12_316 hP hCL 12 kf45) (pc4 _ 316 320 rfl) rfl rfl rfl (fun t316 e316 => ?_)
  refine x_andi (d := 13#5) (a := 10#5) (x := t260) (by decide) (by decide) hrun (c12_320 hP hCL 12 kf45) (pc4 _ 320 324 rfl) rfl (fun t320 e320 => ?_)
  refine x_addlsr (d := 10#5) (a := 14#5) (b := 10#5) (x := t308) (y := t260) (by decide) (by decide) (by decide) hrun (c12_324 hP hCL 12 kf45) (pc4 _ 324 328 rfl) rfl rfl (fun t324 e324 => ?_)
  refine x_addlsr (d := 9#5) (a := 13#5) (b := 9#5) (x := t320) (y := t252) (by decide) (by decide) (by decide) hrun (c12_328 hP hCL 12 kf45) (pc4 _ 328 332 rfl) rfl rfl (fun t328 e328 => ?_)
  refine x_andi (d := 13#5) (a := 12#5) (x := t304) (by decide) (by decide) hrun (c12_332 hP hCL 12 kf45) (pc4 _ 332 336 rfl) rfl (fun t332 e332 => ?_)
  refine x_addlsr (d := 8#5) (a := 13#5) (b := 8#5) (x := t332) (y := t300) (by decide) (by decide) (by decide) hrun (c12_336 hP hCL 12 kf45) (pc4 _ 336 340 rfl) rfl rfl (fun t336 e336 => ?_)
  rw [pick8] at hs44
  refine x_stp_sp (t1 := 11#5) (t2 := 9#5) (v1 := t316) (v2 := t328) (i := 0) (by decide) (by decide) (aligned_sub hal 832 (by decide) (by decide)) hrun (c12_340 hP hCL 12 kf45) (pc4 _ 340 344 rfl) (aSS S 832 128 704 (8 * 0) (by decide)) hs44 (by exact (by decide : 1 < 5)) rfl rfl (fun m46 hs47 kf48 => ?_)
  replace hs47 : m46 ⊨ ((S - 704#64) ↦₆₄* [t316, t328, d_2, d_3, d_4]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs47
  replace kf48 := kf45.trans kf48
  clear hs44 kf45
  refine x_andi (d := 11#5) (a := 15#5) (x := t280) (by decide) (by decide) hrun (c12_344 hP hCL 12 kf48) (pc4 _ 344 348 rfl) rfl (fun t344 e344 => ?_)
  refine x_addlsr (d := 9#5) (a := 11#5) (b := 12#5) (x := t344) (y := t304) (by decide) (by decide) (by decide) hrun (c12_348 hP hCL 12 kf48) (pc4 _ 348 352 rfl) rfl rfl (fun t348 e348 => ?_)
  refine x_stp_sp (t1 := 10#5) (t2 := 8#5) (v1 := t324) (v2 := t336) (i := 2) (by decide) (by decide) (aligned_sub hal 832 (by decide) (by decide)) hrun (c12_352 hP hCL 12 kf48) (pc4 _ 352 356 rfl) (aSS S 832 144 704 (8 * 2) (by decide)) hs47 (by exact (by decide : 3 < 5)) rfl rfl (fun m49 hs50 kf51 => ?_)
  replace hs50 : m49 ⊨ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, d_4]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs50
  replace kf51 := kf48.trans kf51
  clear hs47 kf48
  refine x_addi_sp2 (d := 8#5) (by decide) hrun (c12_356 hP hCL 12 kf51) (pc4 _ 356 360 rfl) (aSk S 832 664 _ (by decide)) ?_
  refine x_str_sp (t := 9#5) (v1 := t348) (i := 4) (by decide) (aligned_sub hal 832 (by decide) (by decide)) hrun (c12_360 hP hCL 12 kf51) (pc4 _ 360 364 rfl) (aSS S 832 160 704 (8 * 4) (by decide)) hs50 (by exact (by decide : 4 < 5)) rfl (fun m52 hs53 kf54 => ?_)
  replace hs53 : m52 ⊨ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs53
  replace kf54 := kf51.trans kf54
  clear hs50 kf51
  have f_D := sub_reduce_slot q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 t236 t252 t288 t272 t280 t292 t316 t240 t260 t320 t328 t264 t300 t308 t324 t296 t304 t332 t336 t344 t348 e236 e252 e288 e272 e280 e292 e316 e240 e260 e320 e328 e264 e300 e308 e324 e296 e304 e332 e336 e344 e348 hQU hQW
  have f_C := add_slot q5 q6 q7 q8 q9 q0 q1 q2 q3 q4 t232 t228 t248 t256 t276 e232 e228 e248 e256 e276 (B := 2 ^ 54) hQW hQU
  have f_B := sub_reduce_slot p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 t80 t112 t136 t72 t84 t108 t144 t104 t124 t152 t164 t132 t148 t160 t172 t140 t156 t168 t180 t176 t188 e80 e112 e136 e72 e84 e108 e144 e104 e124 e152 e164 e132 e148 e160 e172 e140 e156 e168 e180 e176 e188 hPU hPW
  have f_A := add_slot p5 p6 p7 p8 p9 p0 p1 p2 p3 p4 t76 t96 t100 t120 t68 e76 e96 e100 e120 e68 (B := 2 ^ 54) hPW hPU
  exact hcont _ _ _ _ _ t316 t328 t324 t336 t348 t232 t228 t248 t256 t276 t344 t304 t332 t308 t280 hrun kf54 hvs rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl f_D.1 f_C.1 f_B.1 f_A.1 f_D f_C f_B f_A hs53


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
theorem differentialAddAndDouble_192_364_dev {mpl : Arm64.Obj.MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S Pb Qb u1 : BitVec 64} {F : Arm64.SepProp}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 uw0 uw1 uw2 uw3 uw4 : BitVec 64}
    {c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 : BitVec 64}
    {t144 t164 b_2 b_3 b_4 t76 t96 t100 a_3 a_4 c_0 c_1 c_2 c_3 c_4 d_0 d_1 d_2 d_3 d_4 aa_0 aa_1 aa_2 aa_3 aa_4 bb_0 bb_1 bb_2 bb_3 bb_4 e_0 e_1 e_2 e_3 e_4 da_0 da_1 da_2 da_3 da_4 cb_0 cb_1 cb_2 cb_3 cb_4 sum_0 sum_1 sum_2 sum_3 sum_4 diff_0 diff_1 diff_2 diff_3 diff_4 u3_0 u3_1 u3_2 u3_3 u3_4 tmp_0 tmp_1 tmp_2 tmp_3 tmp_4 a24e_0 a24e_1 a24e_2 a24e_3 a24e_4 u2_0 u2_1 u2_2 u2_3 u2_4 a24epbb_0 a24epbb_1 a24epbb_2 a24epbb_3 a24epbb_4 w2_0 w2_1 w2_2 w2_3 w2_4 w3_0 w3_1 w3_2 w3_3 w3_4 g1 t120 t68 t188 t172 t176 t180 t156 t168 t160 t72 t84 t80 t104 t112 t136 t108 t132 t124 t140 t148 t152 : BitVec 64}
    (hal : (S &&& 15#64 == 0#64) = true)
    (hPU : p0.toNat < 9007199254740992 ∧ p1.toNat < 9007199254740992 ∧ p2.toNat < 9007199254740992 ∧ p3.toNat < 9007199254740992 ∧ p4.toNat < 9007199254740992)
    (hPW : p5.toNat < 9007199254740992 ∧ p6.toNat < 9007199254740992 ∧ p7.toNat < 9007199254740992 ∧ p8.toNat < 9007199254740992 ∧ p9.toNat < 9007199254740992)
    (hQU : q0.toNat < 9007199254740992 ∧ q1.toNat < 9007199254740992 ∧ q2.toNat < 9007199254740992 ∧ q3.toNat < 9007199254740992 ∧ q4.toNat < 9007199254740992)
    (hQW : q5.toNat < 9007199254740992 ∧ q6.toNat < 9007199254740992 ∧ q7.toNat < 9007199254740992 ∧ q8.toNat < 9007199254740992 ∧ q9.toNat < 9007199254740992)
    (hU1 : uw0.toNat < 18014398509481984 ∧ uw1.toNat < 18014398509481984 ∧ uw2.toNat < 18014398509481984 ∧ uw3.toNat < 18014398509481984 ∧ uw4.toNat < 18014398509481984)
    (hrun : s.status = Arm64.ExecStatus.Running) (hpc : s.pc = mpl.base 12 + BitVec.ofNat 64 192) (hsp : s.sp = S - 832#64)
    (hr0 : s.regs.regs 0#5 = t120)
    (hr1 : s.regs.regs 1#5 = t68)
    (hr2 : s.regs.regs 2#5 = u1)
    (hr8 : s.regs.regs 8#5 = t188)
    (hr9 : s.regs.regs 9#5 = t172)
    (hr10 : s.regs.regs 10#5 = t176)
    (hr11 : s.regs.regs 11#5 = t180)
    (hr12 : s.regs.regs 12#5 = t144)
    (hr13 : s.regs.regs 13#5 = t156)
    (hr14 : s.regs.regs 14#5 = t168)
    (hr15 : s.regs.regs 15#5 = t160)
    (hr16 : s.regs.regs 16#5 = t100)
    (hr17 : s.regs.regs 17#5 = p8)
    (hr18 : s.regs.regs 18#5 = p9)
    (hr19 : s.regs.regs 19#5 = Qb)
    (hr20 : s.regs.regs 20#5 = Pb)
    (hr21 : s.regs.regs 21#5 = c21)
    (hr22 : s.regs.regs 22#5 = 0x007ffffffffffff0#64)
    (hr23 : s.regs.regs 23#5 = c23)
    (hr24 : s.regs.regs 24#5 = 36028797018963664#64)
    (hr25 : s.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64))
    (hr26 : s.regs.regs 26#5 = c26)
    (hr27 : s.regs.regs 27#5 = c27)
    (hr28 : s.regs.regs 28#5 = c28)
    (hr29 : s.regs.regs 29#5 = (S - 96#64))
    (hr30 : s.regs.regs 30#5 = c30)
    (e68 : t68 = p9 + p4)
    (e72 : t72 = p4 - p9)
    (e76 : t76 = p5 + p0)
    (e80 : t80 = p0 + 36028797018963664#64)
    (e84 : t84 = t72 + 0x007ffffffffffff0#64)
    (e96 : t96 = p6 + p1)
    (e100 : t100 = p7 + p2)
    (e104 : t104 = p1 - p6)
    (e108 : t108 = t84 >>> 51)
    (e112 : t112 = t80 - p5)
    (e120 : t120 = p8 + p3)
    (e124 : t124 = t104 + 0x007ffffffffffff0#64)
    (e132 : t132 = p2 - p7)
    (e136 : t136 = t112 &&& 0x0007ffffffffffff#64)
    (e140 : t140 = p3 - p8)
    (e144 : t144 = t136 + (t108.setWidth 32).setWidth 64 * (((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64).setWidth 32).setWidth 64)
    (e148 : t148 = t132 + 0x007ffffffffffff0#64)
    (e152 : t152 = t124 &&& 0x0007ffffffffffff#64)
    (e156 : t156 = t140 + 0x007ffffffffffff0#64)
    (e160 : t160 = t148 &&& 0x0007ffffffffffff#64)
    (e164 : t164 = t152 + t112 >>> 51)
    (e168 : t168 = t156 &&& 0x0007ffffffffffff#64)
    (e172 : t172 = t160 + t124 >>> 51)
    (e176 : t176 = t84 &&& 0x0007ffffffffffff#64)
    (e180 : t180 = t168 + t148 >>> 51)
    (e188 : t188 = t176 + t156 >>> 51)
    (hs : s.mem ⊨ ((S - 784#64) ↦₆₄* [t144, t164, b_2, b_3, b_4]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, a_3, a_4]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F) :
    ∃ sf, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 12) s sf ∧
      sf.status = Arm64.ExecStatus.Running ∧
      sf.pc = mpl.base 12 + BitVec.ofNat 64 364 ∧
      sf.sp = S - 832#64 ∧
      Arm64.VRegFile.calleeSaved sf.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ t316 t328 t324 t336 t348 t232 t228 t248 t256 t276 t344 t304 t332 t308 t280 : BitVec 64,
        sf.regs.regs 0#5 = (S - 824#64) ∧
        sf.regs.regs 1#5 = ((((1#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) ∧
        sf.regs.regs 2#5 = u1 ∧
        sf.regs.regs 8#5 = (S - 664#64) ∧
        sf.regs.regs 9#5 = t348 ∧
        sf.regs.regs 10#5 = t324 ∧
        sf.regs.regs 11#5 = t344 ∧
        sf.regs.regs 12#5 = t304 ∧
        sf.regs.regs 13#5 = t332 ∧
        sf.regs.regs 14#5 = t308 ∧
        sf.regs.regs 15#5 = t280 ∧
        sf.regs.regs 16#5 = q7 ∧
        sf.regs.regs 17#5 = t256 ∧
        sf.regs.regs 18#5 = q8 ∧
        sf.regs.regs 19#5 = Qb ∧
        sf.regs.regs 20#5 = Pb ∧
        sf.regs.regs 21#5 = c21 ∧
        sf.regs.regs 22#5 = 0x007ffffffffffff0#64 ∧
        sf.regs.regs 23#5 = c23 ∧
        sf.regs.regs 24#5 = 36028797018963664#64 ∧
        sf.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) ∧
        sf.regs.regs 26#5 = c26 ∧
        sf.regs.regs 27#5 = c27 ∧
        sf.regs.regs 28#5 = c28 ∧
        sf.regs.regs 29#5 = (S - 96#64) ∧
        sf.regs.regs 30#5 = c30 ∧
        ((t316.toNat < 4503599627370496 ∧ t328.toNat < 4503599627370496 ∧ t324.toNat < 4503599627370496 ∧ t336.toNat < 4503599627370496 ∧ t348.toNat < 4503599627370496)) ∧
        ((t232.toNat < 18014398509481984 ∧ t228.toNat < 18014398509481984 ∧ t248.toNat < 18014398509481984 ∧ t256.toNat < 18014398509481984 ∧ t276.toNat < 18014398509481984)) ∧
        ((t144.toNat < 4503599627370496 ∧ t164.toNat < 4503599627370496 ∧ t172.toNat < 4503599627370496 ∧ t180.toNat < 4503599627370496 ∧ t188.toNat < 4503599627370496)) ∧
        ((t76.toNat < 18014398509481984 ∧ t96.toNat < 18014398509481984 ∧ t100.toNat < 18014398509481984 ∧ t120.toNat < 18014398509481984 ∧ t68.toNat < 18014398509481984)) ∧
        ((t316.toNat < 4503599627370496 ∧ t328.toNat < 4503599627370496 ∧ t324.toNat < 4503599627370496 ∧ t336.toNat < 4503599627370496 ∧ t348.toNat < 4503599627370496) ∧ (fe51Val t316 t328 t324 t336 t348) % p25519 = fpSub ((fe51Val q0 q1 q2 q3 q4) % p25519) ((fe51Val q5 q6 q7 q8 q9) % p25519)) ∧
        ((t232.toNat < 18014398509481984 ∧ t228.toNat < 18014398509481984 ∧ t248.toNat < 18014398509481984 ∧ t256.toNat < 18014398509481984 ∧ t276.toNat < 18014398509481984) ∧ (fe51Val t232 t228 t248 t256 t276) % p25519 = fpAdd ((fe51Val q5 q6 q7 q8 q9) % p25519) ((fe51Val q0 q1 q2 q3 q4) % p25519)) ∧
        ((t144.toNat < 4503599627370496 ∧ t164.toNat < 4503599627370496 ∧ t172.toNat < 4503599627370496 ∧ t180.toNat < 4503599627370496 ∧ t188.toNat < 4503599627370496) ∧ (fe51Val t144 t164 t172 t180 t188) % p25519 = fpSub ((fe51Val p0 p1 p2 p3 p4) % p25519) ((fe51Val p5 p6 p7 p8 p9) % p25519)) ∧
        ((t76.toNat < 18014398509481984 ∧ t96.toNat < 18014398509481984 ∧ t100.toNat < 18014398509481984 ∧ t120.toNat < 18014398509481984 ∧ t68.toNat < 18014398509481984) ∧ (fe51Val t76 t96 t100 t120 t68) % p25519 = fpAdd ((fe51Val p5 p6 p7 p8 p9) % p25519) ((fe51Val p0 p1 p2 p3 p4) % p25519)) ∧
        sf.mem ⊨ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F := by
  have e0 : mkS s (mpl.base 12 + BitVec.ofNat 64 192) s.regs.regs (S - 832#64) s.pstate s.mem s.vregs.regs = s := by
    rw [← hpc, ← hsp]; rfl
  rw [← e0]
  show Reach (bprog mpl 12) _ _
  refine d12_s2 (S := S) (vo := s.vregs.regs) (c19 := c19) (c20 := c20) (c21 := c21) (c22 := c22) (c23 := c23) (c24 := c24) (c25 := c25) (c26 := c26) (c27 := c27) (c28 := c28) (c29 := c29) (c30 := c30) hP hCL hal (by simpa only [lbw, valw, Nat.reducePow] using hPU) (by simpa only [lbw, valw, Nat.reducePow] using hPW) (by simpa only [lbw, valw, Nat.reducePow] using hQU) (by simpa only [lbw, valw, Nat.reducePow] using hQW) (by simpa only [lbw, valw, Nat.reducePow] using hU1) hrun (Memory.KeepsFrozen.refl _) rfl hr0 hr1 hr2 hr8 hr9 hr10 hr11 hr12 hr13 hr14 hr15 hr16 hr17 hr18 hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26 hr27 hr28 hr29 hr30 e68 e72 e76 e80 e84 e96 e100 e104 e108 e112 e120 e124 e132 e136 e140 e144 e148 e152 e156 e160 e164 e168 e172 e176 e180 e188 hs ?_
  intro sb r ps m v t316 t328 t324 t336 t348 t232 t228 t248 t256 t276 t344 t304 t332 t308 t280 hrun kf hvs hr0 hr1 hr2 hr8 hr9 hr10 hr11 hr12 hr13 hr14 hr15 hr16 hr17 hr18 hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26 hr27 hr28 hr29 hr30 bd_D bd_C bd_B bd_A f_D f_C f_B f_A hs
  apply Reach.done
  exact ⟨hrun, rfl, rfl, hvs, t316, t328, t324, t336, t348, t232, t228, t248, t256, t276, t344, t304, t332, t308, t280, hr0, hr1, hr2, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr20, hr21, hr22, hr23, hr24, hr25, hr26, hr27, hr28, hr29, hr30, (by simpa only [lbw, valw, Nat.reducePow] using bd_D), (by simpa only [lbw, valw, Nat.reducePow] using bd_C), (by simpa only [lbw, valw, Nat.reducePow] using bd_B), (by simpa only [lbw, valw, Nat.reducePow] using bd_A), (by simpa only [lbw, valw, Nat.reducePow] using f_D), (by simpa only [lbw, valw, Nat.reducePow] using f_C), (by simpa only [lbw, valw, Nat.reducePow] using f_B), (by simpa only [lbw, valw, Nat.reducePow] using f_A), hs⟩

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
    {t144 t164 b_2 b_3 b_4 t76 t96 t100 a_3 a_4 c_0 c_1 c_2 c_3 c_4 d_0 d_1 d_2 d_3 d_4 aa_0 aa_1 aa_2 aa_3 aa_4 bb_0 bb_1 bb_2 bb_3 bb_4 e_0 e_1 e_2 e_3 e_4 da_0 da_1 da_2 da_3 da_4 cb_0 cb_1 cb_2 cb_3 cb_4 sum_0 sum_1 sum_2 sum_3 sum_4 diff_0 diff_1 diff_2 diff_3 diff_4 u3_0 u3_1 u3_2 u3_3 u3_4 tmp_0 tmp_1 tmp_2 tmp_3 tmp_4 a24e_0 a24e_1 a24e_2 a24e_3 a24e_4 u2_0 u2_1 u2_2 u2_3 u2_4 a24epbb_0 a24epbb_1 a24epbb_2 a24epbb_3 a24epbb_4 w2_0 w2_1 w2_2 w2_3 w2_4 w3_0 w3_1 w3_2 w3_3 w3_4 g1 t120 t68 t188 t172 t176 t180 t156 t168 t160 t72 t84 t80 t104 t112 t136 t108 t132 t124 t140 t148 t152 : BitVec 64}
    (hal : (S &&& 15#64 == 0#64) = true)
    (hPU : p0.toNat < 9007199254740992 ∧ p1.toNat < 9007199254740992 ∧ p2.toNat < 9007199254740992 ∧ p3.toNat < 9007199254740992 ∧ p4.toNat < 9007199254740992)
    (hPW : p5.toNat < 9007199254740992 ∧ p6.toNat < 9007199254740992 ∧ p7.toNat < 9007199254740992 ∧ p8.toNat < 9007199254740992 ∧ p9.toNat < 9007199254740992)
    (hQU : q0.toNat < 9007199254740992 ∧ q1.toNat < 9007199254740992 ∧ q2.toNat < 9007199254740992 ∧ q3.toNat < 9007199254740992 ∧ q4.toNat < 9007199254740992)
    (hQW : q5.toNat < 9007199254740992 ∧ q6.toNat < 9007199254740992 ∧ q7.toNat < 9007199254740992 ∧ q8.toNat < 9007199254740992 ∧ q9.toNat < 9007199254740992)
    (hU1 : uw0.toNat < 18014398509481984 ∧ uw1.toNat < 18014398509481984 ∧ uw2.toNat < 18014398509481984 ∧ uw3.toNat < 18014398509481984 ∧ uw4.toNat < 18014398509481984)
    (hrun : s.status = Arm64.ExecStatus.Running) (hpc : s.pc = mpl.base 12 + BitVec.ofNat 64 192) (hsp : s.sp = S - 832#64)
    (hr0 : s.regs.regs 0#5 = t120)
    (hr1 : s.regs.regs 1#5 = t68)
    (hr2 : s.regs.regs 2#5 = u1)
    (hr8 : s.regs.regs 8#5 = t188)
    (hr9 : s.regs.regs 9#5 = t172)
    (hr10 : s.regs.regs 10#5 = t176)
    (hr11 : s.regs.regs 11#5 = t180)
    (hr12 : s.regs.regs 12#5 = t144)
    (hr13 : s.regs.regs 13#5 = t156)
    (hr14 : s.regs.regs 14#5 = t168)
    (hr15 : s.regs.regs 15#5 = t160)
    (hr16 : s.regs.regs 16#5 = t100)
    (hr17 : s.regs.regs 17#5 = p8)
    (hr18 : s.regs.regs 18#5 = p9)
    (hr19 : s.regs.regs 19#5 = Qb)
    (hr20 : s.regs.regs 20#5 = Pb)
    (hr21 : s.regs.regs 21#5 = c21)
    (hr22 : s.regs.regs 22#5 = 0x007ffffffffffff0#64)
    (hr23 : s.regs.regs 23#5 = c23)
    (hr24 : s.regs.regs 24#5 = 36028797018963664#64)
    (hr25 : s.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64))
    (hr26 : s.regs.regs 26#5 = c26)
    (hr27 : s.regs.regs 27#5 = c27)
    (hr28 : s.regs.regs 28#5 = c28)
    (hr29 : s.regs.regs 29#5 = (S - 96#64))
    (hr30 : s.regs.regs 30#5 = c30)
    (e68 : t68 = p9 + p4)
    (e72 : t72 = p4 - p9)
    (e76 : t76 = p5 + p0)
    (e80 : t80 = p0 + 36028797018963664#64)
    (e84 : t84 = t72 + 0x007ffffffffffff0#64)
    (e96 : t96 = p6 + p1)
    (e100 : t100 = p7 + p2)
    (e104 : t104 = p1 - p6)
    (e108 : t108 = t84 >>> 51)
    (e112 : t112 = t80 - p5)
    (e120 : t120 = p8 + p3)
    (e124 : t124 = t104 + 0x007ffffffffffff0#64)
    (e132 : t132 = p2 - p7)
    (e136 : t136 = t112 &&& 0x0007ffffffffffff#64)
    (e140 : t140 = p3 - p8)
    (e144 : t144 = t136 + (t108.setWidth 32).setWidth 64 * (((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64).setWidth 32).setWidth 64)
    (e148 : t148 = t132 + 0x007ffffffffffff0#64)
    (e152 : t152 = t124 &&& 0x0007ffffffffffff#64)
    (e156 : t156 = t140 + 0x007ffffffffffff0#64)
    (e160 : t160 = t148 &&& 0x0007ffffffffffff#64)
    (e164 : t164 = t152 + t112 >>> 51)
    (e168 : t168 = t156 &&& 0x0007ffffffffffff#64)
    (e172 : t172 = t160 + t124 >>> 51)
    (e176 : t176 = t84 &&& 0x0007ffffffffffff#64)
    (e180 : t180 = t168 + t148 >>> 51)
    (e188 : t188 = t176 + t156 >>> 51)
    (hs : s.mem ⊨ ((S - 784#64) ↦₆₄* [t144, t164, b_2, b_3, b_4]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, a_3, a_4]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F) :
    ∃ sf, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 12) s sf ∧
      sf.status = Arm64.ExecStatus.Running ∧
      sf.pc = mpl.base 12 + BitVec.ofNat 64 364 ∧
      sf.sp = S - 832#64 ∧
      Arm64.VRegFile.calleeSaved sf.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ t316 t328 t324 t336 t348 t232 t228 t248 t256 t276 t344 t304 t332 t308 t280 : BitVec 64,
        sf.regs.regs 0#5 = (S - 824#64) ∧
        sf.regs.regs 1#5 = ((((1#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) ∧
        sf.regs.regs 2#5 = u1 ∧
        sf.regs.regs 8#5 = (S - 664#64) ∧
        sf.regs.regs 9#5 = t348 ∧
        sf.regs.regs 10#5 = t324 ∧
        sf.regs.regs 11#5 = t344 ∧
        sf.regs.regs 12#5 = t304 ∧
        sf.regs.regs 13#5 = t332 ∧
        sf.regs.regs 14#5 = t308 ∧
        sf.regs.regs 15#5 = t280 ∧
        sf.regs.regs 16#5 = q7 ∧
        sf.regs.regs 17#5 = t256 ∧
        sf.regs.regs 18#5 = q8 ∧
        sf.regs.regs 19#5 = Qb ∧
        sf.regs.regs 20#5 = Pb ∧
        sf.regs.regs 21#5 = c21 ∧
        sf.regs.regs 22#5 = 0x007ffffffffffff0#64 ∧
        sf.regs.regs 23#5 = c23 ∧
        sf.regs.regs 24#5 = 36028797018963664#64 ∧
        sf.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) ∧
        sf.regs.regs 26#5 = c26 ∧
        sf.regs.regs 27#5 = c27 ∧
        sf.regs.regs 28#5 = c28 ∧
        sf.regs.regs 29#5 = (S - 96#64) ∧
        sf.regs.regs 30#5 = c30 ∧
        ((t316.toNat < 4503599627370496 ∧ t328.toNat < 4503599627370496 ∧ t324.toNat < 4503599627370496 ∧ t336.toNat < 4503599627370496 ∧ t348.toNat < 4503599627370496)) ∧
        ((t232.toNat < 18014398509481984 ∧ t228.toNat < 18014398509481984 ∧ t248.toNat < 18014398509481984 ∧ t256.toNat < 18014398509481984 ∧ t276.toNat < 18014398509481984)) ∧
        ((t144.toNat < 4503599627370496 ∧ t164.toNat < 4503599627370496 ∧ t172.toNat < 4503599627370496 ∧ t180.toNat < 4503599627370496 ∧ t188.toNat < 4503599627370496)) ∧
        ((t76.toNat < 18014398509481984 ∧ t96.toNat < 18014398509481984 ∧ t100.toNat < 18014398509481984 ∧ t120.toNat < 18014398509481984 ∧ t68.toNat < 18014398509481984)) ∧
        ((t316.toNat < 4503599627370496 ∧ t328.toNat < 4503599627370496 ∧ t324.toNat < 4503599627370496 ∧ t336.toNat < 4503599627370496 ∧ t348.toNat < 4503599627370496) ∧ (fe51Val t316 t328 t324 t336 t348) % p25519 = fpSub ((fe51Val q0 q1 q2 q3 q4) % p25519) ((fe51Val q5 q6 q7 q8 q9) % p25519)) ∧
        ((t232.toNat < 18014398509481984 ∧ t228.toNat < 18014398509481984 ∧ t248.toNat < 18014398509481984 ∧ t256.toNat < 18014398509481984 ∧ t276.toNat < 18014398509481984) ∧ (fe51Val t232 t228 t248 t256 t276) % p25519 = fpAdd ((fe51Val q5 q6 q7 q8 q9) % p25519) ((fe51Val q0 q1 q2 q3 q4) % p25519)) ∧
        ((t144.toNat < 4503599627370496 ∧ t164.toNat < 4503599627370496 ∧ t172.toNat < 4503599627370496 ∧ t180.toNat < 4503599627370496 ∧ t188.toNat < 4503599627370496) ∧ (fe51Val t144 t164 t172 t180 t188) % p25519 = fpSub ((fe51Val p0 p1 p2 p3 p4) % p25519) ((fe51Val p5 p6 p7 p8 p9) % p25519)) ∧
        ((t76.toNat < 18014398509481984 ∧ t96.toNat < 18014398509481984 ∧ t100.toNat < 18014398509481984 ∧ t120.toNat < 18014398509481984 ∧ t68.toNat < 18014398509481984) ∧ (fe51Val t76 t96 t100 t120 t68) % p25519 = fpAdd ((fe51Val p5 p6 p7 p8 p9) % p25519) ((fe51Val p0 p1 p2 p3 p4) % p25519)) ∧
        sf.mem ⊨ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F := by
  exact X25519Dalek.differentialAddAndDouble_192_364_dev hP hCL hal hPU hPW hQU hQW hU1 hrun hpc hsp hr0 hr1 hr2 hr8 hr9 hr10 hr11 hr12 hr13 hr14 hr15 hr16 hr17 hr18 hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26 hr27 hr28 hr29 hr30 e68 e72 e76 e80 e84 e96 e100 e104 e108 e112 e120 e124 e132 e136 e140 e144 e148 e152 e156 e160 e164 e168 e172 e176 e180 e188 hs

end
