-- Prove2me | solution 1 for X25519Dalek.differentialAddAndDouble_0_192
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T19:44:07.182802+00:00
-- url     : https://prove2.me/submissions/cc799544-9c97-4ac3-91d0-3f08dcc6865b

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

theorem y_orri {d : BitVec 5} (hd : d ≠ 31#5) {k : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalImm .W64 .ORR (.gpr d) .xzr k))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d k) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, BitVec.zero_or]
  exact h

theorem y_mov {d b : BitVec 5} (hd : d ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr b) .LSL 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r b)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, hb, BitVec.zero_or]
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

theorem x_orri {d : BitVec 5} {k : BitVec 64} (hd : d ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalImm .W64 .ORR (.gpr d) .xzr k))
    (hpc : pc + 4#64 = pc')
    (h : Reach p (mkS s0 pc' (upd r d k) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; exact y_orri hd hrun hf h

theorem x_mov {d b : BitVec 5} {y : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr b) .LSL 0))
    (hpc : pc + 4#64 = pc') (ey : r b = y)
    (h : Reach p (mkS s0 pc' (upd r d y) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ey; exact y_mov hd hb hrun hf h

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

theorem x_movn64 {d : BitVec 5} {k : BitVec 16} {c : BitVec 64} (hd : d ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.moveWide .W64 .MOVN (.gpr d) k 0))
    (hpc : pc + 4#64 = pc') (hc : ~~~BitVec.zeroExtend 64 k = c)
    (h : Reach p (mkS s0 pc' (upd r d c) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc hc
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd]
  exact h

theorem x_movk48 {d : BitVec 5} {k : BitVec 16} {x c : BitVec 64} (hd : d ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.moveWide .W64 .MOVK (.gpr d) k 48))
    (hpc : pc + 4#64 = pc') (ex : r d = x)
    (hc : (x &&& ~~~18446462598732840960#64 ||| BitVec.zeroExtend 64 k <<< 48) = c)
    (h : Reach p (mkS s0 pc' (upd r d c) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc hc ex
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd]
  exact h

end

section
variable {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

end

section
variable {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem y_stp_pre {t1 t2 : BitVec 5} {off A A8 : BitVec 64} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5)
    (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (hA8 : A + 8#64 = A8)
    (c1 : m.canWrite A 8 = true) (c2 : m.canWrite A8 8 = true) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.PreIndex .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) r A ps ((m.write64 A (r t1)).write64 A8 (r t2)) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ht1, ht2, hal, hA, hA8, c1, c2]
  exact h

theorem y_subsp {k : BitVec 12} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUB .sp .sp k false))
    (h : Reach p (mkS s0 (pc + 4#64) r (sp - k.setWidth 64) ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', BitVec.truncate_eq_setWidth]
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

theorem c12_0 : (bprog mpl j).fetchMem m (mpl.base 12) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.PreIndex (Reg.sp) 0xffffffffffffffa0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 0) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.PreIndex (Reg.sp) 0xffffffffffffffa0#64))) (by decide) rfl (by decide +kernel) hk
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

theorem c12_4 : (bprog mpl j).fetchMem m (mpl.base 12 + 4#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1c#5) (Reg.gpr 0x1b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000010#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 4) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x1c#5) (Reg.gpr 0x1b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000010#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_8 : (bprog mpl j).fetchMem m (mpl.base 12 + 8#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 8) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_12 : (bprog mpl j).fetchMem m (mpl.base 12 + 12#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 12) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_16 : (bprog mpl j).fetchMem m (mpl.base 12 + 16#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 16) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_20 : (bprog mpl j).fetchMem m (mpl.base 12 + 20#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 20) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_24 : (bprog mpl j).fetchMem m (mpl.base 12 + 24#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1d#5) (Reg.sp) 0x000#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 24) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1d#5) (Reg.sp) 0x000#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_28 : (bprog mpl j).fetchMem m (mpl.base 12 + 28#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.sp) (Reg.sp) 0x2e0#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 28) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.sp) (Reg.sp) 0x2e0#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_32 : (bprog mpl j).fetchMem m (mpl.base 12 + 32#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0a#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x00#5) 0x0000000000000020#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 32) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0a#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x00#5) 0x0000000000000020#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_36 : (bprog mpl j).fetchMem m (mpl.base 12 + 36#64) =
    some (Instr.moveWide (RegWidth.W64) (MoveWideOp.MOVN) (Reg.gpr 0x18#5) 0x012f#16 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 36) (inst := (Instr.moveWide (RegWidth.W64) (MoveWideOp.MOVN) (Reg.gpr 0x18#5) 0x012f#16 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_40 : (bprog mpl j).fetchMem m (mpl.base 12 + 40#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x11#5) (Reg.gpr 0x12#5) (AddrMode.Offset (Reg.gpr 0x00#5) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 40) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x11#5) (Reg.gpr 0x12#5) (AddrMode.Offset (Reg.gpr 0x00#5) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_44 : (bprog mpl j).fetchMem m (mpl.base 12 + 44#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x13#5) (Reg.xzr) (Reg.gpr 0x01#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 44) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x13#5) (Reg.xzr) (Reg.gpr 0x01#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_48 : (bprog mpl j).fetchMem m (mpl.base 12 + 48#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x00#5) 0x0000000000000000#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 48) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x00#5) 0x0000000000000000#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_52 : (bprog mpl j).fetchMem m (mpl.base 12 + 52#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x16#5) (Reg.xzr) 0x007ffffffffffff0#64) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 52) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x16#5) (Reg.xzr) 0x007ffffffffffff0#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_56 : (bprog mpl j).fetchMem m (mpl.base 12 + 56#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0c#5) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x00#5) 0x0000000000000010#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 56) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0c#5) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.gpr 0x00#5) 0x0000000000000010#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_60 : (bprog mpl j).fetchMem m (mpl.base 12 + 60#64) =
    some (Instr.moveWide (RegWidth.W64) (MoveWideOp.MOVK) (Reg.gpr 0x18#5) 0x007f#16 48) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 60) (inst := (Instr.moveWide (RegWidth.W64) (MoveWideOp.MOVK) (Reg.gpr 0x18#5) 0x007f#16 48)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_64 : (bprog mpl j).fetchMem m (mpl.base 12 + 64#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0e#5) (Reg.gpr 0x0f#5) (AddrMode.Offset (Reg.gpr 0x00#5) 0x0000000000000030#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 64) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0e#5) (Reg.gpr 0x0f#5) (AddrMode.Offset (Reg.gpr 0x00#5) 0x0000000000000030#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_68 : (bprog mpl j).fetchMem m (mpl.base 12 + 68#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.gpr 0x12#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 68) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.gpr 0x12#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_72 : (bprog mpl j).fetchMem m (mpl.base 12 + 72#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 72) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_76 : (bprog mpl j).fetchMem m (mpl.base 12 + 76#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x10#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 76) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x10#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_80 : (bprog mpl j).fetchMem m (mpl.base 12 + 80#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x18#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 80) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x18#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_84 : (bprog mpl j).fetchMem m (mpl.base 12 + 84#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 84) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_88 : (bprog mpl j).fetchMem m (mpl.base 12 + 88#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x14#5) (Reg.xzr) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 88) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x14#5) (Reg.xzr) (Reg.gpr 0x00#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_92 : (bprog mpl j).fetchMem m (mpl.base 12 + 92#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x02#5) (Reg.gpr 0x10#5) (AddrMode.Offset (Reg.sp) 0x0000000000000000#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 92) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x02#5) (Reg.gpr 0x10#5) (AddrMode.Offset (Reg.sp) 0x0000000000000000#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_96 : (bprog mpl j).fetchMem m (mpl.base 12 + 96#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 96) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_100 : (bprog mpl j).fetchMem m (mpl.base 12 + 100#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x10#5) (Reg.gpr 0x0f#5) (Reg.gpr 0x0c#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 100) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x10#5) (Reg.gpr 0x0f#5) (Reg.gpr 0x0c#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_104 : (bprog mpl j).fetchMem m (mpl.base 12 + 104#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) (Reg.gpr 0x0e#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 104) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) (Reg.gpr 0x0e#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_108 : (bprog mpl j).fetchMem m (mpl.base 12 + 108#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0e#5) (Reg.gpr 0x0a#5) 51 63) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 108) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0e#5) (Reg.gpr 0x0a#5) 51 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_112 : (bprog mpl j).fetchMem m (mpl.base 12 + 112#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x0b#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 112) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x0b#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_116 : (bprog mpl j).fetchMem m (mpl.base 12 + 116#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x00#5) (Reg.gpr 0x10#5) (AddrMode.Offset (Reg.sp) 0x0000000000000010#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 116) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x00#5) (Reg.gpr 0x10#5) (AddrMode.Offset (Reg.sp) 0x0000000000000010#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_120 : (bprog mpl j).fetchMem m (mpl.base 12 + 120#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.gpr 0x11#5) (Reg.gpr 0x0d#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 120) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.gpr 0x11#5) (Reg.gpr 0x0d#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_124 : (bprog mpl j).fetchMem m (mpl.base 12 + 124#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 124) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_128 : (bprog mpl j).fetchMem m (mpl.base 12 + 128#64) =
    some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x19#5) 0x0013#16 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 128) (inst := (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x19#5) 0x0013#16 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_132 : (bprog mpl j).fetchMem m (mpl.base 12 + 132#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0b#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x0f#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 132) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0b#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x0f#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_136 : (bprog mpl j).fetchMem m (mpl.base 12 + 136#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0c#5) (Reg.gpr 0x08#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 136) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0c#5) (Reg.gpr 0x08#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_140 : (bprog mpl j).fetchMem m (mpl.base 12 + 140#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0d#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x11#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 140) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0d#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x11#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_144 : (bprog mpl j).fetchMem m (mpl.base 12 + 144#64) =
    some (Instr.dataProc3 (RegWidth.W64) (DataProc3Op.UMADDL) (Reg.gpr 0x0c#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x19#5) (Reg.gpr 0x0c#5)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 144) (inst := (Instr.dataProc3 (RegWidth.W64) (DataProc3Op.UMADDL) (Reg.gpr 0x0c#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x19#5) (Reg.gpr 0x0c#5))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_148 : (bprog mpl j).fetchMem m (mpl.base 12 + 148#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 148) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_152 : (bprog mpl j).fetchMem m (mpl.base 12 + 152#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0e#5) (Reg.gpr 0x09#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 152) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0e#5) (Reg.gpr 0x09#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_156 : (bprog mpl j).fetchMem m (mpl.base 12 + 156#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0d#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 156) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0d#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_160 : (bprog mpl j).fetchMem m (mpl.base 12 + 160#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0f#5) (Reg.gpr 0x0b#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 160) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0f#5) (Reg.gpr 0x0b#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_164 : (bprog mpl j).fetchMem m (mpl.base 12 + 164#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 164) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_168 : (bprog mpl j).fetchMem m (mpl.base 12 + 168#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0e#5) (Reg.gpr 0x0d#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 168) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0e#5) (Reg.gpr 0x0d#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_172 : (bprog mpl j).fetchMem m (mpl.base 12 + 172#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x0f#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 172) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.gpr 0x0f#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_176 : (bprog mpl j).fetchMem m (mpl.base 12 + 176#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 176) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_180 : (bprog mpl j).fetchMem m (mpl.base 12 + 180#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x0b#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 180) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x0b#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_184 : (bprog mpl j).fetchMem m (mpl.base 12 + 184#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x0c#5) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64)) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 184) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x0c#5) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c12_188 : (bprog mpl j).fetchMem m (mpl.base 12 + 188#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x0d#5) (ShiftType.LSR) 51) := by
  have := fetch_at' hP hCL (by decide) j blk12 len12 (off := 188) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x0d#5) (ShiftType.LSR) 51)) (by decide) rfl (by decide +kernel) hk
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

theorem upd_eq_self {α : Type} {r : BitVec 5 → α} {i : BitVec 5} {x : α} (h : r i = x) :
    upd r i x = r := by
  funext k; simp only [upd]; split_ifs with hk
  · subst hk; exact h.symm
  · rfl

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

theorem aSmk (S : BitVec 64) (a c : Nat) (k : BitVec 12)
    (h : BitVec.ofNat 64 a + k.setWidth 64 = BitVec.ofNat 64 c) :
    S - BitVec.ofNat 64 a - k.setWidth 64 = S - BitVec.ofNat 64 c := by
  rw [← h]; try abel

theorem aSb (S : BitVec 64) (a b c : Nat) (h : BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 c) :
    S - BitVec.ofNat 64 a + BitVec.ofNat 64 b = S - BitVec.ofNat 64 c := by
  rw [← h]; try abel

theorem aS0 (S : BitVec 64) (a : Nat) : S - BitVec.ofNat 64 a = S - BitVec.ofNat 64 a + BitVec.ofNat 64 (8 * 0) := by
  simp

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

theorem x_subsp {k : BitVec 12} {sp' : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUB .sp .sp k false))
    (hpc : pc + 4#64 = pc') (hx : sp - k.setWidth 64 = sp')
    (h : Reach p (mkS s0 pc' r sp' ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc hx; exact y_subsp hrun hf h

/-- `stp t1, t2, [sp, #off]!` into words `i`, `i + 1` of the word list at position 1. -/
theorem x_stp_pre {t1 t2 : BitVec 5} {off a sp' v1 v2 : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    {i : Nat} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.PreIndex .sp off)))
    (hpc : pc + 4#64 = pc') (hsp : sp + off = sp') (hA : sp' = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hl : i + 1 < ws.length) (e1 : r t1 = v1) (e2 : r t2 = v2)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (ws.set i v1).set (i + 1) v2) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp' ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc e1 e2
  obtain ⟨-, -, c1⟩ := sat_words_read hs i (by omega)
  obtain ⟨-, -, c2⟩ := sat_words_read hs (i + 1) hl
  have c1' : m.canWrite sp' 8 = true := by rw [hA]; exact c1
  have c2' : m.canWrite (sp' + 8#64) 8 = true := by rw [hA, w8]; exact c2
  refine y_stp_pre ht1 ht2 hal hsp rfl c1' c2' hrun hf ?_
  exact Reach.wr64x2 i hs hA (by rw [hA, w8]) hl h


/-- `stp` whose two words fall in the first two pieces: word `i` of `a` and word `j` of `b`. -/
theorem x_stp_sp_x {t1 t2 : BitVec 5} {off a b v1 v2 : BitVec 64} {ws vs : List (BitVec 64)} {F : SepProp}
    {i j : Nat} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * i))
    (hab : a + BitVec.ofNat 64 (8 * (i + 1)) = b + BitVec.ofNat 64 (8 * j))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ (b ↦₆₄* vs) ∗ F) (hi : i < ws.length) (hj : j < vs.length)
    (e1 : r t1 = v1) (e2 : r t2 = v2)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* ws.set i v1) ∗ (b ↦₆₄* vs.set j v2) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc e1 e2
  obtain ⟨-, -, c1⟩ := sat_words_read hs i hi
  have hs2 : m ⊨ (b ↦₆₄* vs) ∗ (a ↦₆₄* ws) ∗ F := by rwa [sepConj_left_comm] at hs
  obtain ⟨-, -, c2⟩ := sat_words_read hs2 j hj
  have c2' : m.canWrite (a + BitVec.ofNat 64 (8 * i) + 8#64) 8 = true := by rw [w8, hab]; exact c2
  refine y_stp_sp ht1 ht2 hal hA rfl c1 c2' hrun hf ?_
  obtain ⟨g1, k1⟩ := sat_words_write hs i hi (r t1)
  have g1' := g1
  rw [sepConj_left_comm] at g1'
  obtain ⟨g2, k2⟩ := sat_words_write g1' j hj (r t2)
  rw [w8, hab]
  exact h _ (by rwa [sepConj_left_comm] at g2) (k1.trans k2)

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
theorem pick4 (A1 A2 A3 A4 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ R) = (A4 ∗ A1 ∗ A2 ∗ A3 ∗ R) := by ac_rfl
theorem pick5 (A1 A2 A3 A4 A5 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ R) = (A5 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ R) := by ac_rfl
theorem pick23 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ R) = (A23 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ R) := by ac_rfl

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
theorem d12_s1 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {S Pb Qb u1 : BitVec 64} {F : SepProp} {Q : State → Prop}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 uw0 uw1 uw2 uw3 uw4 : BitVec 64}
    {vo : BitVec 5 → BitVec 128} {c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 : BitVec 64}
    (hal : (S &&& 15#64 == 0#64) = true)
    (hPU : fe51LimbsBounded ([p0, p1, p2, p3, p4].flatMap unpack64) (2 ^ 53))
    (hPW : fe51LimbsBounded ([p5, p6, p7, p8, p9].flatMap unpack64) (2 ^ 53))
    (hQU : fe51LimbsBounded ([q0, q1, q2, q3, q4].flatMap unpack64) (2 ^ 53))
    (hQW : fe51LimbsBounded ([q5, q6, q7, q8, q9].flatMap unpack64) (2 ^ 53))
    (hU1 : fe51LimbsBounded ([uw0, uw1, uw2, uw3, uw4].flatMap unpack64) (2 ^ 54))
    {sb : State} (hrun : sb.status = .Running) {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} (kf : m0.KeepsFrozen m) (hvs : VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩)
    (hc19 : r 19#5 = c19) (hc20 : r 20#5 = c20) (hc21 : r 21#5 = c21) (hc22 : r 22#5 = c22) (hc23 : r 23#5 = c23)
    (hc24 : r 24#5 = c24) (hc25 : r 25#5 = c25) (hc26 : r 26#5 = c26) (hc27 : r 27#5 = c27) (hc28 : r 28#5 = c28)
    (hc29 : r 29#5 = c29) (hc30 : r 30#5 = c30) {sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 g0 g1 a_0 a_1 a_2 a_3 a_4 b_0 b_1 b_2 b_3 b_4 c_0 c_1 c_2 c_3 c_4 d_0 d_1 d_2 d_3 d_4 aa_0 aa_1 aa_2 aa_3 aa_4 bb_0 bb_1 bb_2 bb_3 bb_4 e_0 e_1 e_2 e_3 e_4 da_0 da_1 da_2 da_3 da_4 cb_0 cb_1 cb_2 cb_3 cb_4 sum_0 sum_1 sum_2 sum_3 sum_4 diff_0 diff_1 diff_2 diff_3 diff_4 u3_0 u3_1 u3_2 u3_3 u3_4 tmp_0 tmp_1 tmp_2 tmp_3 tmp_4 a24e_0 a24e_1 a24e_2 a24e_3 a24e_4 u2_0 u2_1 u2_2 u2_3 u2_4 a24epbb_0 a24epbb_1 a24epbb_2 a24epbb_3 a24epbb_4 w2_0 w2_1 w2_2 w2_3 w2_4 w3_0 w3_1 w3_2 w3_3 w3_4 : BitVec 64}
    (hs : m ⊨ ((S - 96#64) ↦₆₄* [sv0, sv1, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11]) ∗ ((S - 832#64) ↦₆₄* [g0]) ∗ ((S - 824#64) ↦₆₄* [a_0, a_1, a_2, a_3, a_4]) ∗ ((S - 784#64) ↦₆₄* [b_0, b_1, b_2, b_3, b_4]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F)
    (hcont : ∀ (sb : State) (r : BitVec 5 → BitVec 64) (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128) (t144 t164 t76 t96 t100 t120 t68 t188 t172 t176 t180 t156 t168 t160 t72 t84 t80 t104 t112 t136 t108 t132 t124 t140 t148 t152 : BitVec 64), (sb.status = .Running) → (m0.KeepsFrozen m) → (VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩) → (r 0#5 = t120) → (r 1#5 = t68) → (r 2#5 = u1) → (r 8#5 = t188) → (r 9#5 = t172) → (r 10#5 = t176) → (r 11#5 = t180) → (r 12#5 = t144) → (r 13#5 = t156) → (r 14#5 = t168) → (r 15#5 = t160) → (r 16#5 = t100) → (r 17#5 = p8) → (r 18#5 = p9) → (r 19#5 = Qb) → (r 20#5 = Pb) → (r 21#5 = c21) → (r 22#5 = 0x007ffffffffffff0#64) → (r 23#5 = c23) → (r 24#5 = 36028797018963664#64) → (r 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64)) → (r 26#5 = c26) → (r 27#5 = c27) → (r 28#5 = c28) → (r 29#5 = (S - 96#64)) → (r 30#5 = c30) → (t68 = p9 + p4) → (t72 = p4 - p9) → (t76 = p5 + p0) → (t80 = p0 + 36028797018963664#64) → (t84 = t72 + 0x007ffffffffffff0#64) → (t96 = p6 + p1) → (t100 = p7 + p2) → (t104 = p1 - p6) → (t108 = t84 >>> 51) → (t112 = t80 - p5) → (t120 = p8 + p3) → (t124 = t104 + 0x007ffffffffffff0#64) → (t132 = p2 - p7) → (t136 = t112 &&& 0x0007ffffffffffff#64) → (t140 = p3 - p8) → (t144 = t136 + (t108.setWidth 32).setWidth 64 * (((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64).setWidth 32).setWidth 64) → (t148 = t132 + 0x007ffffffffffff0#64) → (t152 = t124 &&& 0x0007ffffffffffff#64) → (t156 = t140 + 0x007ffffffffffff0#64) → (t160 = t148 &&& 0x0007ffffffffffff#64) → (t164 = t152 + t112 >>> 51) → (t168 = t156 &&& 0x0007ffffffffffff#64) → (t172 = t160 + t124 >>> 51) → (t176 = t84 &&& 0x0007ffffffffffff#64) → (t180 = t168 + t148 >>> 51) → (t188 = t176 + t156 >>> 51) → (m ⊨ ((S - 784#64) ↦₆₄* [t144, t164, b_2, b_3, b_4]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, a_3, a_4]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F) → Reach (bprog mpl 12) (mkS sb (mpl.base 12 + BitVec.ofNat 64 192) r (S - 832#64) ps m v) Q) :
    Reach (bprog mpl 12) (mkS sb (mpl.base 12) (upd (upd (upd r 0#5 Pb) 1#5 Qb) 2#5 u1) (S - 0#64) ps m v) Q := by
  refine reach_reg (i := 19#5) hc19 ?_
  refine reach_reg (i := 20#5) hc20 ?_
  refine reach_reg (i := 21#5) hc21 ?_
  refine reach_reg (i := 22#5) hc22 ?_
  refine reach_reg (i := 23#5) hc23 ?_
  refine reach_reg (i := 24#5) hc24 ?_
  refine reach_reg (i := 25#5) hc25 ?_
  refine reach_reg (i := 26#5) hc26 ?_
  refine reach_reg (i := 27#5) hc27 ?_
  refine reach_reg (i := 28#5) hc28 ?_
  refine reach_reg (i := 29#5) hc29 ?_
  refine reach_reg (i := 30#5) hc30 ?_
  refine x_stp_pre (t1 := 29#5) (t2 := 30#5) (i := 0) (by decide) (by decide) (aligned_sub hal 0 (by decide) (by decide)) hrun (c12_0 hP hCL 12 kf) rfl (aSb S 0 18446744073709551520 96 (by decide)) (aS0 S 96) hs (by exact (by decide : 1 < 12)) rfl rfl (fun m1 hs2 kf3 => ?_)
  replace hs2 : m1 ⊨ ((S - 96#64) ↦₆₄* [c29, c30, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11]) ∗ ((S - 832#64) ↦₆₄* [g0]) ∗ ((S - 824#64) ↦₆₄* [a_0, a_1, a_2, a_3, a_4]) ∗ ((S - 784#64) ↦₆₄* [b_0, b_1, b_2, b_3, b_4]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs2
  replace kf3 := kf.trans kf3
  clear hs kf
  refine x_stp_sp (t1 := 28#5) (t2 := 27#5) (v1 := c28) (v2 := c27) (i := 2) (by decide) (by decide) (aligned_sub hal 96 (by decide) (by decide)) hrun (c12_4 hP hCL 12 kf3) (pc4 _ 4 8 rfl) (aSS S 96 16 96 (8 * 2) (by decide)) hs2 (by exact (by decide : 3 < 12)) rfl rfl (fun m4 hs5 kf6 => ?_)
  replace hs5 : m4 ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11]) ∗ ((S - 832#64) ↦₆₄* [g0]) ∗ ((S - 824#64) ↦₆₄* [a_0, a_1, a_2, a_3, a_4]) ∗ ((S - 784#64) ↦₆₄* [b_0, b_1, b_2, b_3, b_4]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs5
  replace kf6 := kf3.trans kf6
  clear hs2 kf3
  refine x_stp_sp (t1 := 26#5) (t2 := 25#5) (v1 := c26) (v2 := c25) (i := 4) (by decide) (by decide) (aligned_sub hal 96 (by decide) (by decide)) hrun (c12_8 hP hCL 12 kf6) (pc4 _ 8 12 rfl) (aSS S 96 32 96 (8 * 4) (by decide)) hs5 (by exact (by decide : 5 < 12)) rfl rfl (fun m7 hs8 kf9 => ?_)
  replace hs8 : m7 ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, sv6, sv7, sv8, sv9, sv10, sv11]) ∗ ((S - 832#64) ↦₆₄* [g0]) ∗ ((S - 824#64) ↦₆₄* [a_0, a_1, a_2, a_3, a_4]) ∗ ((S - 784#64) ↦₆₄* [b_0, b_1, b_2, b_3, b_4]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs8
  replace kf9 := kf6.trans kf9
  clear hs5 kf6
  refine x_stp_sp (t1 := 24#5) (t2 := 23#5) (v1 := c24) (v2 := c23) (i := 6) (by decide) (by decide) (aligned_sub hal 96 (by decide) (by decide)) hrun (c12_12 hP hCL 12 kf9) (pc4 _ 12 16 rfl) (aSS S 96 48 96 (8 * 6) (by decide)) hs8 (by exact (by decide : 7 < 12)) rfl rfl (fun m10 hs11 kf12 => ?_)
  replace hs11 : m10 ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, sv8, sv9, sv10, sv11]) ∗ ((S - 832#64) ↦₆₄* [g0]) ∗ ((S - 824#64) ↦₆₄* [a_0, a_1, a_2, a_3, a_4]) ∗ ((S - 784#64) ↦₆₄* [b_0, b_1, b_2, b_3, b_4]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs11
  replace kf12 := kf9.trans kf12
  clear hs8 kf9
  refine x_stp_sp (t1 := 22#5) (t2 := 21#5) (v1 := c22) (v2 := c21) (i := 8) (by decide) (by decide) (aligned_sub hal 96 (by decide) (by decide)) hrun (c12_16 hP hCL 12 kf12) (pc4 _ 16 20 rfl) (aSS S 96 64 96 (8 * 8) (by decide)) hs11 (by exact (by decide : 9 < 12)) rfl rfl (fun m13 hs14 kf15 => ?_)
  replace hs14 : m13 ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, sv10, sv11]) ∗ ((S - 832#64) ↦₆₄* [g0]) ∗ ((S - 824#64) ↦₆₄* [a_0, a_1, a_2, a_3, a_4]) ∗ ((S - 784#64) ↦₆₄* [b_0, b_1, b_2, b_3, b_4]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs14
  replace kf15 := kf12.trans kf15
  clear hs11 kf12
  refine x_stp_sp (t1 := 20#5) (t2 := 19#5) (v1 := c20) (v2 := c19) (i := 10) (by decide) (by decide) (aligned_sub hal 96 (by decide) (by decide)) hrun (c12_20 hP hCL 12 kf15) (pc4 _ 20 24 rfl) (aSS S 96 80 96 (8 * 10) (by decide)) hs14 (by exact (by decide : 11 < 12)) rfl rfl (fun m16 hs17 kf18 => ?_)
  replace hs17 : m16 ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 832#64) ↦₆₄* [g0]) ∗ ((S - 824#64) ↦₆₄* [a_0, a_1, a_2, a_3, a_4]) ∗ ((S - 784#64) ↦₆₄* [b_0, b_1, b_2, b_3, b_4]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs17
  replace kf18 := kf15.trans kf18
  clear hs14 kf15
  refine x_addi_sp2 (d := 29#5) (by decide) hrun (c12_24 hP hCL 12 kf18) (pc4 _ 24 28 rfl) (aSk S 96 96 _ (by decide)) ?_
  refine x_subsp hrun (c12_28 hP hCL 12 kf18) (pc4 _ 28 32 rfl) (aSmk S 96 832 _ (by decide)) ?_
  rw [pick23] at hs17
  refine x_ldp_r (d1 := 10#5) (d2 := 11#5) (b := 0#5) (x := Pb) (a := Pb) (i := 4) (by decide) (by decide) (by decide) hrun (c12_32 hP hCL 12 kf18) (pc4 _ 32 36 rfl) rfl rfl (wf1 hs17 4 (by exact (by decide : 4 < 10)) : m16.read64 _ = p4 ∧ _) rfl (wf1 hs17 5 (by exact (by decide : 5 < 10)) : m16.read64 _ = p5 ∧ _) ?_
  refine x_movn64 (d := 24#5) (c := 18446744073709551312#64) (by decide) hrun (c12_36 hP hCL 12 kf18) (pc4 _ 36 40 rfl) (by decide) ?_
  refine x_ldp_r (d1 := 17#5) (d2 := 18#5) (b := 0#5) (x := Pb) (a := Pb) (i := 8) (by decide) (by decide) (by decide) hrun (c12_40 hP hCL 12 kf18) (pc4 _ 40 44 rfl) rfl rfl (wf1 hs17 8 (by exact (by decide : 8 < 10)) : m16.read64 _ = p8 ∧ _) rfl (wf1 hs17 9 (by exact (by decide : 9 < 10)) : m16.read64 _ = p9 ∧ _) ?_
  refine x_mov (d := 19#5) (b := 1#5) (y := Qb) (by decide) (by decide) hrun (c12_44 hP hCL 12 kf18) (pc4 _ 44 48 rfl) rfl ?_
  refine x_ldp_r (d1 := 8#5) (d2 := 9#5) (b := 0#5) (x := Pb) (a := Pb) (i := 0) (by decide) (by decide) (by decide) hrun (c12_48 hP hCL 12 kf18) (pc4 _ 48 52 rfl) rfl rfl (wf1 hs17 0 (by exact (by decide : 0 < 10)) : m16.read64 _ = p0 ∧ _) rfl (wf1 hs17 1 (by exact (by decide : 1 < 10)) : m16.read64 _ = p1 ∧ _) ?_
  refine x_orri (d := 22#5) (by decide) hrun (c12_52 hP hCL 12 kf18) (pc4 _ 52 56 rfl) ?_
  refine x_ldp_r (d1 := 12#5) (d2 := 13#5) (b := 0#5) (x := Pb) (a := Pb) (i := 2) (by decide) (by decide) (by decide) hrun (c12_56 hP hCL 12 kf18) (pc4 _ 56 60 rfl) rfl rfl (wf1 hs17 2 (by exact (by decide : 2 < 10)) : m16.read64 _ = p2 ∧ _) rfl (wf1 hs17 3 (by exact (by decide : 3 < 10)) : m16.read64 _ = p3 ∧ _) ?_
  refine x_movk48 (d := 24#5) (x := 18446744073709551312#64) (c := 36028797018963664#64) (by decide) hrun (c12_60 hP hCL 12 kf18) (pc4 _ 60 64 rfl) rfl (by decide) ?_
  refine x_ldp_r (d1 := 14#5) (d2 := 15#5) (b := 0#5) (x := Pb) (a := Pb) (i := 6) (by decide) (by decide) (by decide) hrun (c12_64 hP hCL 12 kf18) (pc4 _ 64 68 rfl) rfl rfl (wf1 hs17 6 (by exact (by decide : 6 < 10)) : m16.read64 _ = p6 ∧ _) rfl (wf1 hs17 7 (by exact (by decide : 7 < 10)) : m16.read64 _ = p7 ∧ _) ?_
  refine x_add (d := 1#5) (a := 18#5) (b := 10#5) (x := p9) (y := p4) (by decide) (by decide) (by decide) hrun (c12_68 hP hCL 12 kf18) (pc4 _ 68 72 rfl) rfl rfl (fun t68 e68 => ?_)
  refine x_sub (d := 10#5) (a := 10#5) (b := 18#5) (x := p4) (y := p9) (by decide) (by decide) (by decide) hrun (c12_72 hP hCL 12 kf18) (pc4 _ 72 76 rfl) rfl rfl (fun t72 e72 => ?_)
  refine x_add (d := 16#5) (a := 11#5) (b := 8#5) (x := p5) (y := p0) (by decide) (by decide) (by decide) hrun (c12_76 hP hCL 12 kf18) (pc4 _ 76 80 rfl) rfl rfl (fun t76 e76 => ?_)
  refine x_add (d := 8#5) (a := 8#5) (b := 24#5) (x := p0) (y := 36028797018963664#64) (by decide) (by decide) (by decide) hrun (c12_80 hP hCL 12 kf18) (pc4 _ 80 84 rfl) rfl rfl (fun t80 e80 => ?_)
  refine x_add (d := 10#5) (a := 10#5) (b := 22#5) (x := t72) (y := 0x007ffffffffffff0#64) (by decide) (by decide) (by decide) hrun (c12_84 hP hCL 12 kf18) (pc4 _ 84 88 rfl) rfl rfl (fun t84 e84 => ?_)
  refine x_mov (d := 20#5) (b := 0#5) (y := Pb) (by decide) (by decide) hrun (c12_88 hP hCL 12 kf18) (pc4 _ 88 92 rfl) rfl ?_
  rw [pick4] at hs17
  rw [pick4] at hs17
  refine x_stp_sp_x (t1 := 2#5) (t2 := 16#5) (v1 := u1) (v2 := t76) (i := 0) (j := 0) (by decide) (by decide) (aligned_sub hal 832 (by decide) (by decide)) hrun (c12_92 hP hCL 12 kf18) (pc4 _ 92 96 rfl) (aSS S 832 0 832 (8 * 0) (by decide)) (aSS S 832 (8 * (0 + 1)) 824 (8 * 0) (by decide)) hs17 (by exact (by decide : 0 < 1)) (by exact (by decide : 0 < 5)) rfl rfl (fun m19 hs20 kf21 => ?_)
  replace hs20 : m19 ⊨ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 824#64) ↦₆₄* [t76, a_1, a_2, a_3, a_4]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 784#64) ↦₆₄* [b_0, b_1, b_2, b_3, b_4]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs20
  replace kf21 := kf18.trans kf21
  clear hs17 kf18
  refine x_add (d := 0#5) (a := 14#5) (b := 9#5) (x := p6) (y := p1) (by decide) (by decide) (by decide) hrun (c12_96 hP hCL 12 kf21) (pc4 _ 96 100 rfl) rfl rfl (fun t96 e96 => ?_)
  refine x_add (d := 16#5) (a := 15#5) (b := 12#5) (x := p7) (y := p2) (by decide) (by decide) (by decide) hrun (c12_100 hP hCL 12 kf21) (pc4 _ 100 104 rfl) rfl rfl (fun t100 e100 => ?_)
  refine x_sub (d := 9#5) (a := 9#5) (b := 14#5) (x := p1) (y := p6) (by decide) (by decide) (by decide) hrun (c12_104 hP hCL 12 kf21) (pc4 _ 104 108 rfl) rfl rfl (fun t104 e104 => ?_)
  refine x_lsr51 (d := 14#5) (a := 10#5) (x := t84) (by decide) (by decide) hrun (c12_108 hP hCL 12 kf21) (pc4 _ 108 112 rfl) rfl (fun t108 e108 => ?_)
  refine x_sub (d := 8#5) (a := 8#5) (b := 11#5) (x := t80) (y := p5) (by decide) (by decide) (by decide) hrun (c12_112 hP hCL 12 kf21) (pc4 _ 112 116 rfl) rfl rfl (fun t112 e112 => ?_)
  rw [pick2] at hs20
  refine x_stp_sp (t1 := 0#5) (t2 := 16#5) (v1 := t96) (v2 := t100) (i := 1) (by decide) (by decide) (aligned_sub hal 832 (by decide) (by decide)) hrun (c12_116 hP hCL 12 kf21) (pc4 _ 116 120 rfl) (aSS S 832 16 824 (8 * 1) (by decide)) hs20 (by exact (by decide : 2 < 5)) rfl rfl (fun m22 hs23 kf24 => ?_)
  replace hs23 : m22 ⊨ ((S - 824#64) ↦₆₄* [t76, t96, t100, a_3, a_4]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 784#64) ↦₆₄* [b_0, b_1, b_2, b_3, b_4]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs23
  replace kf24 := kf21.trans kf24
  clear hs20 kf21
  refine x_add (d := 0#5) (a := 17#5) (b := 13#5) (x := p8) (y := p3) (by decide) (by decide) (by decide) hrun (c12_120 hP hCL 12 kf24) (pc4 _ 120 124 rfl) rfl rfl (fun t120 e120 => ?_)
  refine x_add (d := 9#5) (a := 9#5) (b := 22#5) (x := t104) (y := 0x007ffffffffffff0#64) (by decide) (by decide) (by decide) hrun (c12_124 hP hCL 12 kf24) (pc4 _ 124 128 rfl) rfl rfl (fun t124 e124 => ?_)
  refine x_movz32 (d := 25#5) (by decide) hrun (c12_128 hP hCL 12 kf24) (pc4 _ 128 132 rfl) ?_
  refine x_sub (d := 11#5) (a := 12#5) (b := 15#5) (x := p2) (y := p7) (by decide) (by decide) (by decide) hrun (c12_132 hP hCL 12 kf24) (pc4 _ 132 136 rfl) rfl rfl (fun t132 e132 => ?_)
  refine x_andi (d := 12#5) (a := 8#5) (x := t112) (by decide) (by decide) hrun (c12_136 hP hCL 12 kf24) (pc4 _ 136 140 rfl) rfl (fun t136 e136 => ?_)
  refine x_sub (d := 13#5) (a := 13#5) (b := 17#5) (x := p3) (y := p8) (by decide) (by decide) (by decide) hrun (c12_140 hP hCL 12 kf24) (pc4 _ 140 144 rfl) rfl rfl (fun t140 e140 => ?_)
  refine x_umaddl (d := 12#5) (a := 14#5) (b := 25#5) (c := 12#5) (x := t108) (y := ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64)) (z := t136) (by decide) (by decide) (by decide) (by decide) hrun (c12_144 hP hCL 12 kf24) (pc4 _ 144 148 rfl) rfl rfl rfl (fun t144 e144 => ?_)
  refine x_add (d := 11#5) (a := 11#5) (b := 22#5) (x := t132) (y := 0x007ffffffffffff0#64) (by decide) (by decide) (by decide) hrun (c12_148 hP hCL 12 kf24) (pc4 _ 148 152 rfl) rfl rfl (fun t148 e148 => ?_)
  refine x_andi (d := 14#5) (a := 9#5) (x := t124) (by decide) (by decide) hrun (c12_152 hP hCL 12 kf24) (pc4 _ 152 156 rfl) rfl (fun t152 e152 => ?_)
  refine x_add (d := 13#5) (a := 13#5) (b := 22#5) (x := t140) (y := 0x007ffffffffffff0#64) (by decide) (by decide) (by decide) hrun (c12_156 hP hCL 12 kf24) (pc4 _ 156 160 rfl) rfl rfl (fun t156 e156 => ?_)
  refine x_andi (d := 15#5) (a := 11#5) (x := t148) (by decide) (by decide) hrun (c12_160 hP hCL 12 kf24) (pc4 _ 160 164 rfl) rfl (fun t160 e160 => ?_)
  refine x_addlsr (d := 8#5) (a := 14#5) (b := 8#5) (x := t152) (y := t112) (by decide) (by decide) (by decide) hrun (c12_164 hP hCL 12 kf24) (pc4 _ 164 168 rfl) rfl rfl (fun t164 e164 => ?_)
  refine x_andi (d := 14#5) (a := 13#5) (x := t156) (by decide) (by decide) hrun (c12_168 hP hCL 12 kf24) (pc4 _ 168 172 rfl) rfl (fun t168 e168 => ?_)
  refine x_addlsr (d := 9#5) (a := 15#5) (b := 9#5) (x := t160) (y := t124) (by decide) (by decide) (by decide) hrun (c12_172 hP hCL 12 kf24) (pc4 _ 172 176 rfl) rfl rfl (fun t172 e172 => ?_)
  refine x_andi (d := 10#5) (a := 10#5) (x := t84) (by decide) (by decide) hrun (c12_176 hP hCL 12 kf24) (pc4 _ 176 180 rfl) rfl (fun t176 e176 => ?_)
  refine x_addlsr (d := 11#5) (a := 14#5) (b := 11#5) (x := t168) (y := t148) (by decide) (by decide) (by decide) hrun (c12_180 hP hCL 12 kf24) (pc4 _ 180 184 rfl) rfl rfl (fun t180 e180 => ?_)
  rw [pick5] at hs23
  refine x_stp_sp (t1 := 12#5) (t2 := 8#5) (v1 := t144) (v2 := t164) (i := 0) (by decide) (by decide) (aligned_sub hal 832 (by decide) (by decide)) hrun (c12_184 hP hCL 12 kf24) (pc4 _ 184 188 rfl) (aSS S 832 48 784 (8 * 0) (by decide)) hs23 (by exact (by decide : 1 < 5)) rfl rfl (fun m25 hs26 kf27 => ?_)
  replace hs26 : m25 ⊨ ((S - 784#64) ↦₆₄* [t144, t164, b_2, b_3, b_4]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, a_3, a_4]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ memRegion (S - 832#64 - 224#64) 224 ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((mpl.ρ symA24) ↦ᵣ fe51MontA24Bytes) ∗ F := hs26
  replace kf27 := kf24.trans kf27
  clear hs23 kf24
  refine x_addlsr (d := 8#5) (a := 10#5) (b := 13#5) (x := t176) (y := t156) (by decide) (by decide) (by decide) hrun (c12_188 hP hCL 12 kf27) (pc4 _ 188 192 rfl) rfl rfl (fun t188 e188 => ?_)
  exact hcont _ _ _ _ _ t144 t164 t76 t96 t100 t120 t68 t188 t172 t176 t180 t156 t168 t160 t72 t84 t80 t104 t112 t136 t108 t132 t124 t140 t148 t152 hrun kf27 hvs rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl e68 e72 e76 e80 e84 e96 e100 e104 e108 e112 e120 e124 e132 e136 e140 e144 e148 e152 e156 e160 e164 e168 e172 e176 e180 e188 hs26


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
theorem differentialAddAndDouble_0_192_dev {mpl : Arm64.Obj.MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S Pb Qb u1 : BitVec 64} {F : Arm64.SepProp}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 uw0 uw1 uw2 uw3 uw4 : BitVec 64}
    {sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 g0 g1 a_0 a_1 a_2 a_3 a_4 b_0 b_1 b_2 b_3 b_4 c_0 c_1 c_2 c_3 c_4 d_0 d_1 d_2 d_3 d_4 aa_0 aa_1 aa_2 aa_3 aa_4 bb_0 bb_1 bb_2 bb_3 bb_4 e_0 e_1 e_2 e_3 e_4 da_0 da_1 da_2 da_3 da_4 cb_0 cb_1 cb_2 cb_3 cb_4 sum_0 sum_1 sum_2 sum_3 sum_4 diff_0 diff_1 diff_2 diff_3 diff_4 u3_0 u3_1 u3_2 u3_3 u3_4 tmp_0 tmp_1 tmp_2 tmp_3 tmp_4 a24e_0 a24e_1 a24e_2 a24e_3 a24e_4 u2_0 u2_1 u2_2 u2_3 u2_4 a24epbb_0 a24epbb_1 a24epbb_2 a24epbb_3 a24epbb_4 w2_0 w2_1 w2_2 w2_3 w2_4 w3_0 w3_1 w3_2 w3_3 w3_4 : BitVec 64}
    (hal : (S &&& 15#64 == 0#64) = true)
    (hPU : p0.toNat < 9007199254740992 ∧ p1.toNat < 9007199254740992 ∧ p2.toNat < 9007199254740992 ∧ p3.toNat < 9007199254740992 ∧ p4.toNat < 9007199254740992)
    (hPW : p5.toNat < 9007199254740992 ∧ p6.toNat < 9007199254740992 ∧ p7.toNat < 9007199254740992 ∧ p8.toNat < 9007199254740992 ∧ p9.toNat < 9007199254740992)
    (hQU : q0.toNat < 9007199254740992 ∧ q1.toNat < 9007199254740992 ∧ q2.toNat < 9007199254740992 ∧ q3.toNat < 9007199254740992 ∧ q4.toNat < 9007199254740992)
    (hQW : q5.toNat < 9007199254740992 ∧ q6.toNat < 9007199254740992 ∧ q7.toNat < 9007199254740992 ∧ q8.toNat < 9007199254740992 ∧ q9.toNat < 9007199254740992)
    (hU1 : uw0.toNat < 18014398509481984 ∧ uw1.toNat < 18014398509481984 ∧ uw2.toNat < 18014398509481984 ∧ uw3.toNat < 18014398509481984 ∧ uw4.toNat < 18014398509481984)
    (hrun : s.status = Arm64.ExecStatus.Running) (hpc : s.pc = mpl.base 12) (hsp : s.sp = S)
    (hr0 : s.regs.regs 0#5 = Pb) (hr1 : s.regs.regs 1#5 = Qb) (hr2 : s.regs.regs 2#5 = u1)
    (hs : s.mem ⊨ ((S - 96#64) ↦₆₄* [sv0, sv1, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11]) ∗ ((S - 832#64) ↦₆₄* [g0]) ∗ ((S - 824#64) ↦₆₄* [a_0, a_1, a_2, a_3, a_4]) ∗ ((S - 784#64) ↦₆₄* [b_0, b_1, b_2, b_3, b_4]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F) :
    ∃ sf, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 12) s sf ∧
      sf.status = Arm64.ExecStatus.Running ∧
      sf.pc = mpl.base 12 + BitVec.ofNat 64 192 ∧
      sf.sp = S - 832#64 ∧
      Arm64.VRegFile.calleeSaved sf.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ t144 t164 t76 t96 t100 t120 t68 t188 t172 t176 t180 t156 t168 t160 t72 t84 t80 t104 t112 t136 t108 t132 t124 t140 t148 t152 : BitVec 64,
        sf.regs.regs 0#5 = t120 ∧
        sf.regs.regs 1#5 = t68 ∧
        sf.regs.regs 2#5 = u1 ∧
        sf.regs.regs 8#5 = t188 ∧
        sf.regs.regs 9#5 = t172 ∧
        sf.regs.regs 10#5 = t176 ∧
        sf.regs.regs 11#5 = t180 ∧
        sf.regs.regs 12#5 = t144 ∧
        sf.regs.regs 13#5 = t156 ∧
        sf.regs.regs 14#5 = t168 ∧
        sf.regs.regs 15#5 = t160 ∧
        sf.regs.regs 16#5 = t100 ∧
        sf.regs.regs 17#5 = p8 ∧
        sf.regs.regs 18#5 = p9 ∧
        sf.regs.regs 19#5 = Qb ∧
        sf.regs.regs 20#5 = Pb ∧
        sf.regs.regs 21#5 = (s.regs.regs 21#5) ∧
        sf.regs.regs 22#5 = 0x007ffffffffffff0#64 ∧
        sf.regs.regs 23#5 = (s.regs.regs 23#5) ∧
        sf.regs.regs 24#5 = 36028797018963664#64 ∧
        sf.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) ∧
        sf.regs.regs 26#5 = (s.regs.regs 26#5) ∧
        sf.regs.regs 27#5 = (s.regs.regs 27#5) ∧
        sf.regs.regs 28#5 = (s.regs.regs 28#5) ∧
        sf.regs.regs 29#5 = (S - 96#64) ∧
        sf.regs.regs 30#5 = (s.regs.regs 30#5) ∧
        (t68 = p9 + p4) ∧
        (t72 = p4 - p9) ∧
        (t76 = p5 + p0) ∧
        (t80 = p0 + 36028797018963664#64) ∧
        (t84 = t72 + 0x007ffffffffffff0#64) ∧
        (t96 = p6 + p1) ∧
        (t100 = p7 + p2) ∧
        (t104 = p1 - p6) ∧
        (t108 = t84 >>> 51) ∧
        (t112 = t80 - p5) ∧
        (t120 = p8 + p3) ∧
        (t124 = t104 + 0x007ffffffffffff0#64) ∧
        (t132 = p2 - p7) ∧
        (t136 = t112 &&& 0x0007ffffffffffff#64) ∧
        (t140 = p3 - p8) ∧
        (t144 = t136 + (t108.setWidth 32).setWidth 64 * (((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64).setWidth 32).setWidth 64) ∧
        (t148 = t132 + 0x007ffffffffffff0#64) ∧
        (t152 = t124 &&& 0x0007ffffffffffff#64) ∧
        (t156 = t140 + 0x007ffffffffffff0#64) ∧
        (t160 = t148 &&& 0x0007ffffffffffff#64) ∧
        (t164 = t152 + t112 >>> 51) ∧
        (t168 = t156 &&& 0x0007ffffffffffff#64) ∧
        (t172 = t160 + t124 >>> 51) ∧
        (t176 = t84 &&& 0x0007ffffffffffff#64) ∧
        (t180 = t168 + t148 >>> 51) ∧
        (t188 = t176 + t156 >>> 51) ∧
        sf.mem ⊨ ((S - 784#64) ↦₆₄* [t144, t164, b_2, b_3, b_4]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, a_3, a_4]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [(s.regs.regs 29#5), (s.regs.regs 30#5), (s.regs.regs 28#5), (s.regs.regs 27#5), (s.regs.regs 26#5), (s.regs.regs 25#5), (s.regs.regs 24#5), (s.regs.regs 23#5), (s.regs.regs 22#5), (s.regs.regs 21#5), (s.regs.regs 20#5), (s.regs.regs 19#5)]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F := by
  have er : upd (upd (upd s.regs.regs 0#5 Pb) 1#5 Qb) 2#5 u1 = s.regs.regs := by
    rw [upd_eq_self (by simp only [upd_apply, BitVec.reduceEq, ite_false]; exact hr2),
      upd_eq_self (by simp only [upd_apply, BitVec.reduceEq, ite_false]; exact hr1), upd_eq_self hr0]
  have e0 : mkS s (mpl.base 12) (upd (upd (upd s.regs.regs 0#5 Pb) 1#5 Qb) 2#5 u1) (S - 0#64) s.pstate
      s.mem s.vregs.regs = s := by
    rw [er, BitVec.sub_zero, ← hpc, ← hsp]; rfl
  rw [← e0]
  show Reach (bprog mpl 12) _ _
  refine d12_s1 (S := S) (vo := s.vregs.regs) (c19 := s.regs.regs 19#5) (c20 := s.regs.regs 20#5) (c21 := s.regs.regs 21#5) (c22 := s.regs.regs 22#5) (c23 := s.regs.regs 23#5) (c24 := s.regs.regs 24#5) (c25 := s.regs.regs 25#5) (c26 := s.regs.regs 26#5) (c27 := s.regs.regs 27#5) (c28 := s.regs.regs 28#5) (c29 := s.regs.regs 29#5) (c30 := s.regs.regs 30#5) hP hCL hal (by simpa only [lbw, valw, Nat.reducePow] using hPU) (by simpa only [lbw, valw, Nat.reducePow] using hPW) (by simpa only [lbw, valw, Nat.reducePow] using hQU) (by simpa only [lbw, valw, Nat.reducePow] using hQW) (by simpa only [lbw, valw, Nat.reducePow] using hU1) hrun (Memory.KeepsFrozen.refl _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hs ?_
  intro sb r ps m v t144 t164 t76 t96 t100 t120 t68 t188 t172 t176 t180 t156 t168 t160 t72 t84 t80 t104 t112 t136 t108 t132 t124 t140 t148 t152 hrun kf hvs hr0 hr1 hr2 hr8 hr9 hr10 hr11 hr12 hr13 hr14 hr15 hr16 hr17 hr18 hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26 hr27 hr28 hr29 hr30 e68 e72 e76 e80 e84 e96 e100 e104 e108 e112 e120 e124 e132 e136 e140 e144 e148 e152 e156 e160 e164 e168 e172 e176 e180 e188 hs
  apply Reach.done
  exact ⟨hrun, rfl, rfl, hvs, t144, t164, t76, t96, t100, t120, t68, t188, t172, t176, t180, t156, t168, t160, t72, t84, t80, t104, t112, t136, t108, t132, t124, t140, t148, t152, hr0, hr1, hr2, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr20, hr21, hr22, hr23, hr24, hr25, hr26, hr27, hr28, hr29, hr30, e68, e72, e76, e80, e84, e96, e100, e104, e108, e112, e120, e124, e132, e136, e140, e144, e148, e152, e156, e160, e164, e168, e172, e176, e180, e188, hs⟩

end X25519Dalek

end
end

section
open X25519Dalek

set_option maxHeartbeats 4000000


theorem solution {mpl : Arm64.Obj.MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S Pb Qb u1 : BitVec 64} {F : Arm64.SepProp}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 uw0 uw1 uw2 uw3 uw4 : BitVec 64}
    {sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 g0 g1 a_0 a_1 a_2 a_3 a_4 b_0 b_1 b_2 b_3 b_4 c_0 c_1 c_2 c_3 c_4 d_0 d_1 d_2 d_3 d_4 aa_0 aa_1 aa_2 aa_3 aa_4 bb_0 bb_1 bb_2 bb_3 bb_4 e_0 e_1 e_2 e_3 e_4 da_0 da_1 da_2 da_3 da_4 cb_0 cb_1 cb_2 cb_3 cb_4 sum_0 sum_1 sum_2 sum_3 sum_4 diff_0 diff_1 diff_2 diff_3 diff_4 u3_0 u3_1 u3_2 u3_3 u3_4 tmp_0 tmp_1 tmp_2 tmp_3 tmp_4 a24e_0 a24e_1 a24e_2 a24e_3 a24e_4 u2_0 u2_1 u2_2 u2_3 u2_4 a24epbb_0 a24epbb_1 a24epbb_2 a24epbb_3 a24epbb_4 w2_0 w2_1 w2_2 w2_3 w2_4 w3_0 w3_1 w3_2 w3_3 w3_4 : BitVec 64}
    (hal : (S &&& 15#64 == 0#64) = true)
    (hPU : p0.toNat < 9007199254740992 ∧ p1.toNat < 9007199254740992 ∧ p2.toNat < 9007199254740992 ∧ p3.toNat < 9007199254740992 ∧ p4.toNat < 9007199254740992)
    (hPW : p5.toNat < 9007199254740992 ∧ p6.toNat < 9007199254740992 ∧ p7.toNat < 9007199254740992 ∧ p8.toNat < 9007199254740992 ∧ p9.toNat < 9007199254740992)
    (hQU : q0.toNat < 9007199254740992 ∧ q1.toNat < 9007199254740992 ∧ q2.toNat < 9007199254740992 ∧ q3.toNat < 9007199254740992 ∧ q4.toNat < 9007199254740992)
    (hQW : q5.toNat < 9007199254740992 ∧ q6.toNat < 9007199254740992 ∧ q7.toNat < 9007199254740992 ∧ q8.toNat < 9007199254740992 ∧ q9.toNat < 9007199254740992)
    (hU1 : uw0.toNat < 18014398509481984 ∧ uw1.toNat < 18014398509481984 ∧ uw2.toNat < 18014398509481984 ∧ uw3.toNat < 18014398509481984 ∧ uw4.toNat < 18014398509481984)
    (hrun : s.status = Arm64.ExecStatus.Running) (hpc : s.pc = mpl.base 12) (hsp : s.sp = S)
    (hr0 : s.regs.regs 0#5 = Pb) (hr1 : s.regs.regs 1#5 = Qb) (hr2 : s.regs.regs 2#5 = u1)
    (hs : s.mem ⊨ ((S - 96#64) ↦₆₄* [sv0, sv1, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11]) ∗ ((S - 832#64) ↦₆₄* [g0]) ∗ ((S - 824#64) ↦₆₄* [a_0, a_1, a_2, a_3, a_4]) ∗ ((S - 784#64) ↦₆₄* [b_0, b_1, b_2, b_3, b_4]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F) :
    ∃ sf, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 12) s sf ∧
      sf.status = Arm64.ExecStatus.Running ∧
      sf.pc = mpl.base 12 + BitVec.ofNat 64 192 ∧
      sf.sp = S - 832#64 ∧
      Arm64.VRegFile.calleeSaved sf.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ t144 t164 t76 t96 t100 t120 t68 t188 t172 t176 t180 t156 t168 t160 t72 t84 t80 t104 t112 t136 t108 t132 t124 t140 t148 t152 : BitVec 64,
        sf.regs.regs 0#5 = t120 ∧
        sf.regs.regs 1#5 = t68 ∧
        sf.regs.regs 2#5 = u1 ∧
        sf.regs.regs 8#5 = t188 ∧
        sf.regs.regs 9#5 = t172 ∧
        sf.regs.regs 10#5 = t176 ∧
        sf.regs.regs 11#5 = t180 ∧
        sf.regs.regs 12#5 = t144 ∧
        sf.regs.regs 13#5 = t156 ∧
        sf.regs.regs 14#5 = t168 ∧
        sf.regs.regs 15#5 = t160 ∧
        sf.regs.regs 16#5 = t100 ∧
        sf.regs.regs 17#5 = p8 ∧
        sf.regs.regs 18#5 = p9 ∧
        sf.regs.regs 19#5 = Qb ∧
        sf.regs.regs 20#5 = Pb ∧
        sf.regs.regs 21#5 = (s.regs.regs 21#5) ∧
        sf.regs.regs 22#5 = 0x007ffffffffffff0#64 ∧
        sf.regs.regs 23#5 = (s.regs.regs 23#5) ∧
        sf.regs.regs 24#5 = 36028797018963664#64 ∧
        sf.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) ∧
        sf.regs.regs 26#5 = (s.regs.regs 26#5) ∧
        sf.regs.regs 27#5 = (s.regs.regs 27#5) ∧
        sf.regs.regs 28#5 = (s.regs.regs 28#5) ∧
        sf.regs.regs 29#5 = (S - 96#64) ∧
        sf.regs.regs 30#5 = (s.regs.regs 30#5) ∧
        (t68 = p9 + p4) ∧
        (t72 = p4 - p9) ∧
        (t76 = p5 + p0) ∧
        (t80 = p0 + 36028797018963664#64) ∧
        (t84 = t72 + 0x007ffffffffffff0#64) ∧
        (t96 = p6 + p1) ∧
        (t100 = p7 + p2) ∧
        (t104 = p1 - p6) ∧
        (t108 = t84 >>> 51) ∧
        (t112 = t80 - p5) ∧
        (t120 = p8 + p3) ∧
        (t124 = t104 + 0x007ffffffffffff0#64) ∧
        (t132 = p2 - p7) ∧
        (t136 = t112 &&& 0x0007ffffffffffff#64) ∧
        (t140 = p3 - p8) ∧
        (t144 = t136 + (t108.setWidth 32).setWidth 64 * (((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64).setWidth 32).setWidth 64) ∧
        (t148 = t132 + 0x007ffffffffffff0#64) ∧
        (t152 = t124 &&& 0x0007ffffffffffff#64) ∧
        (t156 = t140 + 0x007ffffffffffff0#64) ∧
        (t160 = t148 &&& 0x0007ffffffffffff#64) ∧
        (t164 = t152 + t112 >>> 51) ∧
        (t168 = t156 &&& 0x0007ffffffffffff#64) ∧
        (t172 = t160 + t124 >>> 51) ∧
        (t176 = t84 &&& 0x0007ffffffffffff#64) ∧
        (t180 = t168 + t148 >>> 51) ∧
        (t188 = t176 + t156 >>> 51) ∧
        sf.mem ⊨ ((S - 784#64) ↦₆₄* [t144, t164, b_2, b_3, b_4]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, a_3, a_4]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [(s.regs.regs 29#5), (s.regs.regs 30#5), (s.regs.regs 28#5), (s.regs.regs 27#5), (s.regs.regs 26#5), (s.regs.regs 25#5), (s.regs.regs 24#5), (s.regs.regs 23#5), (s.regs.regs 22#5), (s.regs.regs 21#5), (s.regs.regs 20#5), (s.regs.regs 19#5)]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F := by
  apply X25519Dalek.differentialAddAndDouble_0_192_dev <;> assumption

end
