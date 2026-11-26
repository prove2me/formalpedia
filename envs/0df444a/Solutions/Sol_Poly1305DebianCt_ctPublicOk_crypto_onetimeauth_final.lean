-- Prove2me | solution 1 for Poly1305DebianCt.ctPublicOk_crypto_onetimeauth_final
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-26T16:52:50.101847+00:00
-- url     : https://prove2.me/submissions/8caa1b85-248e-47e0-9841-83714da79b2f

import Definitions.Def_Poly1305DebianCt_PlacedObj
import Definitions.Def_Poly1305DebianCt_Spec
import Mathlib.Tactic.IntervalCases
import Definitions.Def_Link_LinkOk
import Definitions.Def_Arm64_Leakage
import Theorems.Thm_Arm64Facts_steps_codeLoaded_v2
import Theorems.Thm_Poly1305DebianCt_relOk_poly1305_finish_v2

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

theorem ex_mov (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr n) .LSL 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n)) sp ps m v := by
  simp [execInstWithSvc, execLogicalShift, evalLogical, State.readReg, State.writeReg, shiftVal,
    shift64, hd, hn]

theorem ex_add_gpr_sp (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD (.gpr d) .sp imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (sp + imm.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_false_fst, hd]

theorem ex_movz32 (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 16) :
    execInstWithSvc svc (.moveWide .W32 .MOVZ (.gpr d) imm 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d ((imm.zeroExtend 64).truncate 32 |>.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, State.writeReg, hd]

theorem ex_bl (off : BitVec 64) :
    execInstWithSvc svc (.bl off) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + off) (upd r 30#5 (pc + 4#64)) sp ps m v := by
  simp [execInstWithSvc]

theorem ex_b (off : BitVec 64) :
    execInstWithSvc svc (.b off) (mkS s0 pc r sp ps m v) = mkS s0 (pc + off) r sp ps m v := by
  simp [execInstWithSvc]

end exec

/-! ## Flags of `cmp` -/

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

end Poly1305DebianCtFw

end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw

open Arm64 Arm64.Obj

/-! ## Decoding by masks -/

theorem beq_false_of_mask {w K A M C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A &&& M) :
    (w &&& M == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, ← hK, BitVec.and_assoc, BitVec.and_comm M K, ← BitVec.and_assoc]

theorem beq_false_of_mask' {w K A C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A) :
    (w == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, hK]

theorem decode_adr_class (w : BitVec 32) (hK : w &&& 0x1f000000#32 = 0x10000000#32) :
    decode w = some (.adr (w.getLsbD 31) (Reg.fromZRBits (w.extractLsb' 0 5))
      (if w.getLsbD 31 then ((w.extractLsb' 5 19 ++ w.extractLsb' 29 2).signExtend 64) <<< 12
       else (w.extractLsb' 5 19 ++ w.extractLsb' 29 2).signExtend 64)) := by
  rw [decode]
  simp only [beq_false_of_mask' hK (C := 0xd503201f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4000001#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4200000#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd503201f#32) (M := 0xfffff01f#32) (by decide),
    beq_false_of_mask hK (C := 0#32) (M := 0xffff0000#32) (by decide),
    beq_false_of_mask hK (C := 0xd50b7420#32) (M := 0xffffffe0#32) (by decide), hK]
  simp

/-- The three `ldr xN, [xN, #imm]` words (`N = 4, 2, 3`) with their immediate field cleared. -/
def LdrTmpl (A : BitVec 32) (n : BitVec 5) : Prop :=
  (A = 0xf9400084#32 ∧ n = 4#5) ∨ (A = 0xf9400042#32 ∧ n = 2#5) ∨ (A = 0xf9400063#32 ∧ n = 3#5)

theorem decode_ldr (w A : BitVec 32) (n : BitVec 5) (hA : LdrTmpl A n)
    (hK : w &&& 0xffc003ff#32 = A) :
    decode w = some (.ldr .W64 .X64 false (.gpr n)
      (.Offset (.gpr n) (((w.extractLsb' 10 12).zeroExtend 64) <<< 3))) := by
  rcases hA with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ <;>
  · rw [decode]
    simp (config := {maxSteps := 4000000}) (disch := decide) only [beq_false_of_mask hK,
      beq_false_of_mask' hK, Bool.false_and, Bool.or_false, if_false, Bool.false_eq_true]
    have hb := fun i => (show (w.getLsbD i && (0xffc003ff#32 : BitVec 32).getLsbD i) = _ by
      rw [← BitVec.getLsbD_and, hK])
    have hc : (w &&& 0x3f000000#32 == 0x39000000#32) = true := by
      simp only [beq_iff_eq]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb i
      simp only [BitVec.getLsbD_and] at this ⊢
      interval_cases i <;> simp_all
    have e30 : BitVec.extractLsb' 30 2 w = 3#2 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb (30 + i)
      simp only [BitVec.getLsbD_extractLsb'] at this ⊢
      interval_cases i <;> simp_all
    have e22 : BitVec.extractLsb' 22 2 w = 1#2 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb (22 + i)
      simp only [BitVec.getLsbD_extractLsb'] at this ⊢
      interval_cases i <;> simp_all
    have e0 : BitVec.extractLsb' 0 5 w = n := by
      subst hn
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb (0 + i)
      simp only [BitVec.getLsbD_extractLsb'] at this ⊢
      interval_cases i <;> simp_all
    have e5 : BitVec.extractLsb' 5 5 w = n := by
      subst hn
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb (5 + i)
      simp only [BitVec.getLsbD_extractLsb'] at this ⊢
      interval_cases i <;> simp_all
    rw [if_pos hc, e30, e22, e0, e5]
    subst hn
    rfl

/-! ## `ADRP xN` and `LDR xN, [xN, :lo12:]` words -/

theorem hi_bits32 (D : BitVec 64) (h1 : -(2^32:Int) ≤ D.toInt) (h2 : D.toInt < 2^32) :
    ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem pageOf_eq (x : BitVec 64) : pageOf x = (x >>> 12) <<< 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [pageOf, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem pageOf_toNat (x : BitVec 64) : (pageOf x).toNat = x.toNat / 4096 * 4096 := by
  rw [pageOf_eq]; simp [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]; omega

theorem lo_bits (a b : BitVec 64) : ∀ i, i < 12 → (pageOf a - pageOf b).getLsbD i = false := by
  intro i hi
  have h : (pageOf a - pageOf b).toNat % 4096 = 0 := by
    rw [BitVec.toNat_sub, pageOf_toNat, pageOf_toNat]
    have := a.isLt; have := b.isLt; omega
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize (pageOf a - pageOf b).toNat = n at h ⊢
  interval_cases i <;> simp <;> omega

theorem pageOf_add_lo (T : BitVec 64) : pageOf T + (T &&& 0xfff#64) = T := by
  apply BitVec.eq_of_toNat_eq
  have h2 : (T &&& 0xfff#64).toNat = T.toNat % 4096 := by
    rw [BitVec.toNat_and]
    have : (0xfff#64 : BitVec 64).toNat = 2 ^ 12 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_add, pageOf_toNat, h2]
  have := T.isLt; omega

/-- The three `adrp xN` words (`N = 4, 2, 3`) with their immediate cleared. -/
def AdrpTmpl (W : BitVec 32) (n : BitVec 5) : Prop :=
  (W = 0x90000004#32 ∧ n = 4#5) ∨ (W = 0x90000002#32 ∧ n = 2#5) ∨ (W = 0x90000003#32 ∧ n = 3#5)

theorem adrpW_mask {W : BitVec 32} {n : BitVec 5} (hW : AdrpTmpl W n) (D : BitVec 64) :
    adrpWordOff W D &&& 0x1f000000#32 = 0x10000000#32 := by
  rcases hW with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [adrpWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem adrpW_31 {W : BitVec 32} {n : BitVec 5} (hW : AdrpTmpl W n) (D : BitVec 64) :
    (adrpWordOff W D).getLsbD 31 = true := by
  rcases hW with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [adrpWordOff]

theorem adrpW_rd {W : BitVec 32} {n : BitVec 5} (hW : AdrpTmpl W n) (D : BitVec 64) :
    (adrpWordOff W D).extractLsb' 0 5 = n := by
  rcases hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [adrpWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem adrpW_off {W : BitVec 32} {n : BitVec 5} (hW : AdrpTmpl W n) (D : BitVec 64)
    (hlo : ∀ i, i < 12 → D.getLsbD i = false)
    (hhi : ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32) :
    ((adrpWordOff W D).extractLsb' 5 19 ++ (adrpWordOff W D).extractLsb' 29 2).signExtend 64 <<< 12
      = D := by
  rcases hW with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [adrpWordOff, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend,
      BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getMsbD]
    interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
      first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
        exact (hhi _ (by omega) (by omega)).symm

theorem decode_adrp {W : BitVec 32} {n : BitVec 5} (hW : AdrpTmpl W n) {P T : BitVec 64}
    (hr : AdrpInRange P T) :
    decode (adrpWord W P T) = some (.adr true (.gpr n) (pageOf T - pageOf P)) := by
  rw [adrpWord, decode_adr_class _ (adrpW_mask hW _), adrpW_31 hW, adrpW_rd hW,
    adrpW_off hW _ (lo_bits T P) (hi_bits32 _ hr.1 hr.2)]
  rcases hW with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl

theorem lo12W_mask {A : BitVec 32} {n : BitVec 5} (hA : LdrTmpl A n) (T : BitVec 64) :
    lo12Word 3 A T &&& 0xffc003ff#32 = A := by
  rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [lo12Word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem lo12_imm (A : BitVec 32) (T : BitVec 64) (hal : T &&& 7#64 = 0#64) :
    ((lo12Word 3 A T).extractLsb' 10 12).zeroExtend 64 <<< 3 = T &&& 0xfff#64 := by
  have hb : ∀ i, i < 3 → T.getLsbD i = false := by
    intro i hi
    have := congrArg (fun x => x.getLsbD i) hal
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
    interval_cases i <;> simp_all
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;> exact hb _ (by omega)

theorem decode_ldr_lo12 {A : BitVec 32} {n : BitVec 5} (hA : LdrTmpl A n) (T : BitVec 64)
    (hal : T &&& 7#64 = 0#64) :
    decode (lo12Word 3 A T) = some (.ldr .W64 .X64 false (.gpr n) (.Offset (.gpr n) (T &&& 0xfff#64))) := by
  rw [decode_ldr _ A n hA (lo12W_mask hA T), lo12_imm A T hal]

end Poly1305DebianCtApi

end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw

open Arm64 Arm64.Obj

/-- The text block. -/
abbrev TX : CodeBlock := Poly1305DebianCt.libsodiumDebianOnetimeauthCtText

/-- The relocated word of a relocation that the linker neither relaxes nor retargets. -/
theorem pw_reloc (pl : Placement) {off : Nat} {r : RelocEntry} (hr : TX.relocAt? off = some r)
    (h1 : TX.relaxableAt off = false) (h2 : TX.relaxableAt (off - 4) = false)
    (h3 : r.kind.isGotOrTlsIe = false) (h5 : TX.b2bNext? r = none) :
    TX.patchedWord pl off =
      patchRelocWord r.kind (TX.wordAt off) (pl.base + BitVec.ofNat 64 off) (TX.target pl r) := by
  have hwr : TX.weakRefs = [] := rfl
  have hw : TX.undefWeakBranch pl r = false := by simp [CodeBlock.undefWeakBranch, hwr]
  simp [CodeBlock.patchedWord, hr, CodeBlock.relaxedAt, h1, h2, h3, hw, CodeBlock.relocTarget, h5]

theorem relocTarget_eq (pl : Placement) {off : Nat} {r : RelocEntry} (h5 : TX.b2bNext? r = none) :
    TX.relocTarget pl off r = TX.target pl r := by
  simp [CodeBlock.relocTarget, h5]

theorem reloc_mem {off : Nat} {r : RelocEntry} (hr : TX.relocAt? off = some r) : r ∈ TX.relocs :=
  List.mem_of_find?_eq_some hr

/-- The range condition the placement guarantees for the relocation at `off`. -/
theorem reloc_range {pl : Placement} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl) {off : Nat}
    {r : RelocEntry} (hr : TX.relocAt? off = some r) (hoff : r.off = off)
    (h5 : TX.b2bNext? r = none) :
    TX.relocInRange pl r.kind off (pl.base + BitVec.ofNat 64 off) (TX.target pl r) := by
  have h0 : TX.relocInRange pl r.kind r.off (pl.base + BitVec.ofNat 64 r.off)
      (TX.relocTarget pl r.off r) := (hP.text.relocs_ok r (reloc_mem hr)).2.2
  rw [hoff, relocTarget_eq pl h5] at h0
  exact h0

section
variable {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
  (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl) (hCL : (P pl ex).CodeLoaded m)
include hP hCL

theorem fetch_plain {off : Nat} (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324)
    (h : TX.relocAt? off = none) :
    (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 off) = decode (TX.wordAt off) := by
  rw [fetch_word hP hCL hal hlen, patchedWord_plain pl h]

/-- A `b` to a symbol of the block at `tgt`, `d = tgt - off` bytes ahead. -/
theorem fetch_b {off tgt : Nat} {r : RelocEntry} (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324)
    (hr : TX.relocAt? off = some r) (h1 : TX.relaxableAt off = false)
    (h2 : TX.relaxableAt (off - 4) = false) (h3 : r.kind.isGotOrTlsIe = false)
    (h5 : TX.b2bNext? r = none) (hk : r.kind = .jump26) (hadd : r.addend = 0)
    (hsym : lookup r.sym TX.symbols = some tgt) (d : BitVec 64)
    (hd : BitVec.ofNat 64 tgt - BitVec.ofNat 64 off = d) :
    (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (branchWord (TX.wordAt off) 0#64 d) := by
  rw [fetch_word hP hCL hal hlen, pw_reloc pl hr h1 h2 h3 h5, hk]
  have ht : TX.target pl r = pl.base + BitVec.ofNat 64 tgt := by
    simp [CodeBlock.target, addSignedAddr, hadd, CodeBlock.resolve, hsym]
  rw [ht]
  simp only [patchRelocWord, branchWord]
  congr 3
  rw [← hd]; bv_omega

/-- An `adrp xN` to a symbol outside the block. -/
theorem fetch_adrp {off : Nat} {r : RelocEntry} {W : BitVec 32} {n : BitVec 5}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324)
    (hr : TX.relocAt? off = some r) (hoff : r.off = off) (h1 : TX.relaxableAt off = false)
    (h2 : TX.relaxableAt (off - 4) = false) (h3 : r.kind.isGotOrTlsIe = false)
    (h5 : TX.b2bNext? r = none) (hk : r.kind = .adrpHi21) (hadd : r.addend = 0)
    (hsym : lookup r.sym TX.symbols = none) (hW : TX.wordAt off = W) (hT : AdrpTmpl W n) :
    (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      some (.adr true (.gpr n) (pageOf (pl.ρ r.sym) - pageOf (pl.base + BitVec.ofNat 64 off))) := by
  have ht : TX.target pl r = pl.ρ r.sym := by
    simp [CodeBlock.target, addSignedAddr, hadd, CodeBlock.resolve, hsym]
  have hrg := reloc_range hP hr hoff h5
  rw [hk, ht] at hrg
  rw [fetch_word hP hCL hal hlen, pw_reloc pl hr h1 h2 h3 h5, hk, ht, hW]
  exact decode_adrp hT hrg

/-- An `ldr xN, [xN, :lo12:sym]` for a symbol outside the block. -/
theorem fetch_ldr_lo12 {off : Nat} {r : RelocEntry} {A : BitVec 32} {n : BitVec 5}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324)
    (hr : TX.relocAt? off = some r) (hoff : r.off = off) (h1 : TX.relaxableAt off = false)
    (h2 : TX.relaxableAt (off - 4) = false) (h3 : r.kind.isGotOrTlsIe = false)
    (h5 : TX.b2bNext? r = none) (hk : r.kind = .ldst64Lo12) (hadd : r.addend = 0)
    (hsym : lookup r.sym TX.symbols = none) (hW : TX.wordAt off = A) (hT : LdrTmpl A n) :
    (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      some (.ldr .W64 .X64 false (.gpr n) (.Offset (.gpr n) (pl.ρ r.sym &&& 0xfff#64))) := by
  have ht : TX.target pl r = pl.ρ r.sym := by
    simp [CodeBlock.target, addSignedAddr, hadd, CodeBlock.resolve, hsym]
  have hrg := reloc_range hP hr hoff h5
  rw [hk, ht] at hrg
  rw [fetch_word hP hCL hal hlen, pw_reloc pl hr h1 h2 h3 h5, hk, ht, hW]
  exact decode_ldr_lo12 hT _ hrg

end

end Poly1305DebianCtApi

end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw

open Arm64 Arm64.Obj

/-- The pointer `implementation`. -/
abbrev symI : String := "implementation [libsodium_la_onetimeauth_poly1305]"
/-- The donna table `crypto_onetimeauth_poly1305_donna_implementation`. -/
abbrev symT : String := "crypto_onetimeauth_poly1305_donna_implementation"
/-- The string `crypto_onetimeauth_primitive` returns. -/
abbrev symS : String := "libsodium_la_crypto_onetimeauth:.rodata.str1.8+0x0"

/-- The address of block symbol at offset `o`. -/
abbrev at_ (pl : Placement) (o : Nat) : BitVec 64 := pl.base + BitVec.ofNat 64 o

theorem bytesLE8 (v : BitVec 64) : bytesLE 8 v = unpack64 v := by
  simp [bytesLE, unpack64, List.range, List.range.loop]

abbrev LIB : PlacedLib := Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib

theorem resolve_out (pl : Placement) (x : String) (h : lookup x LIB.text.symbols = none) :
    LIB.text.resolve pl x = pl.ρ x := by
  simp [CodeBlock.resolve, h]

theorem resolve_in (pl : Placement) (x : String) (o : Nat) (h : lookup x LIB.text.symbols = some o) :
    LIB.text.resolve pl x = at_ pl o := by
  simp [CodeBlock.resolve, h]

/-- The pointer's data object. -/
abbrev dI : SymDataInfo :=
  { sym := symI, align := 8, readOnly := false, zeroTail := 0,
    bytes := Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedData1,
    relocs := [{ off := 0, kind := .abs64, sym := symT }] }

/-- The table's data object. -/
abbrev dT : SymDataInfo :=
  { sym := symT, align := 8, readOnly := false, zeroTail := 0,
    bytes := Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedData2,
    relocs := [
      { off := 0, kind := .abs64, sym := "crypto_onetimeauth_poly1305_donna [libsodium_la_poly1305_donna]" },
      { off := 8, kind := .abs64, sym := "crypto_onetimeauth_poly1305_donna_verify [libsodium_la_poly1305_donna]" },
      { off := 16, kind := .abs64, sym := "crypto_onetimeauth_poly1305_donna_init [libsodium_la_poly1305_donna]" },
      { off := 24, kind := .abs64, sym := "crypto_onetimeauth_poly1305_donna_update [libsodium_la_poly1305_donna]" },
      { off := 32, kind := .abs64, sym := "crypto_onetimeauth_poly1305_donna_final [libsodium_la_poly1305_donna]" }] }

/-- The string's data object. -/
abbrev dS : SymDataInfo :=
  { sym := symS, align := 8, readOnly := true, zeroTail := 0,
    bytes := Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedData0, relocs := [] }

/-- `optblocker_u16` (verify.o). -/
abbrev symO : String := "optblocker_u16 [libsodium_la_verify]"

/-- The `optblocker_u16` data object. -/
abbrev dO : SymDataInfo :=
  { sym := symO, align := 2, readOnly := false, zeroTail := 2,
    bytes := Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedData3, relocs := [] }

theorem data_eq : Poly1305DebianCt.libsodiumDebianOnetimeauthCtData = [dS, dI, dT, dO] := rfl

/-- The three data objects of the first three objects (string, pointer, table). -/
def data3 (pl : Placement) : SepProp :=
  (pl.ρ symS ↦ᵣ LIB.patchedData pl dS) ∗
    ((pl.ρ symI ↦ₛ LIB.patchedData pl dI) ∗ (pl.ρ symT ↦ₛ LIB.patchedData pl dT))

theorem dataInit_eq (pl : Placement) :
    LIB.dataInit pl = data3 pl ∗ (pl.ρ symO ↦ₛ LIB.patchedData pl dO) := by
  simp only [PlacedLib.dataInit, LIB, Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib, data_eq,
    List.map, sepAll, data3, if_true, if_false]
  rw [sepConj_assoc, sepConj_assoc]
  rfl

theorem pdI (pl : Placement) : LIB.patchedData pl dI = unpack64 (pl.ρ symT) := by
  simp only [PlacedLib.patchedData, PlacedLib.patchDataReloc, List.foldl,
    resolve_out pl symT (by decide)]
  simp [Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedData1, addSignedAddr, bytesLE8]

theorem pdT (pl : Placement) : LIB.patchedData pl dT =
    unpack64 (at_ pl 0x584) ++ unpack64 (at_ pl 0x640) ++ unpack64 (at_ pl 0x3ac) ++
      unpack64 (at_ pl 0x400) ++ unpack64 (at_ pl 0x564) := by
  simp only [PlacedLib.patchedData, PlacedLib.patchDataReloc, List.foldl,
    resolve_in pl "crypto_onetimeauth_poly1305_donna [libsodium_la_poly1305_donna]" 0x584 (by decide),
    resolve_in pl "crypto_onetimeauth_poly1305_donna_verify [libsodium_la_poly1305_donna]" 0x640 (by decide),
    resolve_in pl "crypto_onetimeauth_poly1305_donna_init [libsodium_la_poly1305_donna]" 0x3ac (by decide),
    resolve_in pl "crypto_onetimeauth_poly1305_donna_update [libsodium_la_poly1305_donna]" 0x400 (by decide),
    resolve_in pl "crypto_onetimeauth_poly1305_donna_final [libsodium_la_poly1305_donna]" 0x564 (by decide)]
  simp [Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedData2, addSignedAddr, bytesLE8, unpack64]

end Poly1305DebianCtApi

end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw

open Arm64 Arm64.Obj

/-! ## Reading the pointer and the table -/

theorem read_mid {m : Memory} {a v : BitVec 64} {F : SepProp} (A B : List (BitVec 8))
    (hs : m ⊨ (a ↦ₛ (A ++ unpack64 v ++ B)) ∗ F) :
    m.read64 (a + BitVec.ofNat 64 A.length) = v ∧
      m.canRead (a + BitVec.ofNat 64 A.length) 8 = true := by
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append, ← pointsTo64_eq_bytes] at hs
  have hs' : m ⊨ ((a + BitVec.ofNat 64 A.length) ↦₆₄ v) ∗
      ((a ↦ₛ A) ∗ ((a + BitVec.ofNat 64 A.length + BitVec.ofNat 64 (unpack64 v).length) ↦ₛ B) ∗ F) :=
    Satisfies.of_eq hs
  exact ⟨(sat64_read hs').1, (sat64_read hs').2.1⟩

/-- The table entry `j` (byte offset `8 j`) holds the donna function at text offset `o`. -/
theorem data_reads3 (pl : Placement) {m : Memory} {X R : SepProp}
    (hs : m ⊨ (X ∗ data3 pl) ∗ R) :
    (m.read64 (pl.ρ symI) = pl.ρ symT ∧ m.canRead (pl.ρ symI) 8 = true) ∧
    (m.read64 (pl.ρ symT + 0#64) = at_ pl 0x584 ∧ m.canRead (pl.ρ symT + 0#64) 8 = true) ∧
    (m.read64 (pl.ρ symT + 8#64) = at_ pl 0x640 ∧ m.canRead (pl.ρ symT + 8#64) 8 = true) ∧
    (m.read64 (pl.ρ symT + 16#64) = at_ pl 0x3ac ∧ m.canRead (pl.ρ symT + 16#64) 8 = true) ∧
    (m.read64 (pl.ρ symT + 24#64) = at_ pl 0x400 ∧ m.canRead (pl.ρ symT + 24#64) 8 = true) ∧
    (m.read64 (pl.ρ symT + 32#64) = at_ pl 0x564 ∧ m.canRead (pl.ρ symT + 32#64) 8 = true) := by
  simp only [data3, pdI, pdT] at hs
  have hI : m ⊨ (pl.ρ symI ↦ₛ ([] ++ unpack64 (pl.ρ symT) ++ [])) ∗
      ((pl.ρ symS ↦ᵣ LIB.patchedData pl dS) ∗ (pl.ρ symT ↦ₛ (unpack64 (at_ pl 0x584) ++
        unpack64 (at_ pl 0x640) ++ unpack64 (at_ pl 0x3ac) ++ unpack64 (at_ pl 0x400) ++
        unpack64 (at_ pl 0x564))) ∗ X ∗ R) := by
    simp only [List.nil_append, List.append_nil]; exact Satisfies.of_eq hs
  have hT : ∀ (A B : List (BitVec 8)) (v : BitVec 64),
      unpack64 (at_ pl 0x584) ++ unpack64 (at_ pl 0x640) ++ unpack64 (at_ pl 0x3ac) ++
        unpack64 (at_ pl 0x400) ++ unpack64 (at_ pl 0x564) = A ++ unpack64 v ++ B →
      m.read64 (pl.ρ symT + BitVec.ofNat 64 A.length) = v ∧
        m.canRead (pl.ρ symT + BitVec.ofNat 64 A.length) 8 = true := by
    intro A B v he
    rw [he] at hs
    have h2 : m ⊨ (pl.ρ symT ↦ₛ (A ++ unpack64 v ++ B)) ∗
        ((pl.ρ symS ↦ᵣ LIB.patchedData pl dS) ∗ (pl.ρ symI ↦ₛ unpack64 (pl.ρ symT)) ∗ X ∗ R) :=
      Satisfies.of_eq hs
    exact read_mid A B h2
  have r0 := hT [] (unpack64 (at_ pl 0x640) ++ unpack64 (at_ pl 0x3ac) ++
    unpack64 (at_ pl 0x400) ++ unpack64 (at_ pl 0x564)) (at_ pl 0x584)
    (by simp only [List.nil_append, List.append_assoc])
  have r1 := hT (unpack64 (at_ pl 0x584))
    (unpack64 (at_ pl 0x3ac) ++ unpack64 (at_ pl 0x400) ++ unpack64 (at_ pl 0x564)) (at_ pl 0x640)
    (by simp only [List.append_assoc])
  have r2 := hT (unpack64 (at_ pl 0x584) ++ unpack64 (at_ pl 0x640))
    (unpack64 (at_ pl 0x400) ++ unpack64 (at_ pl 0x564)) (at_ pl 0x3ac)
    (by simp only [List.append_assoc])
  have r3 := hT (unpack64 (at_ pl 0x584) ++ unpack64 (at_ pl 0x640) ++ unpack64 (at_ pl 0x3ac))
    (unpack64 (at_ pl 0x564)) (at_ pl 0x400)
    (by simp only [List.append_assoc])
  have r4 := hT (unpack64 (at_ pl 0x584) ++ unpack64 (at_ pl 0x640) ++ unpack64 (at_ pl 0x3ac) ++
    unpack64 (at_ pl 0x400)) [] (at_ pl 0x564) (by simp only [List.append_assoc, List.append_nil])
  simp only [List.length_append, unpack64_length, List.length_nil] at r0 r1 r2 r3 r4
  have rI := read_mid [] [] hI
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at rI
  exact ⟨rI, r0, r1, r2, r3, r4⟩

theorem data_reads (pl : Placement) {m : Memory} {X R : SepProp}
    (hs : m ⊨ (X ∗ LIB.dataInit pl) ∗ R) :
    (m.read64 (pl.ρ symI) = pl.ρ symT ∧ m.canRead (pl.ρ symI) 8 = true) ∧
    (m.read64 (pl.ρ symT + 0#64) = at_ pl 0x584 ∧ m.canRead (pl.ρ symT + 0#64) 8 = true) ∧
    (m.read64 (pl.ρ symT + 8#64) = at_ pl 0x640 ∧ m.canRead (pl.ρ symT + 8#64) 8 = true) ∧
    (m.read64 (pl.ρ symT + 16#64) = at_ pl 0x3ac ∧ m.canRead (pl.ρ symT + 16#64) 8 = true) ∧
    (m.read64 (pl.ρ symT + 24#64) = at_ pl 0x400 ∧ m.canRead (pl.ρ symT + 24#64) 8 = true) ∧
    (m.read64 (pl.ρ symT + 32#64) = at_ pl 0x564 ∧ m.canRead (pl.ρ symT + 32#64) 8 = true) := by
  rw [dataInit_eq] at hs
  have h2 : m ⊨ (X ∗ data3 pl) ∗ ((pl.ρ symO ↦ₛ LIB.patchedData pl dO) ∗ R) := Satisfies.of_eq hs
  exact data_reads3 pl h2

/-! ## The specs look at the entry state only through `sp` and `x0`–`x3` -/


/-- The fetch facts of one entry point at `e` whose counterpart is at `c`. -/
structure WrapCode (P : Program) (e c d I k : BitVec 64) (N : BitVec 5) : Prop where
  b_ok : e + 4#64 + d = c
  f0 : ∀ m, P.CodeLoaded m → P.fetchMem m e = some (.hint 0x22#7)
  f1 : ∀ m, P.CodeLoaded m → P.fetchMem m (e + 4#64) = some (.b d)
  f2 : ∀ m, P.CodeLoaded m → P.fetchMem m c = some (.hint 0x22#7)
  f3 : ∀ m, P.CodeLoaded m → P.fetchMem m (c + 4#64) =
    some (.adr true (.gpr N) (pageOf I - pageOf (c + 4#64)))
  f4 : ∀ m, P.CodeLoaded m → P.fetchMem m (c + 8#64) =
    some (.ldr .W64 .X64 false (.gpr N) (.Offset (.gpr N) (I &&& 0xfff#64)))
  f5 : ∀ m, P.CodeLoaded m → P.fetchMem m (c + 12#64) =
    some (.ldr .W64 .X64 false (.gpr N) (.Offset (.gpr N) k))
  f6 : ∀ m, P.CodeLoaded m → P.fetchMem m (c + 16#64) =
    some (.logicalShift .W64 .ORR (.gpr 16#5) .xzr (.gpr N) .LSL 0)
  f7 : ∀ m, P.CodeLoaded m → P.fetchMem m (c + 20#64) = some (.br (.gpr 16#5))


/-! ## The code of the entry points -/

theorem at_add (pl : Placement) (o j : Nat) :
    at_ pl o + BitVec.ofNat 64 j = at_ pl (o + j) := by
  simp only [at_]; rw [BitVec.add_assoc, BitVec.ofNat_add]

section
variable {pl : Placement} {ex : String → Option (State → State)}
  (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)
include hP

theorem wc_final : WrapCode (P pl ex) (at_ pl 0x60) (at_ pl 0x120) 188#64 (pl.ρ symI) 32#64 2#5 where
  b_ok := by rw [at_add pl 0x60 4, at_add pl _ 188]
  f0 := fun m hCL => by rw [fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f1 := fun m hCL => by
    rw [at_add pl 0x60 4, fetch_b hP hCL (off := 0x60+4) (tgt := 0x120)
      (r := { off := 100, kind := .jump26, sym := "crypto_onetimeauth_poly1305_final" })
      (by decide) (by decide) (by rfl) (by decide) (by decide) (by rfl) (by rfl) rfl rfl (by rfl)
      188#64 (by rfl)]
    rfl
  f2 := fun m hCL => by rw [fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f3 := fun m hCL => by
    rw [at_add pl 0x120 4, fetch_adrp hP hCL (off := 0x120+4)
      (r := { off := 292, kind := .adrpHi21, sym := symI }) (W := 0x90000002#32)
      (by decide) (by decide) (by rfl) rfl (by decide) (by decide) (by rfl) (by rfl) rfl rfl
      (by decide) (by rfl) (Or.inr (Or.inl ⟨rfl, rfl⟩))]
  f4 := fun m hCL => by
    rw [at_add pl 0x120 8, fetch_ldr_lo12 hP hCL (off := 0x120+8)
      (r := { off := 296, kind := .ldst64Lo12, sym := symI }) (A := 0xf9400042#32)
      (by decide) (by decide) (by rfl) rfl (by decide) (by decide) (by rfl) (by rfl) rfl rfl
      (by decide) (by rfl) (Or.inr (Or.inl ⟨rfl, rfl⟩))]
  f5 := fun m hCL => by rw [at_add pl 0x120 12, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f6 := fun m hCL => by rw [at_add pl 0x120 16, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f7 := fun m hCL => by rw [at_add pl 0x120 20, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl

end

end Poly1305DebianCtApi

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

theorem step_exec_eq {p : Program} {s s' : State} {i : Instr}
    (hf : p.fetchMem s.mem s.pc = some i) (hs : Step p s s') : s' = p.evalInst i s := by
  cases hs with
  | exec _ h_fetch => rw [hf] at h_fetch; cases h_fetch; rfl
  | halt_unmapped _ h_fetch => rw [hf] at h_fetch; cases h_fetch
  | externHook _ h_ext => rw [externAt_none_of_fetch hf] at h_ext; cases h_ext
  | extern_fault _ h_ext => rw [externAt_none_of_fetch hf] at h_ext; cases h_ext

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

/-! ## Stop conditions -/

/-- `stop₁` and `stop₂` agree on states with equal `pc`, `sp` and status. -/
def StopCompat (stop₁ stop₂ : State → Prop) : Prop :=
  ∀ s₁ s₂ : State, s₁.pc = s₂.pc → s₁.sp = s₂.sp → s₁.status = s₂.status → (stop₁ s₁ ↔ stop₂ s₂)

theorem stopCompat_sub {a₁ a₂ : State} (hlr : a₁.readReg64 Reg.lr = a₂.readReg64 Reg.lr)
    (hsp : a₁.sp = a₂.sp) : StopCompat (SubroutineStop a₁) (SubroutineStop a₂) := by
  intro s₁ s₂ hpc hs hst
  unfold SubroutineStop Returned
  rw [hpc, hs, hst, hlr, hsp]

/-! ## Observational equivalence, backwards -/

section rules
variable {p : Program} {ar : String → Nat} {stop₁ stop₂ : State → Prop}


theorem obsUntil_stopped {s f : State} {t : List Obs} (hs : stop₁ s)
    (h : ObsUntil p ar stop₁ s t f) : t = [] ∧ f = s := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step hc _ _ => exact absurd hs hc

theorem obsIncluded_stop {s₁ s₂ : State} (h1 : stop₁ s₁) (h2 : stop₂ s₂) :
    ObsIncluded p ar stop₁ stop₂ s₁ s₂ := by
  intro t f₁ hr
  obtain ⟨rfl, rfl⟩ := obsUntil_stopped h1 hr
  exact ⟨s₂, ObsUntil.refl s₂, iff_of_true h1 h2⟩

/-- Both runs have stopped. -/
theorem oe_stop {s₁ s₂ : State} (h1 : stop₁ s₁) (h2 : stop₂ s₂) :
    ObsEquiv p ar stop₁ stop₂ s₁ s₂ :=
  ⟨obsIncluded_stop h1 h2, obsIncluded_stop h2 h1⟩

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

/-- Two states that differ at most in memory: the second is the first with its memory. -/
theorem sameExceptMem_eq {s₁ s₂ : State} (h : SameExceptMem s₁ s₂) :
    s₂ = { s₁ with mem := s₂.mem } := by
  cases s₁; cases s₂; unfold SameExceptMem at h; simp only [State.mk.injEq] at h ⊢
  simp_all

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

theorem ex_ret :
    execInstWithSvc svc (.ret (.gpr 30#5)) (mkS s0 pc r sp ps m v) =
      mkS s0 (r 30#5) r sp ps m v := by
  simp [execInstWithSvc]

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

/-! ## Stepping, and calls -/

end Poly1305DebianCtFw

end
end

section
section
/-! # Two runs on `mkS` states, the dispatch wrapper, and permissions under stores

Both runs of a constant-time proof are written `mkS s₁ pc rⱼ sp psⱼ mⱼ vⱼ` over the first run's
entry state `s₁` (the entries differ only in memory, `Poly1305DebianCtFw.sameExceptMem_eq`), so
`pc`, `sp` and the status agree by construction. `oe_mk` is the framework's `oe_exec` on such
pairs, threading `CodeLoaded`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw

open Arm64 Arm64.Obj Leakage

/-! ## Memory permissions survive stores -/

/-! ## Instruction shapes not in the framework -/

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_adrpS (rd : BitVec 5) (hd : rd ≠ 31#5) (off : BitVec 64) :
    execInstWithSvc svc (.adr true (.gpr rd) off) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r rd ((pc &&& 0xfffffffffffff000#64) + off)) sp ps m v := by
  simp [execInstWithSvc, hd]

theorem ex_brS (n : BitVec 5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.br (.gpr n)) (mkS s0 pc r sp ps m v) = mkS s0 (r n) r sp ps m v := by
  simp [execInstWithSvc, hn]

end exec

theorem upd_upd_same {α : Type} (r : BitVec 5 → α) (i : BitVec 5) (a b : α) :
    upd (upd r i a) i b = upd r i b := by
  funext j; simp only [upd_apply]; split <;> rfl

/-! ## The step rule on `mkS` pairs -/

section rules
variable {p : Program} {ar : String → Nat} {stop₁ stop₂ : State → Prop}

theorem oe_mk (hc : StopCompat stop₁ stop₂) {s0 : State} {pc sp : BitVec 64}
    {r₁ r₂ : BitVec 5 → BitVec 64} {ps₁ ps₂ : PState} {m₁ m₂ : Memory}
    {v₁ v₂ : BitVec 5 → BitVec 128} {i : Instr}
    (hrun : s0.status = .Running) (hCL₁ : p.CodeLoaded m₁) (hCL₂ : p.CodeLoaded m₂)
    (hf₁ : p.fetchMem m₁ pc = some i) (hf₂ : p.fetchMem m₂ pc = some i)
    (hl : leakedValues i (mkS s0 pc r₁ sp ps₁ m₁ v₁) = leakedValues i (mkS s0 pc r₂ sp ps₂ m₂ v₂))
    (h : p.CodeLoaded (execInstWithSvc (evalSvc p.svc) i (mkS s0 pc r₁ sp ps₁ m₁ v₁)).mem →
      p.CodeLoaded (execInstWithSvc (evalSvc p.svc) i (mkS s0 pc r₂ sp ps₂ m₂ v₂)).mem →
      ObsEquiv p ar stop₁ stop₂ (execInstWithSvc (evalSvc p.svc) i (mkS s0 pc r₁ sp ps₁ m₁ v₁))
        (execInstWithSvc (evalSvc p.svc) i (mkS s0 pc r₂ sp ps₂ m₂ v₂))) :
    ObsEquiv p ar stop₁ stop₂ (mkS s0 pc r₁ sp ps₁ m₁ v₁) (mkS s0 pc r₂ sp ps₂ m₂ v₂) := by
  have st₁ : Step p (mkS s0 pc r₁ sp ps₁ m₁ v₁) (p.evalInst i (mkS s0 pc r₁ sp ps₁ m₁ v₁)) :=
    Step.exec hrun hf₁
  have st₂ : Step p (mkS s0 pc r₂ sp ps₂ m₂ v₂) (p.evalInst i (mkS s0 pc r₂ sp ps₂ m₂ v₂)) :=
    Step.exec hrun hf₂
  exact oe_exec hc rfl rfl hrun hrun hf₁ hf₂ hl
    (h (Arm64Facts.steps_codeLoaded_v2 (Steps.step st₁ (Steps.refl _)) hCL₁)
      (Arm64Facts.steps_codeLoaded_v2 (Steps.step st₂ (Steps.refl _)) hCL₂))

/-- The dispatch wrapper `bti c; b c; bti c; adrp xN; ldr xN; ldr xN, [xN, #k]; mov x16, xN;
br x16`, run in both runs from equal registers, reaching `fn` (the table entry, the same in both). -/
theorem oe_wrap (hc : StopCompat stop₁ stop₂) {e c d I k Tb fn : BitVec 64} {N : BitVec 5}
    (hW : WrapCode p e c d I k N) (hN31 : N ≠ 31#5) {s0 : State} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m₁ m₂ : Memory} {v : BitVec 5 → BitVec 128}
    (hrun : s0.status = .Running) (hCL₁ : p.CodeLoaded m₁) (hCL₂ : p.CodeLoaded m₂)
    (hrI₁ : m₁.read64 I = Tb) (hcI₁ : m₁.canRead I 8 = true)
    (hrT₁ : m₁.read64 (Tb + k) = fn) (hcT₁ : m₁.canRead (Tb + k) 8 = true)
    (hrI₂ : m₂.read64 I = Tb) (hcI₂ : m₂.canRead I 8 = true)
    (hrT₂ : m₂.read64 (Tb + k) = fn) (hcT₂ : m₂.canRead (Tb + k) 8 = true)
    (h : ObsEquiv p ar stop₁ stop₂ (mkS s0 fn (upd (upd r N fn) 16#5 fn) sp ps m₁ v)
      (mkS s0 fn (upd (upd r N fn) 16#5 fn) sp ps m₂ v)) :
    ObsEquiv p ar stop₁ stop₂ (mkS s0 e r sp ps m₁ v) (mkS s0 e r sp ps m₂ v) := by
  -- `bti c`
  refine oe_mk hc hrun hCL₁ hCL₂ (hW.f0 _ hCL₁) (hW.f0 _ hCL₂) rfl fun _ _ => ?_
  rw [ex_hint, ex_hint]
  -- `b c`
  refine oe_mk hc hrun hCL₁ hCL₂ (hW.f1 _ hCL₁) (hW.f1 _ hCL₂) rfl fun _ _ => ?_
  rw [ex_b, ex_b, hW.b_ok]
  -- `bti c`
  refine oe_mk hc hrun hCL₁ hCL₂ (hW.f2 _ hCL₁) (hW.f2 _ hCL₂) rfl fun _ _ => ?_
  rw [ex_hint, ex_hint]
  -- `adrp xN, I`
  refine oe_mk hc hrun hCL₁ hCL₂ (hW.f3 _ hCL₁) (hW.f3 _ hCL₂) rfl fun _ _ => ?_
  rw [ex_adrpS _ hN31, ex_adrpS _ hN31,
    show ((c + 4#64) &&& 0xfffffffffffff000#64) + (pageOf I - pageOf (c + 4#64)) = pageOf I by
      rw [show (c + 4#64) &&& 0xfffffffffffff000#64 = pageOf (c + 4#64) from rfl]; bv_omega,
    show c + 4#64 + 4#64 = c + 8#64 by bv_omega]
  -- `ldr xN, [xN, :lo12:I]`
  have e8 : upd r N (pageOf I) N + (I &&& 0xfff#64) = I := by simp [pageOf_add_lo]
  refine oe_mk hc hrun hCL₁ hCL₂ (hW.f4 _ hCL₁) (hW.f4 _ hCL₂) rfl fun _ _ => ?_
  rw [ex_ldr64_gpr _ _ hN31 hN31 _ (by rw [e8]; exact hcI₁),
    ex_ldr64_gpr _ _ hN31 hN31 _ (by rw [e8]; exact hcI₂), e8, hrI₁, hrI₂, upd_upd_same,
    show c + 8#64 + 4#64 = c + 12#64 by bv_omega]
  -- `ldr xN, [xN, #k]`
  have e12 : upd r N Tb N + k = Tb + k := by simp
  refine oe_mk hc hrun hCL₁ hCL₂ (hW.f5 _ hCL₁) (hW.f5 _ hCL₂) rfl fun _ _ => ?_
  rw [ex_ldr64_gpr _ _ hN31 hN31 _ (by rw [e12]; exact hcT₁),
    ex_ldr64_gpr _ _ hN31 hN31 _ (by rw [e12]; exact hcT₂), e12, hrT₁, hrT₂, upd_upd_same,
    show c + 12#64 + 4#64 = c + 16#64 by bv_omega]
  -- `mov x16, xN`
  refine oe_mk hc hrun hCL₁ hCL₂ (hW.f6 _ hCL₁) (hW.f6 _ hCL₂) rfl fun _ _ => ?_
  rw [ex_mov _ _ (by decide) hN31, ex_mov _ _ (by decide) hN31, upd_same,
    show c + 16#64 + 4#64 = c + 20#64 by bv_omega]
  -- `br x16`
  refine oe_mk hc hrun hCL₁ hCL₂ (hW.f7 _ hCL₁) (hW.f7 _ hCL₂) rfl fun _ _ => ?_
  rw [ex_brS _ (by decide), ex_brS _ (by decide), upd_same]
  exact h

end rules

end Poly1305DebianCtApi

end
end

section
section
/-! # `crypto_onetimeauth_init` is constant-time

`crypto_onetimeauth_init` (text 0x48): `bti c; b crypto_onetimeauth_poly1305_init`; that (0xe0):
`bti c; adrp x2, implementation; ldr x2, [x2, :lo12:implementation]; ldr x2, [x2, #16];
mov x16, x2; br x16`, reaching the donna `_init` (0x3ac = 940) through the table entry, which both
runs read from the library's data in its initial state. The donna `_init` is straight-line:

`bti c; ldp x2, x3, [x1]; stp xzr, xzr, [x0, #0x18]; str xzr, [x0, #0x28];
and x4, x2, #0xfffffffffff; extr x2, x3, x2, #44; and x2, x2, #0xfffffffffff;
and x4, x4, #0xfffffffc0fffffff; and x2, x2, #0xffffffffffc0ffff; stp x4, x2, [x0];
mov x2, #0xfffff0000; movk x2, #0xfc0f; and x3, x2, x3, lsr #24; str x3, [x0, #0x10];
ldr x2, [x1, #0x10]; str x2, [x0, #0x30]; ldr x1, [x1, #0x18]; stp x1, xzr, [x0, #0x38];
strb wzr, [x0, #0x58]; mov w0, #0; ret`.

Every address it touches is `x0` or `x1` plus a constant, so both runs reveal the same addresses;
the key words land in `x1`–`x4` (different in the two runs) and are only stored. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw

open Arm64 Arm64.Obj Leakage
open Poly1305DebianCt (lib arity initPre initPub preSpec ctPublicOk)
open Poly1305Libsodium (bytesIn)

/-! ## Permissions from the precondition -/

/-! ## The run -/

section run
variable {pl : Placement} {ex : String → Option (State → State)}
  (hP : lib.Placeable pl) {m : Memory} (hCL : (P pl ex).CodeLoaded m)
include hP hCL

theorem fI (off : Nat) (i : Instr) (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324)
    (hr : TX.relocAt? off = none) (hd : decode (TX.wordAt off) = some i) :
    (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 off) = some i := by
  rw [fetch_plain hP hCL hal hlen hr, hd]

end run

/-- The step rule with the successors given by equations. -/
theorem oe_mk' {p : Program} {ar : String → Nat} {stop₁ stop₂ : State → Prop}
    (hc : StopCompat stop₁ stop₂) {s0 : State} {pc sp : BitVec 64}
    {r₁ r₂ : BitVec 5 → BitVec 64} {ps₁ ps₂ : PState} {m₁ m₂ : Memory}
    {v₁ v₂ : BitVec 5 → BitVec 128} {i : Instr} {t₁ t₂ : State}
    (hrun : s0.status = .Running) (hCL₁ : p.CodeLoaded m₁) (hCL₂ : p.CodeLoaded m₂)
    (hf₁ : p.fetchMem m₁ pc = some i) (hf₂ : p.fetchMem m₂ pc = some i)
    (hl : leakedValues i (mkS s0 pc r₁ sp ps₁ m₁ v₁) = leakedValues i (mkS s0 pc r₂ sp ps₂ m₂ v₂))
    (e₁ : execInstWithSvc (evalSvc p.svc) i (mkS s0 pc r₁ sp ps₁ m₁ v₁) = t₁)
    (e₂ : execInstWithSvc (evalSvc p.svc) i (mkS s0 pc r₂ sp ps₂ m₂ v₂) = t₂)
    (h : p.CodeLoaded t₁.mem → p.CodeLoaded t₂.mem → ObsEquiv p ar stop₁ stop₂ t₁ t₂) :
    ObsEquiv p ar stop₁ stop₂ (mkS s0 pc r₁ sp ps₁ m₁ v₁) (mkS s0 pc r₂ sp ps₂ m₂ v₂) :=
  oe_mk hc hrun hCL₁ hCL₂ hf₁ hf₂ hl (by rw [e₁, e₂]; exact h)


end Poly1305DebianCtApi

end
end

section
section
/-! # `crypto_onetimeauth_final` is constant-time, given a relational contract of `poly1305_finish`

`crypto_onetimeauth_final` (0x60) dispatches through `implementation` (table entry 4) to the donna
`_final` (0x564 = 1380): `paciasp; stp x29, x30, [sp, #-16]!; mov x29, sp; bl poly1305_finish;
ldp x29, x30, [sp], #16; autiasp; mov w0, #0; ret`.

`poly1305_finish` (0x420 = 1056) is used through `FinishRel`, its relational contract in
continuation-passing form: two runs entering it with equal arguments, `sp`, `lr` and callee-saved
registers, each owning `finishPre` and a frame `Rⱼ`, with equal `leftover`, are observationally
equivalent provided the continuation is, for every pair of returned states that restored the
callee-saved registers and `sp`, kept `Rⱼ`, and kept the code loaded. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw

open Arm64 Arm64.Obj Leakage
open Poly1305DebianCt (lib arity finalPre finishPre leftoverPub preSpec ctPublicOk)
open Poly1305Libsodium (u64At)

/-- What a caller of `poly1305_finish` keeps from one run: the run returned to `lr` with `sp`
restored, kept the callee-saved registers and the code, and its memory holds the frame `R` beside
the 96 state bytes, the 16 tag bytes and the 4128-byte stack frame it was lent. -/
def FinRet (pl : Placement) (ex : String → Option (State → State)) (c : State) (R : SepProp)
    (f : State) : Prop :=
  Returned c f ∧ CalleeSavedPreserved c f ∧ (P pl ex).CodeLoaded f.mem ∧
    (f.mem ⊨ (memRegion (c.readReg64 Reg.x0) 96 ∗ memRegion (c.readReg64 Reg.x1) 16 ∗
      stackFrame c 4128) ∗ R)

/-- The relational contract of `poly1305_finish` (text offset 0x420), in continuation-passing form. -/
def FinishRel (pl : Placement) (ex : String → Option (State → State)) : Prop :=
  ∀ (stop₁ stop₂ : State → Prop), StopCompat stop₁ stop₂ →
  ∀ (x₁ x₂ : List (BitVec 8) × List (BitVec 8)) (R₁ R₂ : SepProp) (c₁ c₂ : State),
    c₁.pc = at_ pl 0x420 → c₂.pc = c₁.pc → c₂.sp = c₁.sp →
    c₁.status = .Running → c₂.status = .Running → c₁.spAligned = true →
    (∀ i : BitVec 5, (i.toNat ≤ 1 ∨ (19 ≤ i.toNat ∧ i.toNat ≤ 30)) → c₂.regs.regs i = c₁.regs.regs i) →
    (P pl ex).CodeLoaded c₁.mem → (P pl ex).CodeLoaded c₂.mem →
    (c₁.mem ⊨ finishPre pl x₁ c₁ ∗ R₁) → (c₂.mem ⊨ finishPre pl x₂ c₂ ∗ R₂) → leftoverPub x₁ x₂ →
    (∀ f₁ f₂ : State, FinRet pl ex c₁ R₁ f₁ → FinRet pl ex c₂ R₂ f₂ →
      ObsEquiv (P pl ex) arity stop₁ stop₂ f₁ f₂) →
    ObsEquiv (P pl ex) arity stop₁ stop₂ c₁ c₂

/-- The step rule on `mkS` pairs over possibly different base states. -/
theorem oe_mk2 {p : Program} {ar : String → Nat} {stop₁ stop₂ : State → Prop}
    (hc : StopCompat stop₁ stop₂) {b₁ b₂ : State} {pc sp : BitVec 64}
    {r₁ r₂ : BitVec 5 → BitVec 64} {ps₁ ps₂ : PState} {m₁ m₂ : Memory}
    {v₁ v₂ : BitVec 5 → BitVec 128} {i : Instr} {t₁ t₂ : State}
    (hrun₁ : b₁.status = .Running) (hrun₂ : b₂.status = .Running)
    (hCL₁ : p.CodeLoaded m₁) (hCL₂ : p.CodeLoaded m₂)
    (hf₁ : p.fetchMem m₁ pc = some i) (hf₂ : p.fetchMem m₂ pc = some i)
    (hl : leakedValues i (mkS b₁ pc r₁ sp ps₁ m₁ v₁) = leakedValues i (mkS b₂ pc r₂ sp ps₂ m₂ v₂))
    (e₁ : execInstWithSvc (evalSvc p.svc) i (mkS b₁ pc r₁ sp ps₁ m₁ v₁) = t₁)
    (e₂ : execInstWithSvc (evalSvc p.svc) i (mkS b₂ pc r₂ sp ps₂ m₂ v₂) = t₂)
    (h : p.CodeLoaded t₁.mem → p.CodeLoaded t₂.mem → ObsEquiv p ar stop₁ stop₂ t₁ t₂) :
    ObsEquiv p ar stop₁ stop₂ (mkS b₁ pc r₁ sp ps₁ m₁ v₁) (mkS b₂ pc r₂ sp ps₂ m₂ v₂) := by
  have st₁ : Step p (mkS b₁ pc r₁ sp ps₁ m₁ v₁) (p.evalInst i (mkS b₁ pc r₁ sp ps₁ m₁ v₁)) :=
    Step.exec hrun₁ hf₁
  have st₂ : Step p (mkS b₂ pc r₂ sp ps₂ m₂ v₂) (p.evalInst i (mkS b₂ pc r₂ sp ps₂ m₂ v₂)) :=
    Step.exec hrun₂ hf₂
  refine oe_exec hc rfl rfl hrun₁ hrun₂ hf₁ hf₂ hl ?_
  have c₁ := Arm64Facts.steps_codeLoaded_v2 (Steps.step st₁ (Steps.refl _)) hCL₁
  have c₂ := Arm64Facts.steps_codeLoaded_v2 (Steps.step st₂ (Steps.refl _)) hCL₂
  have e₁' : p.evalInst i (mkS b₁ pc r₁ sp ps₁ m₁ v₁) = t₁ := e₁
  have e₂' : p.evalInst i (mkS b₂ pc r₂ sp ps₂ m₂ v₂) = t₂ := e₂
  rw [e₁'] at c₁ ⊢; rw [e₂'] at c₂ ⊢
  exact h c₁ c₂

theorem u64At_take96 (st : List (BitVec 8)) : u64At (st.take 96) 64 = u64At st 64 := by
  simp only [u64At, List.drop_take, List.take_take, show min 8 (96 - 64) = 8 from rfl]

/-- One run of `final` up to the call: the memory split the walk uses. -/
theorem final_split {pl : Placement} {x : List (BitVec 8) × List (BitVec 8)} {s : State}
    {R : SepProp} (hp : s.mem ⊨ (finalPre pl x s ∗ lib.dataInit pl) ∗ R) :
    x.1.length = 256 ∧ u64At x.1 64 < 16 ∧ x.2.length = 16 ∧
    ∃ u0 u1 : BitVec 64, s.mem ⊨ ((s.sp - 16#64) ↦₆₄ u0) ∗ ((s.sp - 16#64 + 8#64) ↦₆₄ u1) ∗
      (memRegion (s.sp - BitVec.ofNat 64 4144) 4128 ∗ (s.readReg64 Reg.x0 ↦ₛ x.1) ∗
        (s.readReg64 Reg.x1 ↦ₛ x.2) ∗ (lib.dataInit pl ∗ R)) := by
  obtain ⟨st, mac⟩ := x
  simp only [finalPre] at hp
  have hp' : s.mem ⊨ ⌜st.length = 256 ∧ u64At st 64 < 16 ∧ mac.length = 16⌝ ∗
      (stackFrame s 4144 ∗ ((s.readReg64 Reg.x0 ↦ₛ st) ∗ (s.readReg64 Reg.x1 ↦ₛ mac) ∗
        (lib.dataInit pl ∗ R))) := Satisfies.of_eq hp
  obtain ⟨⟨h1, h2, h3⟩, hs⟩ := sat_pure_sep.mp hp'
  refine ⟨h1, h2, h3, ?_⟩
  have hsf : stackFrame s 4144 = memRegion (s.sp - BitVec.ofNat 64 4144) (4128 + 16) := rfl
  rw [hsf] at hs
  have hs2 := sat_sep_mono hs (memRegion_split _ 4128 16 (by norm_num))
  have eT : s.sp - BitVec.ofNat 64 4144 + BitVec.ofNat 64 4128 = s.sp - 16#64 := by bv_omega
  rw [eT, sepConj_assoc] at hs2
  have hs3 := sat_sep_mono (Satisfies.of_eq hs2 (Q := memRegion (s.sp - 16#64) 16 ∗
    (memRegion (s.sp - BitVec.ofNat 64 4144) 4128 ∗ (s.readReg64 Reg.x0 ↦ₛ st) ∗
      (s.readReg64 Reg.x1 ↦ₛ mac) ∗ (lib.dataInit pl ∗ R)))) (memRegion_eq_cells (s.sp - 16#64))
  rw [sepExists_sepConj, sat_sepExists] at hs3
  obtain ⟨u0, hs3⟩ := hs3
  rw [sepExists_sepConj, sat_sepExists] at hs3
  obtain ⟨u1, hs3⟩ := hs3
  exact ⟨u0, u1, Satisfies.of_eq hs3⟩

/-- The hypotheses of the judgments, for `FinishRel`. -/
def Hyps (pl : Placement) (ex : String → Option (State → State)) : Prop :=
  lib.Placeable pl ∧ Poly1305DebianCt.GuardUniform pl ∧ Poly1305Libsodium.MemzeroOk ex ∧
    Poly1305DebianCt.MemsetOk ex ∧ Link.PlacedLib.LinkOk lib pl ex

set_option maxHeartbeats 4000000 in
theorem ctPublicOk_crypto_onetimeauth_final_of_rel
    (hF : ∀ pl ex, Hyps pl ex → FinishRel pl ex) :
    ctPublicOk "crypto_onetimeauth_final" finalPre leftoverPub := by
  refine ⟨by decide, fun pl hP hG ex hZ hM hL => ?_⟩
  have hFR := hF pl ex ⟨hP, hG, hZ, hM, hL⟩
  intro x₁ x₂ R₁ R₂ s₁ s₂ he₁ he₂ hl₁ hl₂ hp₁ hp₂ hsame hpub
  have e₂ := sameExceptMem_eq hsame
  have hlr : s₁.readReg64 Reg.lr = s₂.readReg64 Reg.lr := by rw [e₂]; rfl
  have hsp : s₁.sp = s₂.sp := by rw [e₂]
  have hc := stopCompat_sub hlr hsp
  obtain ⟨hpc, hrun, hal⟩ := he₁
  have hfa : lib.fnAddr pl "crypto_onetimeauth_final" = at_ pl 0x60 := rfl
  rw [hfa] at hpc
  have D₁ := data_reads pl hp₁
  have D₂ := data_reads pl hp₂
  obtain ⟨hl₁', hlo₁, hm₁, u0, u1, S₁⟩ := final_split hp₁
  obtain ⟨hl₂', hlo₂, hm₂, w0, w1, S₂⟩ := final_split hp₂
  have hx0 : s₂.readReg64 Reg.x0 = s₁.readReg64 Reg.x0 := by rw [e₂]; rfl
  have hx1 : s₂.readReg64 Reg.x1 = s₁.readReg64 Reg.x1 := by rw [e₂]; rfl
  rw [hx0, hx1, ← hsp] at S₂
  have hCL₂ : (P pl ex).CodeLoaded s₂.mem := hl₂
  have hpub' : u64At (x₁.1.take 96) 64 = u64At (x₂.1.take 96) 64 := by
    rw [u64At_take96, u64At_take96]; exact hpub
  set a := s₁.readReg64 Reg.x0 with ha
  set o := s₁.readReg64 Reg.x1 with ho
  set sp0 := s₁.sp with hsp0
  set T := sp0 - 16#64 with hT
  have hal0 : sp0 &&& 0b1111#64 = 0#64 := by simpa [State.spAligned] using hal
  have hTal : T &&& 0b1111#64 = 0#64 := by rw [hT]; exact al16_sub _ 16 (by norm_num) (by norm_num) hal0
  have hlr1 : s₁.readReg64 Reg.lr = s₁.regs.regs 30#5 := by simp [readGpr_unfold, Reg.lr]
  have har : s₁.regs.regs 0#5 = a := by rw [ha]; simp [readGpr_unfold, Reg.x0]
  have hor : s₁.regs.regs 1#5 = o := by rw [ho]; simp [readGpr_unfold, Reg.x1]
  -- both runs as `mkS` over `s₁`
  refine oe_congr (mkS_self s₁).symm (e₂.trans (rfl : { s₁ with mem := s₂.mem } =
    mkS s₁ s₁.pc s₁.regs.regs s₁.sp s₁.pstate s₂.mem s₁.vregs.regs)) ?_
  rw [hpc]
  refine oe_wrap (p := P pl ex) hc (wc_final hP) (by decide) hrun hl₁ hCL₂
    D₁.1.1 D₁.1.2 D₁.2.2.2.2.2.1 D₁.2.2.2.2.2.2 D₂.1.1 D₂.1.2 D₂.2.2.2.2.2.1 D₂.2.2.2.2.2.2 ?_
  rw [show at_ pl 0x564 = pl.base + BitVec.ofNat 64 1380 from rfl]
  set r := upd (upd s₁.regs.regs 2#5 (pl.base + BitVec.ofNat 64 1380)) 16#5
    (pl.base + BitVec.ofNat 64 1380) with hr
  have r0 : r 0#5 = a := by simp [hr, har]
  have r1 : r 1#5 = o := by simp [hr, hor]
  have r29 : r 29#5 = s₁.regs.regs 29#5 := by simp [hr]
  have r30 : r 30#5 = s₁.regs.regs 30#5 := by simp [hr]
  have eT' : sp0 + 0xfffffffffffffff0#64 = T := by rw [hT]; bv_omega
  have c₁0 := sat64_read S₁
  have c₁1 := sat64_read (Satisfies.of_eq S₁ (Q := ((T + 8#64) ↦₆₄ u1) ∗ (T ↦₆₄ u0) ∗
    (memRegion (sp0 - BitVec.ofNat 64 4144) 4128 ∗ (a ↦ₛ x₁.1) ∗ (o ↦ₛ x₁.2) ∗ (lib.dataInit pl ∗ R₁))))
  have c₂0 := sat64_read S₂
  have c₂1 := sat64_read (Satisfies.of_eq S₂ (Q := ((T + 8#64) ↦₆₄ w1) ∗ (T ↦₆₄ w0) ∗
    (memRegion (sp0 - BitVec.ofNat 64 4144) 4128 ∗ (a ↦ₛ x₂.1) ∗ (o ↦ₛ x₂.2) ∗ (lib.dataInit pl ∗ R₂))))
  -- 1380: paciasp
  refine oe_mk' hc hrun hl₁ hCL₂
    (fI hP hl₁ 1380 (.hint 0x19#7) (by decide) (by decide) (by decide) (by rfl))
    (fI hP hCL₂ 1380 (.hint 0x19#7) (by decide) (by decide) (by decide) (by rfl))
    (by simp only [leakedValues]) (ex_hint _) (ex_hint _) fun k₁ k₂ => ?_
  rw [pc_add pl.base 1380 4]
  -- 1384: stp x29, x30, [sp, #-16]!
  refine oe_mk' hc hrun k₁ k₂
    (fI hP k₁ 1384 (.stp .W64 (.gpr 29#5) (.gpr 30#5) (.PreIndex .sp 0xfffffffffffffff0#64))
      (by decide) (by decide) (by decide) (by rfl))
    (fI hP k₂ 1384 (.stp .W64 (.gpr 29#5) (.gpr 30#5) (.PreIndex .sp 0xfffffffffffffff0#64))
      (by decide) (by decide) (by decide) (by rfl))
    (by simp [leakedValues, evalAddrMode])
    (ex_stp64_pre_sp _ _ (by decide) (by decide) _ hal0 (by rw [eT']; exact c₁0.2.2)
      (by rw [eT']; exact c₁1.2.2))
    (ex_stp64_pre_sp _ _ (by decide) (by decide) _ hal0 (by rw [eT']; exact c₂0.2.2)
      (by rw [eT']; exact c₂1.2.2)) fun k₁ k₂ => ?_
  have eT'' : s₁.sp + 0xfffffffffffffff0#64 = T := eT'
  rw [pc_add pl.base 1384 4, eT''] at k₁ k₂ ⊢
  have W₁ := sat64_write (Satisfies.of_eq (sat64_write S₁ (r 29#5)) (Q := ((T + 8#64) ↦₆₄ u1) ∗
    (T ↦₆₄ r 29#5) ∗ (memRegion (sp0 - BitVec.ofNat 64 4144) 4128 ∗ (a ↦ₛ x₁.1) ∗ (o ↦ₛ x₁.2) ∗
      (lib.dataInit pl ∗ R₁)))) (r 30#5)
  have W₂ := sat64_write (Satisfies.of_eq (sat64_write S₂ (r 29#5)) (Q := ((T + 8#64) ↦₆₄ w1) ∗
    (T ↦₆₄ r 29#5) ∗ (memRegion (sp0 - BitVec.ofNat 64 4144) 4128 ∗ (a ↦ₛ x₂.1) ∗ (o ↦ₛ x₂.2) ∗
      (lib.dataInit pl ∗ R₂)))) (r 30#5)
  generalize ((s₁.mem.write64 T (r 29#5)).write64 (T + 8#64) (r 30#5)) = n₁ at W₁ k₁ ⊢
  generalize ((s₂.mem.write64 T (r 29#5)).write64 (T + 8#64) (r 30#5)) = n₂ at W₂ k₂ ⊢
  clear S₁ S₂ c₁0 c₁1 c₂0 c₂1 D₁ D₂ hp₁ hp₂
  -- 1388: mov x29, sp
  refine oe_mk' hc hrun k₁ k₂
    (fI hP k₁ 1388 (.addSubImm .W64 .ADD (.gpr 29#5) .sp 0#12 false) (by decide) (by decide)
      (by decide) (by rfl))
    (fI hP k₂ 1388 (.addSubImm .W64 .ADD (.gpr 29#5) .sp 0#12 false) (by decide) (by decide)
      (by decide) (by rfl))
    (by simp only [leakedValues]) (ex_add_gpr_sp _ (by decide) _) (ex_add_gpr_sp _ (by decide) _)
    fun k₁ k₂ => ?_
  rw [pc_add pl.base 1388 4]
  -- 1392: bl poly1305_finish
  have fbl : ∀ m, (P pl ex).CodeLoaded m → (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 1392) =
      some (.bl 0xfffffffffffffeb0#64) :=
    fun m hm => fI hP hm 1392 _ (by decide) (by decide) (by decide) (by rfl)
  refine oe_mk' hc hrun k₁ k₂ (fbl _ k₁) (fbl _ k₂) (by simp only [leakedValues])
    (ex_bl _) (ex_bl _) fun k₁ k₂ => ?_
  rw [show pl.base + BitVec.ofNat 64 1392 + 0xfffffffffffffeb0#64 = at_ pl 0x420 by
    simp only [at_]; bv_omega]
  -- the call
  set rc := upd (upd r 29#5 (T + (0#12 : BitVec 12).zeroExtend 64)) 30#5
    (pl.base + BitVec.ofNat 64 1392 + 4#64) with hrc
  have rc0 : rc 0#5 = a := by simp [hrc, r0]
  have rc1 : rc 1#5 = o := by simp [hrc, r1]
  have ex0 : (mkS s₁ (at_ pl 0x420) rc T s₁.pstate n₁ s₁.vregs.regs).readReg64 Reg.x0 = a := by
    simp [Reg.x0, rc0]
  have ex1 : (mkS s₁ (at_ pl 0x420) rc T s₁.pstate n₁ s₁.vregs.regs).readReg64 Reg.x1 = o := by
    simp [Reg.x1, rc1]
  have ex0' : (mkS s₁ (at_ pl 0x420) rc T s₁.pstate n₂ s₁.vregs.regs).readReg64 Reg.x0 = a := by
    simp [Reg.x0, rc0]
  have ex1' : (mkS s₁ (at_ pl 0x420) rc T s₁.pstate n₂ s₁.vregs.regs).readReg64 Reg.x1 = o := by
    simp [Reg.x1, rc1]
  have estk : ∀ m, stackFrame (mkS s₁ (at_ pl 0x420) rc T s₁.pstate m s₁.vregs.regs) 4128 =
      memRegion (sp0 - BitVec.ofNat 64 4144) 4128 := by
    intro m
    show memRegion (T - BitVec.ofNat 64 4128) 4128 = _
    rw [show T - BitVec.ofNat 64 4128 = sp0 - BitVec.ofNat 64 4144 by rw [hT]; bv_omega]
  have pre₁ : n₁ ⊨ finishPre pl (x₁.1.take 96, x₁.2)
      (mkS s₁ (at_ pl 0x420) rc T s₁.pstate n₁ s₁.vregs.regs) ∗
      (((a + BitVec.ofNat 64 96) ↦ₛ x₁.1.drop 96) ∗ ((T + 8#64) ↦₆₄ r 30#5) ∗ (T ↦₆₄ r 29#5) ∗
        (lib.dataInit pl ∗ R₁)) := by
    simp only [finishPre]
    rw [ex0, ex1, estk, sepConj_assoc, sat_pure_sep]
    refine ⟨⟨by simp [hl₁'], by rw [u64At_take96]; exact hlo₁, hm₁⟩, ?_⟩
    rw [pointsToBytes_split a x₁.1 96 (by omega)] at W₁
    exact Satisfies.of_eq W₁
  have pre₂ : n₂ ⊨ finishPre pl (x₂.1.take 96, x₂.2)
      (mkS s₁ (at_ pl 0x420) rc T s₁.pstate n₂ s₁.vregs.regs) ∗
      (((a + BitVec.ofNat 64 96) ↦ₛ x₂.1.drop 96) ∗ ((T + 8#64) ↦₆₄ r 30#5) ∗ (T ↦₆₄ r 29#5) ∗
        (lib.dataInit pl ∗ R₂)) := by
    simp only [finishPre]
    rw [ex0', ex1', estk, sepConj_assoc, sat_pure_sep]
    refine ⟨⟨by simp [hl₂'], by rw [u64At_take96]; exact hlo₂, hm₂⟩, ?_⟩
    rw [pointsToBytes_split a x₂.1 96 (by omega)] at W₂
    exact Satisfies.of_eq W₂
  have halc : (mkS s₁ (at_ pl 0x420) rc T s₁.pstate n₁ s₁.vregs.regs).spAligned = true := by
    simp [hTal]
  refine hFR _ _ hc (x₁.1.take 96, x₁.2) (x₂.1.take 96, x₂.2) _ _
    (mkS s₁ (at_ pl 0x420) rc T s₁.pstate n₁ s₁.vregs.regs)
    (mkS s₁ (at_ pl 0x420) rc T s₁.pstate n₂ s₁.vregs.regs) rfl rfl rfl hrun hrun
    halc (fun _ _ => rfl) (show (P pl ex).CodeLoaded n₁ from k₁)
    (show (P pl ex).CodeLoaded n₂ from k₂) pre₁ pre₂ hpub' ?_
  -- after the call
  intro f₁ f₂ F₁ F₂
  obtain ⟨⟨fpc₁, fsp₁, frun₁⟩, _, fk₁, fm₁⟩ := F₁
  obtain ⟨⟨fpc₂, fsp₂, frun₂⟩, _, fk₂, fm₂⟩ := F₂
  simp only [mkS_sp] at fsp₁ fsp₂
  have flr : (mkS s₁ (at_ pl 0x420) rc T s₁.pstate n₁ s₁.vregs.regs).readReg64 Reg.lr =
      pl.base + BitVec.ofNat 64 1396 := by
    simp [Reg.lr, hrc, pc_add]
  have flr' : (mkS s₁ (at_ pl 0x420) rc T s₁.pstate n₂ s₁.vregs.regs).readReg64 Reg.lr =
      pl.base + BitVec.ofNat 64 1396 := by
    simp [Reg.lr, hrc, pc_add]
  rw [flr] at fpc₁; rw [flr'] at fpc₂
  rw [ex0, ex1, estk] at fm₁; rw [ex0', ex1', estk] at fm₂
  have q₁ := Satisfies.of_eq fm₁ (Q := (T ↦₆₄ r 29#5) ∗ ((T + 8#64) ↦₆₄ r 30#5) ∗
    ((memRegion a 96 ∗ memRegion o 16 ∗ memRegion (sp0 - BitVec.ofNat 64 4144) 4128) ∗
      ((a + BitVec.ofNat 64 96) ↦ₛ x₁.1.drop 96) ∗ (lib.dataInit pl ∗ R₁)))
  have q₂ := Satisfies.of_eq fm₂ (Q := (T ↦₆₄ r 29#5) ∗ ((T + 8#64) ↦₆₄ r 30#5) ∗
    ((memRegion a 96 ∗ memRegion o 16 ∗ memRegion (sp0 - BitVec.ofNat 64 4144) 4128) ∗
      ((a + BitVec.ofNat 64 96) ↦ₛ x₂.1.drop 96) ∗ (lib.dataInit pl ∗ R₂)))
  have d₁0 := sat64_read q₁
  have d₁1 := sat64_read (Satisfies.of_eq q₁ (Q := ((T + 8#64) ↦₆₄ r 30#5) ∗ (T ↦₆₄ r 29#5) ∗
    ((memRegion a 96 ∗ memRegion o 16 ∗ memRegion (sp0 - BitVec.ofNat 64 4144) 4128) ∗
      ((a + BitVec.ofNat 64 96) ↦ₛ x₁.1.drop 96) ∗ (lib.dataInit pl ∗ R₁))))
  have d₂0 := sat64_read q₂
  have d₂1 := sat64_read (Satisfies.of_eq q₂ (Q := ((T + 8#64) ↦₆₄ r 30#5) ∗ (T ↦₆₄ r 29#5) ∗
    ((memRegion a 96 ∗ memRegion o 16 ∗ memRegion (sp0 - BitVec.ofNat 64 4144) 4128) ∗
      ((a + BitVec.ofNat 64 96) ↦ₛ x₂.1.drop 96) ∗ (lib.dataInit pl ∗ R₂))))
  refine oe_congr (mkS_self f₁).symm (mkS_self f₂).symm ?_
  rw [fpc₁, fpc₂, fsp₁, fsp₂]
  -- 1396: ldp x29, x30, [sp], #16
  refine oe_mk2 hc frun₁ frun₂ fk₁ fk₂
    (fI hP fk₁ 1396 (.ldp .W64 false (.gpr 29#5) (.gpr 30#5) (.PostIndex .sp 0x10#64))
      (by decide) (by decide) (by decide) (by rfl))
    (fI hP fk₂ 1396 (.ldp .W64 false (.gpr 29#5) (.gpr 30#5) (.PostIndex .sp 0x10#64))
      (by decide) (by decide) (by decide) (by rfl))
    (by simp [leakedValues, evalAddrMode])
    (ex_ldp64_post_sp _ _ (by decide) (by decide) _ hTal d₁0.2.1 d₁1.2.1)
    (ex_ldp64_post_sp _ _ (by decide) (by decide) _ hTal d₂0.2.1 d₂1.2.1) fun k₁ k₂ => ?_
  rw [pc_add pl.base 1396 4, d₁0.1, d₁1.1, d₂0.1, d₂1.1]
  -- 1400: autiasp
  refine oe_mk2 hc frun₁ frun₂ k₁ k₂
    (fI hP k₁ 1400 (.hint 0x1d#7) (by decide) (by decide) (by decide) (by rfl))
    (fI hP k₂ 1400 (.hint 0x1d#7) (by decide) (by decide) (by decide) (by rfl))
    (by simp only [leakedValues]) (ex_hint _) (ex_hint _) fun k₁ k₂ => ?_
  rw [pc_add pl.base 1400 4]
  -- 1404: mov w0, #0
  refine oe_mk2 hc frun₁ frun₂ k₁ k₂
    (fI hP k₁ 1404 (.moveWide .W32 .MOVZ (.gpr 0#5) 0#16 0) (by decide) (by decide) (by decide) (by rfl))
    (fI hP k₂ 1404 (.moveWide .W32 .MOVZ (.gpr 0#5) 0#16 0) (by decide) (by decide) (by decide) (by rfl))
    (by simp only [leakedValues]) (ex_movz32 _ (by decide) _) (ex_movz32 _ (by decide) _) fun k₁ k₂ => ?_
  rw [pc_add pl.base 1404 4]
  -- 1408: ret
  refine oe_mk2 hc frun₁ frun₂ k₁ k₂
    (fI hP k₁ 1408 (.ret (.gpr 30#5)) (by decide) (by decide) (by decide) (by rfl))
    (fI hP k₂ 1408 (.ret (.gpr 30#5)) (by decide) (by decide) (by decide) (by rfl))
    (by simp only [leakedValues]) ex_ret ex_ret fun _ _ => ?_
  have hS : T + 0x10#64 = sp0 := by rw [hT]; bv_omega
  refine oe_stop (Or.inl ⟨?_, ?_, frun₁⟩) (Or.inl ⟨?_, ?_, frun₂⟩)
  · simp [r30, hlr1]
  · simpa using hS
  · simp [r30, ← hlr, hlr1]
  · simp only [mkS_sp]; rw [hS, hsp]

end Poly1305DebianCtApi

end
end

section
section
/-! # `crypto_onetimeauth_final` from the published contract of `poly1305_finish` -/

set_option autoImplicit false

namespace Poly1305DebianCtApi

open Poly1305DebianCt (finalPre leftoverPub ctPublicOk)

theorem ctPublicOk_crypto_onetimeauth_final_dev :
    ctPublicOk "crypto_onetimeauth_final" finalPre leftoverPub :=
  ctPublicOk_crypto_onetimeauth_final_of_rel fun pl ex H =>
    Poly1305DebianCt.relOk_poly1305_finish_v2 pl H.1 H.2.1 ex H.2.2.1 H.2.2.2.1 H.2.2.2.2

end Poly1305DebianCtApi

end
end

section
open Poly1305DebianCt

theorem solution :
    ctPublicOk "crypto_onetimeauth_final" finalPre leftoverPub := by
  apply Poly1305DebianCtApi.ctPublicOk_crypto_onetimeauth_final_dev <;> assumption

end
