-- Prove2me | solution 1 for TangleStructTree.theorem_4_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:55:42.732498+00:00
-- url     : https://prove2.me/submissions/4ea2e42e-4d7f-49b2-852a-889f525351b1

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_ThoroughlyOrdered
import Theorems.Thm_TangleStructTree_closure_eq
import Definitions.Def_TangleStructTree_IsTrivial
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_IsStandard
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_StronglyEfficient
import Definitions.Def_TangleStructTree_IsRich
import Definitions.Def_TangleStructTree_SepTree_Consistent
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Definitions.Def_TangleStructTree_OrderInjective
import Theorems.Thm_TangleStructTree_lemma_4_5

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TangleStructTree.Dev.Base

open TangleStructTree SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma le_rev_symm {a b : E} (h : a ≤ rev b) : b ≤ rev a := by
  have := SepSystem.rev_le_rev _ _ h
  rwa [rev_rev] at this

lemma consistent_empty : IsConsistent (∅ : Set E) := fun x hx => absurd hx (by simp)

lemma labels_cons (x : E) (v : List E) : labels (x :: v) = insert x (labels v) := by
  ext y; simp [labels]

lemma labels_nil : labels ([] : List E) = ∅ := by
  ext y; simp [labels]

lemma pairwise_path (T : SepTree E) :
    ∀ v ∈ T.nodes, v.Pairwise (fun a b => a ≠ b ∧ a ≠ rev b) := by
  intro v
  induction v with
  | nil => intro _; exact List.Pairwise.nil
  | cons x u ih =>
    intro h
    have hu := T.parent_mem x u h
    refine List.pairwise_cons.mpr ⟨?_, ih hu⟩
    obtain ⟨s, hs, hy⟩ := T.split u hu ⟨x, h⟩
    intro y hy'
    have hxs := (hs x).mp h
    obtain ⟨h1, h2⟩ := hy y hy'
    rcases hxs with rfl | rfl
    · exact ⟨fun h => h1 h.symm, fun h => h2 (by rw [h, rev_rev])⟩
    · refine ⟨fun h => h2 h.symm, fun h => h1 ?_⟩
      have := congrArg rev h
      simp only [rev_rev] at this
      exact this.symm

end TangleStructTree.Dev.Base
end

section
set_option autoImplicit false

namespace TangleStructTree.Dev.Cl

open TangleStructTree SepSystem TangleStructTree.Dev.Base

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma mem_cl (τ : Set E) (hτ : IsConsistent τ) {x : E} :
    x ∈ sepClosure τ ↔ x ∈ τ ∨ ∃ r ∈ τ, (r ≠ x ∧ r ≠ rev x) ∧ r < x := by
  rw [(TangleStructTree.closure_eq τ hτ).2]
  simp [Set.mem_union]

lemma sub_cl (τ : Set E) : τ ⊆ sepClosure τ := fun _ h => Or.inl h

lemma not_orients_mem {τ : Set E} {x : E} (h : ¬ Orients τ x) : x ∉ τ ∧ rev x ∉ τ :=
  ⟨fun h' => h (Or.inl h'), fun h' => h (Or.inr h')⟩

lemma thor_consistent (ord : E → ℝ) (T : SepTree E) (hT : T.ThoroughlyOrdered ord) :
    ∀ v ∈ T.nodes, IsConsistent (labels v) := by
  intro v
  induction v with
  | nil => intro _; rw [labels_nil]; exact consistent_empty
  | cons x u ih =>
    intro hx
    have hu := T.parent_mem x u hx
    have hβ := ih hu
    obtain ⟨hno, -⟩ := hT u x hx
    obtain ⟨hx1, hx2⟩ := not_orients_mem hno
    have hxβ : x ∉ labels u := fun h => hx1 (sub_cl _ h)
    have hrxβ : rev x ∉ labels u := fun h => hx2 (sub_cl _ h)
    -- no element of β is below x or rev x
    have h1 : ∀ r ∈ labels u, r ≠ x → r ≠ rev x → ¬ r < x := by
      intro r hr h1 h2 hlt
      exact hx1 ((mem_cl _ hβ).mpr (Or.inr ⟨r, hr, ⟨h1, h2⟩, hlt⟩))
    have h2 : ∀ r ∈ labels u, r ≠ rev x → r ≠ x → ¬ r < rev x := by
      intro r hr h1 h2 hlt
      exact hx2 ((mem_cl _ hβ).mpr (Or.inr ⟨r, hr, ⟨h1, by rw [rev_rev]; exact h2⟩, hlt⟩))
    rw [labels_cons]
    intro a ha b hb hba hbra hab
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hba (hb.trans ha.symm)
    · have h3 : b ≤ rev x := by rw [← ha]; exact le_rev_symm hab
      have h4 : b ≠ rev x := fun h => hrxβ (h ▸ hb)
      exact h2 b hb h4 (fun h => hba (h.trans ha.symm)) (lt_of_le_of_ne h3 h4)
    · have h3 : a ≤ rev x := by rw [← hb]; exact hab
      have h4 : a ≠ rev x := fun h => hrxβ (h ▸ ha)
      exact h2 a ha h4 (fun h => hba (hb.trans h.symm)) (lt_of_le_of_ne h3 h4)
    · exact hβ a ha b hb hba hbra hab

end TangleStructTree.Dev.Cl
end

section
set_option autoImplicit false

namespace TangleStructTree.Dev.T46

open TangleStructTree SepSystem TangleStructTree.Dev.Base TangleStructTree.Dev.Cl

open Classical in
/-- the tree obtained by splitting a leaf `ℓ` along `y` -/
noncomputable def extend {E : Type*} [PartialOrder E] [SepSystem E] (T : SepTree E) (ℓ : List E) (y : E) (hℓ : T.IsLeaf ℓ)
    (hy : ∀ z ∈ labels ℓ, z ≠ y ∧ z ≠ rev y) : SepTree E where
  nodes := insert (y :: ℓ) (insert (rev y :: ℓ) T.nodes)
  root_mem := by
    simp only [Finset.mem_insert]
    exact Or.inr (Or.inr T.root_mem)
  parent_mem := by
    intro x v hxv
    simp only [Finset.mem_insert] at hxv ⊢
    rcases hxv with h | h | h
    · have := (List.cons.inj h).2; rw [this]; exact Or.inr (Or.inr hℓ.1)
    · have := (List.cons.inj h).2; rw [this]; exact Or.inr (Or.inr hℓ.1)
    · exact Or.inr (Or.inr (T.parent_mem x v h))
  split := by
    intro v hv hex
    simp only [Finset.mem_insert] at hv hex
    by_cases hvℓ : v = ℓ
    · subst hvℓ
      refine ⟨y, ?_, hy⟩
      intro x
      simp only [Finset.mem_insert]
      constructor
      · rintro (h | h | h)
        · exact Or.inl (List.cons.inj h).1
        · exact Or.inr (List.cons.inj h).1
        · exact absurd h (hℓ.2 x)
      · rintro (h | h)
        · exact Or.inl (by rw [h])
        · exact Or.inr (Or.inl (by rw [h]))
    · have hvT : v ∈ T.nodes := by
        rcases hv with h | h | h
        · exfalso
          obtain ⟨x, hx⟩ := hex
          rcases hx with hx | hx | hx
          · have := congrArg List.length hx; subst h; simp at this
          · have := congrArg List.length hx; subst h; simp at this
          · exact hℓ.2 y (by rw [h] at hx; exact T.parent_mem x _ hx)
        · exfalso
          obtain ⟨x, hx⟩ := hex
          rcases hx with hx | hx | hx
          · have := congrArg List.length hx; subst h; simp at this
          · have := congrArg List.length hx; subst h; simp at this
          · exact hℓ.2 (rev y) (by rw [h] at hx; exact T.parent_mem x _ hx)
        · exact h
      have hiff : ∀ x, x :: v ∈ insert (y :: ℓ) (insert (rev y :: ℓ) T.nodes) ↔ x :: v ∈ T.nodes := by
        intro x
        simp only [Finset.mem_insert]
        constructor
        · rintro (h | h | h)
          · exact absurd (List.cons.inj h).2 hvℓ
          · exact absurd (List.cons.inj h).2 hvℓ
          · exact h
        · intro h; exact Or.inr (Or.inr h)
      obtain ⟨x0, hx0⟩ := hex
      have hex' : ∃ x, x :: v ∈ T.nodes := ⟨x0, (hiff x0).mp (by simpa only [Finset.mem_insert] using hx0)⟩
      obtain ⟨s, hs, hsy⟩ := T.split v hvT hex'
      exact ⟨s, fun x => by rw [hiff]; exact hs x, hsy⟩


variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma mem_extend {T : SepTree E} {ℓ : List E} {y : E} {hℓ : T.IsLeaf ℓ}
    {hy : ∀ z ∈ labels ℓ, z ≠ y ∧ z ≠ rev y} {v : List E} :
    v ∈ (extend T ℓ y hℓ hy).nodes ↔ v = y :: ℓ ∨ v = rev y :: ℓ ∨ v ∈ T.nodes := by
  simp [extend]

lemma extend_thor (ord : E → ℝ) (hord : IsOrderFunction ord) (T : SepTree E) (ℓ : List E) (y : E)
    (hℓ : T.IsLeaf ℓ) (hy : ∀ z ∈ labels ℓ, z ≠ y ∧ z ≠ rev y)
    (hthor : T.ThoroughlyOrdered ord) (hy0 : ¬ Orients (sepClosure (labels ℓ)) y)
    (hmin : ∀ z, ¬ Orients (sepClosure (labels ℓ)) z → ord y ≤ ord z) :
    (extend T ℓ y hℓ hy).ThoroughlyOrdered ord := by
  intro v x hx
  rcases mem_extend.mp hx with h | h | h
  · obtain ⟨h1, h2⟩ := List.cons.inj h
    subst h1; subst h2
    exact ⟨hy0, hmin⟩
  · obtain ⟨h1, h2⟩ := List.cons.inj h
    subst h1; subst h2
    refine ⟨fun h => hy0 ?_, fun z hz => ?_⟩
    · rcases h with h | h
      · exact Or.inr h
      · rw [rev_rev] at h; exact Or.inl h
    · rw [hord y]; exact hmin z hz
  · exact hthor v x h

lemma extend_avoid (ℱ : Set (Set E)) (T : SepTree E) (ℓ : List E) (y : E)
    (hℓ : T.IsLeaf ℓ) (hy : ∀ z ∈ labels ℓ, z ≠ y ∧ z ≠ rev y)
    (hav : ∀ (v : List E) (x : E), x :: v ∈ T.nodes → Avoids ℱ (labels v))
    (hℓav : Avoids ℱ (labels ℓ)) :
    ∀ (v : List E) (x : E), x :: v ∈ (extend T ℓ y hℓ hy).nodes → Avoids ℱ (labels v) := by
  intro v x hx
  rcases mem_extend.mp hx with h | h | h
  · obtain ⟨-, h2⟩ := List.cons.inj h
    subst h2; exact hℓav
  · obtain ⟨-, h2⟩ := List.cons.inj h
    subst h2; exact hℓav
  · exact hav v x h

lemma extend_card (T : SepTree E) (ℓ : List E) (y : E)
    (hℓ : T.IsLeaf ℓ) (hy : ∀ z ∈ labels ℓ, z ≠ y ∧ z ≠ rev y) :
    T.nodes.card < (extend T ℓ y hℓ hy).nodes.card := by
  apply Finset.card_lt_card
  refine ⟨fun v hv => mem_extend.mpr (Or.inr (Or.inr hv)), fun hsub => ?_⟩
  have : y :: ℓ ∈ (extend T ℓ y hℓ hy).nodes := mem_extend.mpr (Or.inl rfl)
  exact hℓ.2 y (hsub this)

/-- one step of the construction -/
lemma step (ord : E → ℝ) (hord : IsOrderFunction ord) [Finite E] (ℱ : Set (Set E))
    (hrich : IsRich ord ℱ) (hstd : IsStandard ℱ) (T : SepTree E)
    (hthor : T.ThoroughlyOrdered ord)
    (hav : ∀ (v : List E) (x : E), x :: v ∈ T.nodes → Avoids ℱ (labels v))
    (hnot : ¬ T.IsTST ℱ) :
    ∃ T' : SepTree E, T'.ThoroughlyOrdered ord ∧
      (∀ (v : List E) (x : E), x :: v ∈ T'.nodes → Avoids ℱ (labels v)) ∧
      T.nodes.card < T'.nodes.card := by
  have hcons : T.Consistent := thor_consistent ord T hthor
  have : ∃ ℓ, T.IsLeaf ℓ ∧ ¬ T.IsTangleLeaf ℱ ℓ ∧ ¬ T.IsForbiddenLeaf ℱ ℓ := by
    by_contra hcon
    push_neg at hcon
    exact hnot ⟨hcons, fun ℓ hℓ => by
      by_cases h : T.IsTangleLeaf ℱ ℓ
      · exact Or.inl h
      · exact Or.inr (by_contra fun h' => absurd (hcon ℓ hℓ h) h'), hav⟩
  obtain ⟨ℓ, hℓ, hntl, hnf⟩ := this
  have hℓav : Avoids ℱ (labels ℓ) := by
    by_contra h; exact hnf ⟨hℓ, h⟩
  have hcℓ := hcons ℓ hℓ.1
  have hex : ∃ y, ¬ Orients (sepClosure (labels ℓ)) y := by
    by_contra hall
    push_neg at hall
    exact hntl ⟨hℓ, TangleStructTree.lemma_4_5 ord hord ℱ hrich hstd T hthor ℓ hℓ.1 hcℓ hℓav hall⟩
  obtain ⟨y, hyU, hymin⟩ := Set.exists_min_image {y : E | ¬ Orients (sepClosure (labels ℓ)) y}
    ord (Set.toFinite _) hex
  have hy : ∀ z ∈ labels ℓ, z ≠ y ∧ z ≠ rev y := by
    intro z hz
    constructor
    · rintro rfl; exact hyU (Or.inl (sub_cl _ hz))
    · rintro rfl; exact hyU (Or.inr (sub_cl _ hz))
  exact ⟨extend T ℓ y hℓ hy, extend_thor ord hord T ℓ y hℓ hy hthor hyU hymin,
    extend_avoid ℱ T ℓ y hℓ hy hav hℓav, extend_card T ℓ y hℓ hy⟩

lemma card_bound [Finite E] (T : SepTree E) :
    T.nodes.card ≤ (List.finite_length_le E (Nat.card E)).toFinset.card := by
  classical
  haveI := Fintype.ofFinite E
  apply Finset.card_le_card
  intro v hv
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hpw := pairwise_path T v hv
  have hnd : v.Nodup := hpw.imp (fun h => h.1)
  rw [Nat.card_eq_fintype_card]
  exact hnd.length_le_card

end TangleStructTree.Dev.T46

namespace TangleStructTree
open SepSystem TangleStructTree.Dev.T46

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_theorem_4_6 [Finite E] (ord : E → ℝ) (hord : IsOrderFunction ord) (ℱ : Set (Set E))
    (hrich : IsRich ord ℱ) (hstd : IsStandard ℱ) :
    ∃ T : SepTree E, T.ThoroughlyOrdered ord ∧ T.IsTST ℱ := by
  classical
  by_contra hno
  push_neg at hno
  let T0 : SepTree E :=
    { nodes := {[]}
      root_mem := by simp
      parent_mem := by
        intro x v h
        simp at h
      split := by
        intro v hv hex
        obtain ⟨x, hx⟩ := hex
        simp at hv hx }
  have hgrow : ∀ k : ℕ, ∃ T : SepTree E, T.ThoroughlyOrdered ord ∧
      (∀ (v : List E) (x : E), x :: v ∈ T.nodes → Avoids ℱ (labels v)) ∧ k ≤ T.nodes.card := by
    intro k
    induction k with
    | zero =>
      refine ⟨T0, ?_, ?_, Nat.zero_le _⟩
      · intro v x hx; simp [T0] at hx
      · intro v x hx; simp [T0] at hx
    | succ k ih =>
      obtain ⟨T, h1, h2, h3⟩ := ih
      obtain ⟨T', h1', h2', h3'⟩ := step ord hord ℱ hrich hstd T h1 h2 (fun h => hno T h1 h)
      exact ⟨T', h1', h2', by omega⟩
  obtain ⟨T, -, -, hk⟩ := hgrow ((List.finite_length_le E (Nat.card E)).toFinset.card + 1)
  have := card_bound T
  omega

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_theorem_4_6 := @TangleStructTree.chk_theorem_4_6
