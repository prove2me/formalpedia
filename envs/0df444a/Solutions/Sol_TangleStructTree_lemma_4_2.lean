-- Prove2me | solution 1 for TangleStructTree.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:32:19.944652+00:00
-- url     : https://prove2.me/submissions/8a3f34b6-8dc8-4cb6-8856-e8fe0dc9fc93

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_ThoroughlyOrdered
import Theorems.Thm_TangleStructTree_closure_eq
import Theorems.Thm_TangleStructTree_lemma_2_1
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_StronglyEfficient

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TangleStructTree.Dev.Base

open TangleStructTree SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma rev_lt_rev {x y : E} (h : x < y) : rev y < rev x := by
  refine lt_of_le_of_ne (SepSystem.rev_le_rev _ _ h.le) ?_
  intro h'
  have := congrArg rev h'
  rw [rev_rev, rev_rev] at this
  exact h.ne this.symm

lemma le_rev_symm {a b : E} (h : a ≤ rev b) : b ≤ rev a := by
  have := SepSystem.rev_le_rev _ _ h
  rwa [rev_rev] at this

lemma consistent_empty : IsConsistent (∅ : Set E) := fun x hx => absurd hx (by simp)

lemma mem_labels {v : List E} {x : E} : x ∈ labels v ↔ x ∈ v := Iff.rfl

lemma labels_cons (x : E) (v : List E) : labels (x :: v) = insert x (labels v) := by
  ext y; simp [labels]

lemma labels_nil : labels ([] : List E) = ∅ := by
  ext y; simp [labels]

lemma nodes_append (T : SepTree E) : ∀ (a w : List E), a ++ w ∈ T.nodes → w ∈ T.nodes := by
  intro a
  induction a with
  | nil => intro w h; simpa using h
  | cons x a ih => intro w h; exact ih w (T.parent_mem x _ h)

/-- if `v ∈ nodes` and `y ∈ v`, `v = a ++ y :: u`, then `y :: u` and `u` are nodes -/
lemma decomp (T : SepTree E) {v : List E} (hv : v ∈ T.nodes) {y : E} (hy : y ∈ v) :
    ∃ a u, v = a ++ y :: u ∧ y :: u ∈ T.nodes ∧ u ∈ T.nodes := by
  obtain ⟨a, u, h⟩ := List.append_of_mem hy
  subst h
  have h1 := nodes_append T a _ hv
  exact ⟨a, u, rfl, h1, T.parent_mem y u h1⟩

lemma child_not_mem (T : SepTree E) {v : List E} {x : E} (hx : x :: v ∈ T.nodes) :
    x ∉ labels v ∧ rev x ∉ labels v := by
  obtain ⟨s, hs, hsy⟩ := T.split v (T.parent_mem x v hx) ⟨x, hx⟩
  have hxs := (hs x).mp hx
  constructor
  · intro h
    rcases hxs with h1 | h1
    · exact (hsy x h).1 h1
    · exact (hsy x h).2 h1.symm.symm
  · intro h
    rcases hxs with h1 | h1
    · exact (hsy _ h).2 (by rw [h1])
    · exact (hsy _ h).1 (by rw [h1, rev_rev])

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

lemma cl_mono {σ τ : Set E} (h : σ ⊆ τ) (hσ : IsConsistent σ) (hτ : IsConsistent τ) :
    sepClosure σ ⊆ sepClosure τ :=
  (TangleStructTree.lemma_2_1 σ τ h hσ hτ).1

lemma labels_sub_of_append (a : List E) (r : E) (u : List E) :
    labels u ⊆ labels (a ++ r :: u) := by
  intro y hy
  simp only [mem_labels, List.mem_append, List.mem_cons] at hy ⊢
  exact Or.inr (Or.inr hy)

lemma mem_of_append (a : List E) (r : E) (u : List E) : r ∈ labels (a ++ r :: u) := by
  simp [mem_labels]

end TangleStructTree.Dev.Cl
end

section
set_option autoImplicit false

namespace TangleStructTree.Dev.L42

open TangleStructTree SepSystem TangleStructTree.Dev.Base TangleStructTree.Dev.Cl

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma part_i (ord : E → ℝ) (T : SepTree E) (hT : T.ThoroughlyOrdered ord) (v : List E)
    (hv : v ∈ T.nodes) (σ : Set E) (hσ : StronglyEfficient ord σ (sepClosure (labels v))) :
    σ ⊆ labels v := by
  classical
  have hcv := thor_consistent ord T hT v hv
  intro s hs
  by_contra hsv
  have hsC := hσ.1 hs
  obtain ⟨r0, hr0, ⟨-, hr0'⟩, hlt0⟩ := ((mem_cl _ hcv).mp hsC).resolve_left hsv
  -- minimal-depth witness
  let Q : ℕ → Prop := fun k => ∃ (a : List E) (r : E) (u : List E), v = a ++ r :: u ∧
    u.length = k ∧ r < s ∧ r ≠ rev s
  have hQ : ∃ k, Q k := by
    obtain ⟨a, u, h⟩ := List.append_of_mem (show r0 ∈ v from hr0)
    exact ⟨u.length, a, r0, u, h, rfl, hlt0, hr0'⟩
  obtain ⟨a, r, u, hvr, hlen, hrs, hrrs⟩ := Nat.find_spec hQ
  have hnodes : r :: u ∈ T.nodes := nodes_append T a _ (hvr ▸ hv)
  have hu : u ∈ T.nodes := T.parent_mem r u hnodes
  have hcu := thor_consistent ord T hT u hu
  obtain ⟨hno, hmin⟩ := hT u r hnodes
  have hsu : s ∉ labels u := fun h => hsv (hvr ▸ labels_sub_of_append a r u h)
  have hs1 : s ∉ sepClosure (labels u) := by
    intro h
    obtain ⟨r', hr', ⟨-, hr'2⟩, hlt'⟩ := ((mem_cl _ hcu).mp h).resolve_left hsu
    obtain ⟨a', u', h'⟩ := List.append_of_mem (show r' ∈ u from hr')
    have hQ' : Q u'.length := ⟨a ++ r :: a', r', u', by rw [hvr, h']; simp, rfl, hlt', hr'2⟩
    have := Nat.find_min' hQ hQ'
    have h3 : u'.length < u.length := by rw [h']; simp; omega
    omega
  have hs2 : rev s ∉ sepClosure (labels u) := by
    intro h
    have hr'' : ∃ r'' ∈ labels u, r'' ≤ rev s := by
      rcases (mem_cl _ hcu).mp h with h | ⟨r'', h1, -, h3⟩
      · exact ⟨_, h, le_rfl⟩
      · exact ⟨r'', h1, h3.le⟩
    obtain ⟨r'', hr'', hle⟩ := hr''
    have hlt2 : r'' < rev r := lt_of_le_of_lt hle (rev_lt_rev hrs)
    apply hno
    right
    rw [mem_cl _ hcu]
    by_cases hmem : rev r ∈ labels u
    · exact Or.inl hmem
    · refine Or.inr ⟨r'', hr'', ⟨hlt2.ne, ?_⟩, hlt2⟩
      rw [rev_rev]
      intro h
      exact (child_not_mem T hnodes).1 (h ▸ hr'')
  have hord : ord r ≤ ord s := hmin s (fun h => h.elim hs1 hs2)
  have hrC : r ∈ sepClosure (labels v) := sub_cl _ (hvr ▸ mem_of_append a r u)
  exact (hσ.2 s hs r hrC hrs.ne ⟨hrs, hord⟩).elim

lemma part_ii (ord : E → ℝ) (T : SepTree E) (hT : T.ThoroughlyOrdered ord) (v : List E)
    (hv : v ∈ T.nodes) (τ : Set E) (hτ : IsPartialOrientation τ)
    (hsub : sepClosure (labels v) ⊆ τ) : Efficient ord (labels v) τ := by
  have hcv := thor_consistent ord T hT v hv
  refine ⟨fun x hx => hsub (sub_cl _ hx), ?_⟩
  intro x hx y hy hyx ⟨hlt, hord⟩
  obtain ⟨a, u, hvx, hxu, hu⟩ := decomp T hv hx
  have hcu := thor_consistent ord T hT u hu
  obtain ⟨hno, hmin⟩ := hT u x hxu
  have hor : Orients (sepClosure (labels u)) y := by
    by_contra hn
    exact absurd (hmin y hn) (not_le.mpr hord)
  have hsubu : labels u ⊆ labels v := hvx ▸ labels_sub_of_append a x u
  have hCsub : sepClosure (labels u) ⊆ τ := fun z hz =>
    hsub (cl_mono hsubu hcu hcv hz)
  have hyC : y ∈ sepClosure (labels u) := by
    rcases hor with h | h
    · exact h
    · have := hτ y hy (hCsub h)
      rw [this] at h; exact h
  apply hno
  left
  rw [mem_cl _ hcu] at hyC ⊢
  have hrx : rev x ∉ labels u := (child_not_mem T hxu).2
  rcases hyC with hyu | ⟨r', hr', ⟨-, -⟩, hlt'⟩
  · refine Or.inr ⟨y, hyu, ⟨hyx, ?_⟩, hlt⟩
    intro h
    exact hrx (h ▸ hyu)
  · refine Or.inr ⟨r', hr', ⟨(hlt'.trans hlt).ne, ?_⟩, hlt'.trans hlt⟩
    intro h
    exact hrx (h ▸ hr')

end TangleStructTree.Dev.L42

namespace TangleStructTree
open SepSystem TangleStructTree.Dev.L42

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_lemma_4_2 (ord : E → ℝ) (hord : IsOrderFunction ord) (T : SepTree E)
    (hT : T.ThoroughlyOrdered ord) (v : List E) (hv : v ∈ T.nodes) :
    (∀ σ : Set E, StronglyEfficient ord σ (sepClosure (labels v)) → σ ⊆ labels v) ∧
      (IsConsistent (labels v) → ∀ τ : Set E, IsPartialOrientation τ →
        sepClosure (labels v) ⊆ τ → Efficient ord (labels v) τ) :=
  ⟨fun σ hσ => part_i ord T hT v hv σ hσ, fun _ τ hτ hsub => part_ii ord T hT v hv τ hτ hsub⟩

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_lemma_4_2 := @TangleStructTree.chk_lemma_4_2
