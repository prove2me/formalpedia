-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P26.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T02:06:33.905224+00:00
-- url     : https://prove2.me/submissions/346d69e1-8ddd-4958-bfed-c8be7a998a2b

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26
noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Renew46.P26

theorem g65d_mono {n : ℕ} (T : YoungTableau n) (l l' : Fin n) (h : T.val l ≤ T.val l') :
    l.val ≤ l'.val := by
  obtain ⟨i, hi, he⟩ := T.property.2 (l'.val + 1) (by omega) h ⟨l', by omega, rfl⟩
  have := T.property.1 he
  subst this; omega

theorem g65d_perm_lt {n : ℕ} (i : Adjacent n) (l k : Fin n) (hlk : l.val < k.val)
    (hbad : ¬ (l = i.val ∧ k = nextPosition i)) :
    (adjacentPerm i l).val < (adjacentPerm i k).val := by
  have hn : (nextPosition i).val = i.val.val + 1 := rfl
  simp only [adjacentPerm, Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp_all [Fin.ext_iff] <;> omega

theorem g65d_valid {n : ℕ} (T : YoungTableau n) (i : Adjacent n)
    (hnot : ¬ (T.val i.val ≤ T.val (nextPosition i))) :
    ∀ m : ℕ, m ≤ n → IsLowerSet {b | ∃ k : Fin n, k.val < m ∧ (T.val ∘ adjacentPerm i) k = b} := by
  intro m hm c d hcd hd
  obtain ⟨k, hk, rfl⟩ := hd
  set k' := adjacentPerm i k with hk'
  have hinv : adjacentPerm i k' = k := by simp [hk', adjacentPerm]
  simp only [Function.comp_apply] at hcd
  obtain ⟨l, hl, rfl⟩ := T.property.2 (k'.val + 1) (by omega) hcd ⟨k', by omega, rfl⟩
  refine ⟨adjacentPerm i l, ?_, by simp [adjacentPerm]⟩
  rcases Nat.lt_or_ge l.val k'.val with hlt | hge
  · have : ¬ (l = i.val ∧ k' = nextPosition i) := by
      rintro ⟨rfl, h2⟩; rw [← hk', h2] at hcd; exact hnot hcd
    have := g65d_perm_lt i l k' hlt this
    rw [hinv] at this; omega
  · have : l = k' := Fin.ext (by omega)
    subst this; rw [hinv]; exact hk

/-- the swapped tableau -/
def g65d_swap {n : ℕ} (T : YoungTableau n) (i : Adjacent n)
    (hnot : ¬ (T.val i.val ≤ T.val (nextPosition i))) : YoungTableau n :=
  ⟨T.val ∘ adjacentPerm i, T.property.1.comp (adjacentPerm i).injective, g65d_valid T i hnot⟩

theorem g65d_step {n : ℕ} (T : YoungTableau n) (i : Adjacent n)
    (hnot : ¬ (T.val i.val ≤ T.val (nextPosition i))) : TableauStep T (g65d_swap T i hnot) := by
  have hnot2 : ¬ (T.val (nextPosition i) ≤ T.val i.val) := by
    intro h; have := g65d_mono T _ _ h; simp [nextPosition] at this
  refine ⟨i, ?_, ?_, rfl⟩
  · intro h; rcases le_total (T.val i.val).2 (T.val (nextPosition i)).2 with h' | h'
    · exact hnot (Prod.le_def.mpr ⟨h.le, h'⟩)
    · exact hnot2 (Prod.le_def.mpr ⟨h.ge, h'⟩)
  · intro h; rcases le_total (T.val i.val).1 (T.val (nextPosition i)).1 with h' | h'
    · exact hnot (Prod.le_def.mpr ⟨h', h.le⟩)
    · exact hnot2 (Prod.le_def.mpr ⟨h', h.ge⟩)

theorem g65d_move {n k : ℕ} (hk : k < n) (U : YoungTableau n) :
    ∀ d : ℕ, ∀ (T : YoungTableau n) (j : Fin n), j.val + d = k → T.val j = U.val ⟨k, hk⟩ →
      Finset.univ.image T.val = Finset.univ.image U.val →
      (∀ l : Fin n, k < l.val → T.val l = U.val l) →
      ∃ T' : YoungTableau n, Relation.ReflTransGen TableauStep T T' ∧
        T'.val ⟨k, hk⟩ = U.val ⟨k, hk⟩ ∧ Finset.univ.image T'.val = Finset.univ.image U.val ∧
        (∀ l : Fin n, k < l.val → T'.val l = U.val l) := by
  intro d
  induction d with
  | zero =>
    intro T j hj hTj him hag
    have : j = ⟨k, hk⟩ := Fin.ext (by simpa using hj)
    subst this
    exact ⟨T, Relation.ReflTransGen.refl, hTj, him, hag⟩
  | succ d ih =>
    intro T j hj hTj him hag
    let i : Adjacent n := ⟨j, by omega⟩
    have hnext : (nextPosition i).val = j.val + 1 := rfl
    have hmem : T.val (nextPosition i) ∈ Finset.univ.image U.val := by
      rw [← him]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    obtain ⟨l', -, hl'⟩ := Finset.mem_image.mp hmem
    have hl'k : l'.val ≤ k := by
      by_contra hc
      have h1 := hag l' (by omega)
      rw [hl'] at h1
      have := T.property.1 h1
      rw [this] at hc; omega
    have hnot : ¬ (T.val i.val ≤ T.val (nextPosition i)) := by
      intro hle
      change T.val j ≤ _ at hle
      rw [hTj, ← hl'] at hle
      have h1 := g65d_mono U _ _ hle
      have h2 : l' = ⟨k, hk⟩ := Fin.ext (by simp at h1 ⊢; omega)
      rw [h2, ← hTj] at hl'
      have := T.property.1 hl'
      have := congrArg Fin.val this
      rw [hnext] at this; omega
    set T1 := g65d_swap T i hnot with hT1
    have hT1v : T1.val = T.val ∘ adjacentPerm i := rfl
    have hT1n : T1.val (nextPosition i) = U.val ⟨k, hk⟩ := by
      rw [hT1v, Function.comp_apply, adjacentPerm, Equiv.swap_apply_right]; exact hTj
    have him1 : Finset.univ.image T1.val = Finset.univ.image U.val := by
      rw [← him]; ext b; simp only [Finset.mem_image, Finset.mem_univ, true_and, hT1v,
        Function.comp_apply]
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨a, rfl⟩; exact ⟨adjacentPerm i a, by simp [adjacentPerm]⟩
    have hag1 : ∀ l : Fin n, k < l.val → T1.val l = U.val l := by
      intro l hl
      rw [hT1v, Function.comp_apply, adjacentPerm, Equiv.swap_apply_of_ne_of_ne]
      · exact hag l hl
      · intro h; rw [h] at hl; change k < j.val at hl; omega
      · intro h; rw [h, hnext] at hl; omega
    obtain ⟨T', h1, h2, h3, h4⟩ := ih T1 (nextPosition i) (by rw [hnext]; omega) hT1n him1 hag1
    exact ⟨T', Relation.ReflTransGen.head (g65d_step T i hnot) h1, h2, h3, h4⟩

theorem g65d_main {n : ℕ} : ∀ k : ℕ, ∀ T U : YoungTableau n,
    Finset.univ.image T.val = Finset.univ.image U.val →
    (∀ l : Fin n, k ≤ l.val → T.val l = U.val l) → Relation.ReflTransGen TableauStep T U := by
  intro k
  induction k with
  | zero =>
    intro T U _ hag
    have : T = U := Subtype.ext (funext fun l => hag l (Nat.zero_le _))
    subst this; exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro T U him hag
    by_cases hk : k < n
    · have hmem : U.val ⟨k, hk⟩ ∈ Finset.univ.image T.val := by
        rw [him]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
      have hjk : j.val ≤ k := by
        by_contra hc
        have h1 := hag j (by omega)
        rw [hj] at h1
        have := congrArg Fin.val (U.property.1 h1)
        simp at this; omega
      obtain ⟨T', h1, h2, h3, h4⟩ := g65d_move hk U (k - j.val) T j (by omega) hj him
        (fun l hl => hag l hl)
      refine h1.trans (ih T' U h3 (fun l hl => ?_))
      rcases Nat.eq_or_lt_of_le hl with h | h
      · have : l = ⟨k, hk⟩ := Fin.ext h.symm
        rw [this]; exact h2
      · exact h4 l h
    · exact ih T U him (fun l hl => by omega)


theorem solution {n : ℕ} (T U : YoungTableau n) (h : tableauShape T = tableauShape U) :
    Relation.ReflTransGen TableauStep T U := by
  have him : Finset.univ.image T.val = Finset.univ.image U.val := congrArg YoungDiagram.cells h
  exact g65d_main n T U him (fun l hl => by have := l.isLt; omega)

end
