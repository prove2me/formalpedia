-- Prove2me | solution 1 for TarchaBraids.prop_3_14_three_braid_alternating_form
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T05:13:56.441587+00:00
-- url     : https://prove2.me/submissions/197e6928-08af-450d-bd18-a63e7c64dd2d

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

open BraidsLinksMCG

/-- One alternating block `σ₁^a σ₂^b` of a 3-braid. -/
private def b3blk (p : ℤ × ℤ) : ArtinBraidGroup 3 :=
  sigma (0 : Fin (3 - 1)) ^ p.1 * sigma (1 : Fin (3 - 1)) ^ p.2

/-- The product of a list of blocks. -/
private def b3pr (l : List (ℤ × ℤ)) : ArtinBraidGroup 3 := (l.map b3blk).prod

/-- The normal-form condition: only the first exponent of `σ₁` and the last exponent of `σ₂`
are allowed to vanish. -/
private def B3Norm (l : List (ℤ × ℤ)) : Prop :=
  (∀ p ∈ l.tail, p.1 ≠ 0) ∧ (∀ p ∈ l.dropLast, p.2 ≠ 0)

private lemma pr_nil : b3pr [] = 1 := rfl

private lemma pr_cons (x : ℤ × ℤ) (t : List (ℤ × ℤ)) : b3pr (x :: t) = b3blk x * b3pr t := rfl

private lemma pr_append (l₁ l₂ : List (ℤ × ℤ)) : b3pr (l₁ ++ l₂) = b3pr l₁ * b3pr l₂ := by
  simp [b3pr]

private lemma norm_cons_iff (x : ℤ × ℤ) (t : List (ℤ × ℤ)) :
    B3Norm (x :: t) ↔
      ((∀ p ∈ t, p.1 ≠ 0) ∧ (t ≠ [] → x.2 ≠ 0) ∧ (∀ p ∈ t.dropLast, p.2 ≠ 0)) := by
  cases t with
  | nil => simp [B3Norm]
  | cons y s =>
      simp only [B3Norm, List.tail_cons, List.dropLast_cons_cons, List.mem_cons, ne_eq,
        List.cons_ne_nil, not_false_eq_true, forall_const]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2 _ (Or.inl rfl), fun p hp => h2 p (Or.inr hp)⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_⟩
        intro p hp
        rcases hp with hp | hp
        · exact hp ▸ h2
        · exact h3 p hp

private lemma norm_tail {x : ℤ × ℤ} {t : List (ℤ × ℤ)} (h : B3Norm (x :: t)) : B3Norm t := by
  obtain ⟨h1, _, h3⟩ := (norm_cons_iff x t).mp h
  exact ⟨fun p hp => h1 p (List.tail_subset t hp), h3⟩

private lemma blk_merge_left (a x1 x2 : ℤ) :
    b3blk (a, (0 : ℤ)) * b3blk (x1, x2) = b3blk (a + x1, x2) := by
  simp [b3blk, zpow_add]
  group

private lemma blk_merge_right (a b c : ℤ) :
    b3blk (a, b) * b3blk ((0 : ℤ), c) = b3blk (a, b + c) := by
  simp [b3blk, zpow_add]
  group

/-- Prepending a block to a list already in normal form, and renormalizing. -/
private lemma b3prepend : ∀ (l : List (ℤ × ℤ)), B3Norm l → ∀ a b : ℤ,
    ∃ l', B3Norm l' ∧ b3pr l' = b3blk (a, b) * b3pr l := by
  intro l
  induction l with
  | nil =>
      intro _ a b
      exact ⟨[(a, b)], by simp [B3Norm], by simp [b3pr]⟩
  | cons x t ih =>
      obtain ⟨x1, x2⟩ := x
      intro hl a b
      obtain ⟨ht1, hx2, ht2⟩ := (norm_cons_iff (x1, x2) t).mp hl
      by_cases hb : b = 0
      · subst hb
        refine ⟨(a + x1, x2) :: t, (norm_cons_iff _ _).mpr ⟨ht1, hx2, ht2⟩, ?_⟩
        rw [pr_cons, pr_cons, ← mul_assoc, blk_merge_left]
      · by_cases ha : x1 = 0
        · subst ha
          obtain ⟨l', hl', hp⟩ := ih (norm_tail hl) a (b + x2)
          refine ⟨l', hl', ?_⟩
          rw [hp, pr_cons, ← mul_assoc, blk_merge_right]
        · refine ⟨(a, b) :: (x1, x2) :: t, ?_, rfl⟩
          refine (norm_cons_iff _ _).mpr ⟨?_, fun _ => hb, hl.2⟩
          intro p hp
          rcases List.mem_cons.mp hp with hp | hp
          · exact hp ▸ ha
          · exact ht1 p hp

private lemma b3normalize : ∀ l : List (ℤ × ℤ), ∃ l', B3Norm l' ∧ b3pr l' = b3pr l := by
  intro l
  induction l with
  | nil => exact ⟨[], by simp [B3Norm], rfl⟩
  | cons x t ih =>
      obtain ⟨l', hl', hp⟩ := ih
      obtain ⟨l'', hl'', hp''⟩ := b3prepend l' hl' x.1 x.2
      exact ⟨l'', hl'', by rw [hp'', hp, pr_cons]⟩

/-- A list whose block product is the inverse of the block product of `l`. -/
private def b3invL : List (ℤ × ℤ) → List (ℤ × ℤ)
  | [] => []
  | p :: t => b3invL t ++ [((0 : ℤ), -p.2), (-p.1, (0 : ℤ))]

private lemma pr_invL : ∀ l : List (ℤ × ℤ), b3pr (b3invL l) = (b3pr l)⁻¹ := by
  intro l
  induction l with
  | nil => simp [b3invL, b3pr]
  | cons x t ih =>
      obtain ⟨x1, x2⟩ := x
      have hpair : b3pr [((0 : ℤ), -x2), (-x1, (0 : ℤ))] = (b3blk (x1, x2))⁻¹ := by
        rw [pr_cons, pr_cons]
        simp [b3blk, mul_inv_rev, pr_nil]
      rw [b3invL, pr_append, ih, hpair, pr_cons, mul_inv_rev]

private def b3Subgroup : Subgroup (ArtinBraidGroup 3) where
  carrier := Set.range b3pr
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro _ _ ⟨l₁, rfl⟩ ⟨l₂, rfl⟩
    exact ⟨l₁ ++ l₂, pr_append l₁ l₂⟩
  inv_mem' := by
    rintro _ ⟨l, rfl⟩
    exact ⟨b3invL l, pr_invL l⟩

private lemma exists_pr (b : ArtinBraidGroup 3) : ∃ l : List (ℤ × ℤ), b = b3pr l := by
  have hgen : Subgroup.closure
      ({sigma (0 : Fin (3 - 1)), sigma (1 : Fin (3 - 1))} : Set (ArtinBraidGroup 3)) = ⊤ := by
    have hrange : (Set.range fun i : Fin (3 - 1) => sigma (n := 3) i)
        = ({sigma (0 : Fin (3 - 1)), sigma (1 : Fin (3 - 1))} : Set (ArtinBraidGroup 3)) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        have hi := i.isLt
        have : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
        rcases this with h | h
        · exact Or.inl (by congr 1; exact Fin.ext h)
        · exact Or.inr (by congr 1; exact Fin.ext h)
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [← hrange]
    exact PresentedGroup.closure_range_of (braidRels 3)
  have hsub : Subgroup.closure
      ({sigma (0 : Fin (3 - 1)), sigma (1 : Fin (3 - 1))} : Set (ArtinBraidGroup 3))
        ≤ b3Subgroup := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨[(1, 0)], by simp [b3pr, b3blk]⟩
    · exact ⟨[(0, 1)], by simp [b3pr, b3blk]⟩
  obtain ⟨l, hl⟩ := hsub (by rw [hgen]; trivial)
  exact ⟨l, hl.symm⟩

theorem solution (b : ArtinBraidGroup 3) :
    ∃ l : List (ℤ × ℤ),
      b = (l.map (fun p =>
            sigma (0 : Fin (3 - 1)) ^ p.1 * sigma (1 : Fin (3 - 1)) ^ p.2)).prod ∧
      (∀ p ∈ l.tail, p.1 ≠ 0) ∧ (∀ p ∈ l.dropLast, p.2 ≠ 0) := by
  obtain ⟨l, hl⟩ := exists_pr b
  obtain ⟨l', hl', hp⟩ := b3normalize l
  exact ⟨l', by rw [hl, ← hp]; rfl, hl'.1, hl'.2⟩
