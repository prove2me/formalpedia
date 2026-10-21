-- Prove2me | solution 1 for OnlineCRS.Submod.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:35:17.493984+00:00
-- url     : https://prove2.me/submissions/c2776d79-5c54-4ba4-8de7-2f4924156bd1

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

set_option autoImplicit false

open NonmonotoneSubmod.Shared

section Aux
variable {α : Type} [Fintype α] [DecidableEq α]

def ChainP (g : Finset α → ℝ) (T : Finset α) (δ : α → ℝ) : Prop :=
  ∀ B ⊆ T, g ∅ + ∑ e ∈ B, δ e ≤ g B

lemma chainP_insert (g : Finset α → ℝ) (hg : Submodular g) {T : Finset α} {a : α} (ha : a ∉ T)
    {δ : α → ℝ} (h : ChainP g T δ) :
    ChainP g (insert a T) (Function.update δ a (g (insert a T) - g T)) := by
  intro B hB
  by_cases haB : a ∈ B
  · set B' := B.erase a with hB'
    have hBB : B = insert a B' := (Finset.insert_erase haB).symm
    have hB'T : B' ⊆ T := by
      intro x hx
      have hx' := Finset.mem_erase.1 hx
      have := hB hx'.2
      rcases Finset.mem_insert.1 this with h1 | h1
      · exact absurd h1 hx'.1
      · exact h1
    have haB' : a ∉ B' := by simp [hB']
    have h1 := h B' hB'T
    have h2 := hg (insert a B') T
    have e1 : insert a B' ∪ T = insert a T := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (hB'T h)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    have e2 : insert a B' ∩ T = B' := by
      ext x; simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨h | h, hT⟩
        · exact absurd (h ▸ hT) ha
        · exact h
      · intro h; exact ⟨Or.inr h, hB'T h⟩
    rw [e1, e2] at h2
    have hs : ∑ e ∈ insert a B', Function.update δ a (g (insert a T) - g T) e
        = (g (insert a T) - g T) + ∑ e ∈ B', δ e := by
      rw [Finset.sum_insert haB', Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      exact Function.update_of_ne (by rintro rfl; exact haB' hx) _ _
    rw [hBB, hs]
    linarith
  · have hBT : B ⊆ T := by
      intro x hx
      rcases Finset.mem_insert.1 (hB hx) with h1 | h1
      · exact absurd (h1 ▸ hx) haB
      · exact h1
    have hs : ∑ e ∈ B, Function.update δ a (g (insert a T) - g T) e = ∑ e ∈ B, δ e := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Function.update_of_ne (by rintro rfl; exact haB hx) _ _
    rw [hs]
    exact h B hBT

lemma chainP_sum (g : Finset α → ℝ) (hg : Submodular g) (T : Finset α) :
    ∃ δ : α → ℝ, ChainP g T δ ∧ ∑ e ∈ T, δ e = g T - g ∅ := by
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, ?_, by simp⟩
    intro B hB
    have : B = ∅ := Finset.subset_empty.1 hB
    subst this; simp
  | insert a T ha ih =>
    obtain ⟨δ, hδ, hsum⟩ := ih
    refine ⟨_, chainP_insert g hg ha hδ, ?_⟩
    rw [Finset.sum_insert ha, Function.update_self]
    have : ∑ e ∈ T, Function.update δ a (g (insert a T) - g T) e = ∑ e ∈ T, δ e := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Function.update_of_ne (by rintro rfl; exact ha hx) _ _
    rw [this, hsum]; ring

/-- expectation of a chain bound -/
lemma chainP_expect (g : Finset α → ℝ) (T : Finset α) (δ : α → ℝ) (h : ChainP g T δ)
    (μ : Finset α → ℝ) (hμ0 : ∀ B, 0 ≤ μ B) (hμ1 : ∑ B : Finset α, μ B = 1)
    (hμT : ∀ B, μ B ≠ 0 → B ⊆ T) :
    g ∅ + ∑ e ∈ T, δ e * (∑ B : Finset α, μ B * (if e ∈ B then 1 else 0)) ≤ ∑ B : Finset α, μ B * g B := by
  have key : ∀ B : Finset α, μ B * (g ∅ + ∑ e ∈ B, δ e) ≤ μ B * g B := by
    intro B
    by_cases hB : μ B = 0
    · simp [hB]
    · exact mul_le_mul_of_nonneg_left (h B (hμT B hB)) (hμ0 B)
  have lhs : ∑ B : Finset α, μ B * (g ∅ + ∑ e ∈ B, δ e)
      = g ∅ + ∑ e ∈ T, δ e * (∑ B : Finset α, μ B * (if e ∈ B then 1 else 0)) := by
    have h1 : ∀ B : Finset α, μ B * (g ∅ + ∑ e ∈ B, δ e)
        = μ B * g ∅ + ∑ e ∈ T, δ e * (μ B * (if e ∈ B then 1 else 0)) := by
      intro B
      by_cases hB : μ B = 0
      · simp [hB]
      · have hBT := hμT B hB
        have : ∑ e ∈ B, δ e = ∑ e ∈ T, δ e * (if e ∈ B then 1 else 0) := by
          rw [← Finset.sum_subset hBT (by
            intro x _ hx; simp [hx])]
          · apply Finset.sum_congr rfl
            intro x hx; simp [hx]
        · rw [mul_add, this, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro x _; ring
    rw [Finset.sum_congr rfl (fun B _ => h1 B), Finset.sum_add_distrib, ← Finset.sum_mul, hμ1,
      one_mul, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.mul_sum]
  rw [← lhs]
  exact Finset.sum_le_sum (fun B _ => key B)

end Aux

section Aux2
variable {α : Type} [Fintype α] [DecidableEq α]

/-- ordered Abel-summation bound: elements added in order of decreasing weight `q` -/
lemma chainP_abel (g : Finset α → ℝ) (hg : Submodular g) (hg0 : ∀ S, 0 ≤ g S) (q : α → ℝ) :
    ∀ n : ℕ, ∀ T : Finset α, T.card = n → ∃ δ : α → ℝ, ChainP g T δ ∧
      ∀ m u : ℝ, m ≤ u → (∀ e ∈ T, m ≤ q e ∧ q e ≤ u) →
        m * g T - u * g ∅ ≤ ∑ e ∈ T, δ e * q e := by
  intro n
  induction n with
  | zero =>
    intro T hT
    have : T = ∅ := Finset.card_eq_zero.1 hT
    subst this
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro B hB
      have : B = ∅ := Finset.subset_empty.1 hB
      subst this; simp
    · intro m u hmu _
      simp only [Finset.sum_empty]
      nlinarith [hg0 ∅]
  | succ n ih =>
    intro T hT
    have hne : T.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨a, haT, hmin⟩ := Finset.exists_min_image T q hne
    have hcard : (T.erase a).card = n := by rw [Finset.card_erase_of_mem haT]; omega
    obtain ⟨δ, hδ, hb⟩ := ih (T.erase a) hcard
    have haT' : a ∉ T.erase a := by simp
    have hch := chainP_insert g hg haT' hδ
    rw [Finset.insert_erase haT] at hch
    refine ⟨_, hch, ?_⟩
    intro m u hmu hmq
    have hs : ∑ e ∈ T, Function.update δ a (g T - g (T.erase a)) e * q e
        = (g T - g (T.erase a)) * q a + ∑ e ∈ T.erase a, δ e * q e := by
      rw [← Finset.add_sum_erase T _ haT, Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      rw [Function.update_of_ne (by rintro rfl; exact haT' hx)]
    have hqa := hmq a haT
    have := hb (q a) u (hqa.2) (by
      intro e he
      exact ⟨hmin e (Finset.mem_of_mem_erase he), (hmq e (Finset.mem_of_mem_erase he)).2⟩)
    rw [hs]
    have h1 : m * g T ≤ q a * g T := mul_le_mul_of_nonneg_right hqa.1 (hg0 T)
    nlinarith

end Aux2

open Classical in
theorem solution {α : Type} [Fintype α] [DecidableEq α] (g : Finset α → ℝ) (hg0 : ∀ S, 0 ≤ g S)
    (hg : NonmonotoneSubmod.Shared.Submodular g) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (μ : Finset α → ℝ) (hμ0 : ∀ B, 0 ≤ μ B) (hμ1 : ∑ B : Finset α, μ B = 1)
    (hμp : ∀ e : α, ∑ B : Finset α, μ B * (if e ∈ B then 1 else 0) ≤ p) :
    (1 - p) * g ∅ ≤ ∑ B : Finset α, μ B * g B := by
  set q : α → ℝ := fun e => ∑ B : Finset α, μ B * (if e ∈ B then 1 else 0) with hq
  have hq0 : ∀ e, 0 ≤ q e := fun e =>
    Finset.sum_nonneg (fun B _ => mul_nonneg (hμ0 B) (by split_ifs <;> norm_num))
  obtain ⟨δ, hδ, hb⟩ := chainP_abel g hg hg0 q _ (Finset.univ : Finset α) rfl
  have h1 := hb 0 p hp0 (fun e _ => ⟨hq0 e, hμp e⟩)
  have h2 := chainP_expect g Finset.univ δ hδ μ hμ0 hμ1 (fun B _ => Finset.subset_univ B)
  have h3 : ∑ e ∈ (Finset.univ : Finset α), δ e * q e
      = ∑ e ∈ (Finset.univ : Finset α), δ e * (∑ B : Finset α, μ B * (if e ∈ B then 1 else 0)) := rfl
  rw [← h3] at h2
  nlinarith
