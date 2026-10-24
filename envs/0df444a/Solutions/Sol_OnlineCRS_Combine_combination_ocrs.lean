-- Prove2me | solution 1 for OnlineCRS.Combine.combination_ocrs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T18:45:51.800562+00:00
-- url     : https://prove2.me/submissions/0a8aa2e9-cd60-4538-94b7-c5fb0b55103d

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Combination

set_option autoImplicit false

open scoped Pointwise

namespace OCRSCombineHelpers

open OnlineCRS.Matroid

variable {α : Type} [Fintype α] [DecidableEq α]

lemma activeProb_nonneg (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (A : Finset α) :
    0 ≤ activeProb x A := by
  unfold activeProb
  apply Finset.prod_nonneg
  intro e _
  split_ifs
  · exact (hx e).1
  · linarith [(hx e).2]

lemma activeProb_mul (x : α → ℝ) (A B : Finset α) :
    activeProb x A * activeProb x B = activeProb x (A ∩ B) * activeProb x (A ∪ B) := by
  unfold activeProb
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases ha : e ∈ A <;> by_cases hb : e ∈ B <;>
    simp [ha, hb, Finset.mem_inter, Finset.mem_union]; ring

lemma activeProb_sum (x : α → ℝ) : ∑ A : Finset α, activeProb x A = 1 := by
  have h := Fintype.prod_add (fun e => x e) (fun e => 1 - x e)
  simp only [add_sub_cancel, Finset.prod_const_one] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro A _
  unfold activeProb
  rw [← Finset.prod_mul_prod_compl A]
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    rw [if_pos he]
  · apply Finset.prod_congr rfl
    intro e he
    rw [if_neg (Finset.mem_compl.mp he)]

lemma harris_general (μ : Finset α → ℝ) (hμ0 : 0 ≤ μ)
    (hμ : ∀ A B, μ A * μ B ≤ μ (A ∩ B) * μ (A ∪ B))
    (f g : Finset α → ℝ) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) (hf : Antitone f) (hg : Antitone g) :
    (∑ A, μ A * f A) * ∑ A, μ A * g A ≤ (∑ A, μ A) * ∑ A, μ A * (f A * g A) := by
  have key := fkg (α := (Finset α)ᵒᵈ) (μ := μ ∘ OrderDual.ofDual) (f := f ∘ OrderDual.ofDual)
    (g := g ∘ OrderDual.ofDual) (fun a => hμ0 _) (fun a => hf0 _) (fun a => hg0 _)
    hf.dual_left hg.dual_left
    (fun a b => (hμ (OrderDual.ofDual a) (OrderDual.ofDual b)).trans (le_of_eq (mul_comm _ _)))
  exact key

lemma selectable_inter {F₁ F₂ : Finset (Finset α)} {A : Finset α} {e : α}
    (h₁ : Selectable F₁ A e) (h₂ : Selectable F₂ A e) : Selectable (F₁ ∩ F₂) A e := by
  intro I hI hF
  rw [Finset.mem_inter] at hF ⊢
  exact ⟨h₁ I hI hF.1, h₂ I hI hF.2⟩

lemma selectable_anti {Fam : Finset (Finset α)} {A B : Finset α} {e : α} (hAB : A ⊆ B)
    (h : Selectable Fam B e) : Selectable Fam A e :=
  fun I hI hF => h I (hI.trans hAB) hF

open Classical in
lemma harris_sel (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (F₁ F₂ : Finset (Finset α)) (e : α) :
    selProb x F₁ e * selProb x F₂ e ≤ selProb x (F₁ ∩ F₂) e := by
  have key := harris_general (activeProb x) (fun A => activeProb_nonneg x hx A)
    (fun A B => (activeProb_mul x A B).le)
    (fun A => if Selectable F₁ A e then (1 : ℝ) else 0)
    (fun A => if Selectable F₂ A e then (1 : ℝ) else 0)
    (fun A => by dsimp only; split_ifs <;> norm_num)
    (fun A => by dsimp only; split_ifs <;> norm_num)
    (fun A B hAB => by
      dsimp only
      by_cases hB : Selectable F₁ B e
      · rw [if_pos hB, if_pos (selectable_anti hAB hB)]
      · rw [if_neg hB]; split_ifs <;> norm_num)
    (fun A B hAB => by
      dsimp only
      by_cases hB : Selectable F₂ B e
      · rw [if_pos hB, if_pos (selectable_anti hAB hB)]
      · rw [if_neg hB]; split_ifs <;> norm_num)
  rw [activeProb_sum, one_mul] at key
  have e1 : ∀ F : Finset (Finset α), selProb x F e =
      ∑ A, activeProb x A * (if Selectable F A e then (1 : ℝ) else 0) := by
    intro F
    unfold selProb
    apply Finset.sum_congr rfl
    intro A _
    split_ifs <;> simp
  rw [e1 F₁, e1 F₂]
  refine key.trans ?_
  unfold selProb
  apply Finset.sum_le_sum
  intro A _
  by_cases h1 : Selectable F₁ A e
  · by_cases h2 : Selectable F₂ A e
    · rw [if_pos h1, if_pos h2, if_pos (selectable_inter h1 h2)]; simp
    · rw [if_pos h1, if_neg h2]; simp only [mul_zero]; split_ifs
      · exact activeProb_nonneg x hx A
      · exact le_rfl
  · rw [if_neg h1]; simp only [zero_mul, mul_zero]; split_ifs
    · exact activeProb_nonneg x hx A
    · exact le_rfl

lemma combine_sum (w₁ w₂ : (α → ℝ) → Finset (Finset α) → ℝ) (x : α → ℝ)
    (φ : Finset (Finset α) → ℝ) :
    ∑ Fam, OnlineCRS.Combine.combine w₁ w₂ x Fam * φ Fam =
      ∑ F₁, ∑ F₂, w₁ x F₁ * w₂ x F₂ * φ (F₁ ∩ F₂) := by
  unfold OnlineCRS.Combine.combine
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro F₁ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro F₂ _
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

end OCRSCombineHelpers

theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (𝓕₁ 𝓕₂ : Finset α → Prop) (P₁ P₂ : Set (α → ℝ))
    (b c₁ c₂ : ℝ)
    (w₁ w₂ : (α → ℝ) → Finset (Finset α) → ℝ)
    (hP₁ : ∀ y ∈ P₁, ∀ e, 0 ≤ y e ∧ y e ≤ 1)
    (hP₂ : ∀ y ∈ P₂, ∀ e, 0 ≤ y e ∧ y e ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (hc₁₀ : 0 ≤ c₁) (hc₁₁ : c₁ ≤ 1)
    (hc₂₀ : 0 ≤ c₂) (hc₂₁ : c₂ ≤ 1)
    (hπ₁ : OnlineCRS.Matroid.IsSelectableRand 𝓕₁ P₁ b c₁ w₁)
    (hπ₂ : OnlineCRS.Matroid.IsSelectableRand 𝓕₂ P₂ b c₂ w₂) :
    ∃ w : (α → ℝ) → Finset (Finset α) → ℝ,
      OnlineCRS.Matroid.IsSelectableRand (fun I => 𝓕₁ I ∧ 𝓕₂ I) (P₁ ∩ P₂) b (c₁ * c₂) w := by
  refine ⟨OnlineCRS.Combine.combine w₁ w₂, ?_, ?_⟩
  · intro x
    obtain ⟨h1n, h1s, h1g⟩ := hπ₁.1 x
    obtain ⟨h2n, h2s, h2g⟩ := hπ₂.1 x
    refine ⟨?_, ?_, ?_⟩
    · intro Fam
      unfold OnlineCRS.Combine.combine
      apply Finset.sum_nonneg
      intro F₁ _
      apply Finset.sum_nonneg
      intro F₂ _
      apply mul_nonneg (mul_nonneg (h1n F₁) (h2n F₂))
      split_ifs <;> norm_num
    · have := OCRSCombineHelpers.combine_sum w₁ w₂ x (fun _ => 1)
      simp only [mul_one] at this
      rw [this, ← Finset.sum_mul_sum, h1s, h2s, one_mul]
    · intro Fam hFam
      unfold OnlineCRS.Combine.combine at hFam
      obtain ⟨F₁, -, hF₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero hFam
      obtain ⟨F₂, -, hF₂⟩ := Finset.exists_ne_zero_of_sum_ne_zero hF₁
      have hw1 : w₁ x F₁ ≠ 0 := fun h => hF₂ (by rw [h]; ring)
      have hw2 : w₂ x F₂ ≠ 0 := fun h => hF₂ (by rw [h]; ring)
      have hEq : F₁ ∩ F₂ = Fam := by
        by_contra hne
        exact hF₂ (by rw [if_neg hne]; ring)
      subst hEq
      obtain ⟨g1e, g1d, g1f⟩ := h1g F₁ hw1
      obtain ⟨g2e, g2d, g2f⟩ := h2g F₂ hw2
      refine ⟨Finset.mem_inter.mpr ⟨g1e, g2e⟩, ?_, ?_⟩
      · intro I hI J hJ
        rw [Finset.mem_inter] at hI ⊢
        exact ⟨g1d I hI.1 J hJ, g2d I hI.2 J hJ⟩
      · intro I hI
        rw [Finset.mem_inter] at hI
        exact ⟨g1f I hI.1, g2f I hI.2⟩
  · intro x hx e
    obtain ⟨y, ⟨hy1, hy2⟩, rfl⟩ := hx
    have hx1 : b • y ∈ b • P₁ := Set.smul_mem_smul_set hy1
    have hx2 : b • y ∈ b • P₂ := Set.smul_mem_smul_set hy2
    have hbd : ∀ e, 0 ≤ (b • y) e ∧ (b • y) e ≤ 1 := by
      intro e'
      have h := hP₁ y hy1 e'
      simp only [Pi.smul_apply, smul_eq_mul]
      exact ⟨mul_nonneg hb₀ h.1, mul_le_one₀ hb₁ h.1 h.2⟩
    have s1 := hπ₁.2 (b • y) hx1 e
    have s2 := hπ₂.2 (b • y) hx2 e
    rw [OCRSCombineHelpers.combine_sum]
    calc c₁ * c₂
        ≤ (∑ F₁, w₁ (b • y) F₁ * OnlineCRS.Matroid.selProb (b • y) F₁ e) *
            ∑ F₂, w₂ (b • y) F₂ * OnlineCRS.Matroid.selProb (b • y) F₂ e :=
          mul_le_mul s1 s2 hc₂₀ (le_trans hc₁₀ s1)
      _ = ∑ F₁, ∑ F₂, (w₁ (b • y) F₁ * OnlineCRS.Matroid.selProb (b • y) F₁ e) *
            (w₂ (b • y) F₂ * OnlineCRS.Matroid.selProb (b • y) F₂ e) := Finset.sum_mul_sum _ _ _ _
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro F₁ _
          apply Finset.sum_le_sum
          intro F₂ _
          have hh := OCRSCombineHelpers.harris_sel (b • y) hbd F₁ F₂ e
          have hw : 0 ≤ w₁ (b • y) F₁ * w₂ (b • y) F₂ :=
            mul_nonneg ((hπ₁.1 (b • y)).1 F₁) ((hπ₂.1 (b • y)).1 F₂)
          calc (w₁ (b • y) F₁ * OnlineCRS.Matroid.selProb (b • y) F₁ e) *
                (w₂ (b • y) F₂ * OnlineCRS.Matroid.selProb (b • y) F₂ e)
              = (w₁ (b • y) F₁ * w₂ (b • y) F₂) *
                  (OnlineCRS.Matroid.selProb (b • y) F₁ e *
                    OnlineCRS.Matroid.selProb (b • y) F₂ e) := by ring
            _ ≤ (w₁ (b • y) F₁ * w₂ (b • y) F₂) *
                  OnlineCRS.Matroid.selProb (b • y) (F₁ ∩ F₂) e :=
                mul_le_mul_of_nonneg_left hh hw
