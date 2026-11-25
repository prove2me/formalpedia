-- Prove2me | solution 1 for ReciprocityTheory.Cheb.exists_reps_meanZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:09.157364+00:00
-- url     : https://prove2.me/submissions/d9ce95ce-789e-45a6-a01f-2f1d5fc9b14e

import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_NormCongr
import Definitions.Def_ReciprocityTheory_Chebotarev_MeanZero
import Theorems.Thm_ReciprocityTheory_Cheb_isCoprime_span_mul_of_coprime_absNorm
import Theorems.Thm_ReciprocityTheory_Cheb_sum_crt_weight_eq_zero
import Theorems.Thm_ReciprocityTheory_Cheb_latOf_mono
import Theorems.Thm_ReciprocityTheory_Cheb_preZ_embZ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) (b c : NZIdeal E)
    (hcop : Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm b.1)) :
    latOf (mbc l b.1 c.1) ≤ latOf b.1 ∧
    ∃ reps : Finset (mixedSpace E), (∀ β ∈ reps, β ∈ latOf b.1) ∧
      (∀ α ∈ latOf b.1, ∃ l' ∈ latOf (mbc l b.1 c.1), ∃ β ∈ reps, α = l' + β) ∧
      (∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ latOf (mbc l b.1 c.1) → β₁ = β₂) ∧
      (∀ l' ∈ latOf (mbc l b.1 c.1), ∀ β ∈ reps, cfun χ b.1 c.1 (l' + β) = cfun χ b.1 c.1 β) ∧
      ∑ β ∈ reps, cfun χ b.1 c.1 β = 0 := by
  have hM : mbc l b.1 c.1 = Ideal.span {((l * Ideal.absNorm b.1 : ℕ) : 𝓞 E)} * b.1 * c.1 := rfl
  rw [hM]
  obtain ⟨B, hB0⟩ := b
  obtain ⟨C, hC0⟩ := c
  simp only at hcop ⊢
  set I : Ideal (𝓞 E) := Ideal.span {((l * Ideal.absNorm B : ℕ) : 𝓞 E)} * B with hI
  have hIC : IsCoprime I C := isCoprime_span_mul_of_coprime_absNorm B C hcop
  have hIB : I ≤ B := Ideal.mul_le_right
  have hIspan : I ≤ Ideal.span {((((l : ℤ) * (Ideal.absNorm B : ℤ) : ℤ)) : 𝓞 E)} := by
    have : ((((l : ℤ) * (Ideal.absNorm B : ℤ) : ℤ)) : 𝓞 E) = ((l * Ideal.absNorm B : ℕ) : 𝓞 E) := by
      push_cast; rfl
    rw [this]; exact Ideal.mul_le_left
  have hMB : I * C ≤ B := le_trans Ideal.mul_le_left hIB
  have hMBC : I * C ≤ B * C := Ideal.mul_mono_left hIB
  have hBC : B * C = B ⊓ C := Ideal.mul_eq_inf_of_coprime
    (Ideal.isCoprime_iff_sup_eq.mp (hIC.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hIB)))
  have hl0 : (l * Ideal.absNorm B : ℕ) ≠ 0 :=
    Nat.mul_ne_zero (Fact.out : l.Prime).ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨by exact_mod_cast hl0, hB0⟩
  have hM0 : I * C ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]; exact ⟨hI0, hC0⟩
  have := Ideal.finiteQuotientOfFreeOfNeBot (I * C) hM0
  have := Ideal.finiteQuotientOfFreeOfNeBot I hI0
  have := Ideal.finiteQuotientOfFreeOfNeBot C hC0
  let : Fintype (𝓞 E ⧸ I * C) := Fintype.ofFinite _
  let : Fintype (𝓞 E ⧸ I) := Fintype.ofFinite _
  let : Fintype (𝓞 E ⧸ C) := Fintype.ofFinite _
  have hsurj : Function.Surjective (Ideal.Quotient.mk (I * C)) := Ideal.Quotient.mk_surjective
  obtain ⟨σ, hσ⟩ : ∃ σ : 𝓞 E ⧸ I * C → 𝓞 E, ∀ y, Ideal.Quotient.mk (I * C) (σ y) = y :=
    ⟨_, Function.surjInv_eq hsurj⟩
  have hσinj : Function.Injective σ := fun y₁ y₂ h => by rw [← hσ y₁, ← hσ y₂, h]
  have hkey : ∀ y₁ y₂, σ y₁ - σ y₂ ∈ I * C → y₁ = y₂ := by
    intro y₁ y₂ h
    rw [← hσ y₁, ← hσ y₂]; exact Ideal.Quotient.eq.mpr h

  set F : 𝓞 E → ℂ := fun α => χ (((Algebra.norm ℤ α / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) *
    (1 - (Ideal.absNorm C : ℂ) * (if α ∈ B * C then 1 else 0)) with hF
  have hcf : ∀ α, cfun χ B C (embZ α) = F α := by
    intro α; simp only [cfun, preZ_embZ, hF]
  have hchi : ∀ a a', a ∈ B → a' ∈ B → a - a' ∈ I →
      χ (((Algebra.norm ℤ a / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) =
      χ (((Algebra.norm ℤ a' / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) := by
    intro a a' ha ha' h
    congr 1
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr (norm_div_absNorm_modEq (l : ℤ) ha ha' (hIspan h))
  have hper : ∀ μ ∈ I * C, ∀ a ∈ B, F (μ + a) = F a := by
    intro μ hμ a ha
    simp only [hF]
    rw [hchi (μ + a) a (B.add_mem (hMB hμ) ha) ha (by rw [add_sub_cancel_right]; exact Ideal.mul_le_left hμ)]
    simp only [Ideal.add_mem_iff_right _ (hMBC hμ)]
  set reps : Finset (mixedSpace E) :=
    (Finset.univ.filter fun y => σ y ∈ B).image (fun y => embZ (σ y)) with hreps
  have hmemreps : ∀ β ∈ reps, ∃ y, σ y ∈ B ∧ embZ (σ y) = β := by
    intro β hβ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hβ
    exact ⟨y, (Finset.mem_filter.mp hy).2, rfl⟩
  refine ⟨latOf_mono hMB, reps, ?_, ?_, ?_, ?_, ?_⟩
  · intro β hβ
    obtain ⟨y, hy, rfl⟩ := hmemreps β hβ
    exact mem_latOf.mpr ⟨_, hy, rfl⟩
  · intro α hα
    obtain ⟨a, ha, rfl⟩ := mem_latOf.mp hα
    have hya : σ (Ideal.Quotient.mk _ a) - a ∈ I * C := Ideal.Quotient.eq.mp (hσ _)
    have hyB : σ (Ideal.Quotient.mk _ a) ∈ B := by
      have := B.add_mem (hMB hya) ha
      rwa [sub_add_cancel] at this
    refine ⟨embZ (a - σ (Ideal.Quotient.mk _ a)), mem_latOf.mpr ⟨_, ?_, rfl⟩,
      embZ (σ (Ideal.Quotient.mk _ a)), ?_, ?_⟩
    · have := (I * C).neg_mem hya
      rwa [neg_sub] at this
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyB⟩, rfl⟩
    · rw [map_sub, sub_add_cancel]
  · intro β₁ h₁ β₂ h₂ hd
    obtain ⟨y₁, -, rfl⟩ := hmemreps β₁ h₁
    obtain ⟨y₂, -, rfl⟩ := hmemreps β₂ h₂
    obtain ⟨μ, hμ, hμe⟩ := mem_latOf.mp hd
    have : μ = σ y₁ - σ y₂ := embZ_injective (by rw [hμe, map_sub])
    rw [hkey y₁ y₂ (this ▸ hμ)]
  · intro l' hl' β hβ
    obtain ⟨y, hy, rfl⟩ := hmemreps β hβ
    obtain ⟨μ, hμ, rfl⟩ := mem_latOf.mp hl'
    rw [← map_add, hcf, hcf, hper μ hμ _ hy]
  · rw [hreps, Finset.sum_image (fun y₁ _ y₂ _ h => hσinj (embZ_injective h))]
    simp only [hcf]
    rw [Finset.sum_filter]
    set f : 𝓞 E → ℂ := fun a => if a ∈ B then
      χ (((Algebra.norm ℤ a / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) else 0 with hf
    have hfper : ∀ a a', a - a' ∈ I → f a = f a' := by
      intro a a' h
      have hiff : a ∈ B ↔ a' ∈ B := by
        have h' := hIB h
        constructor
        · intro ha; have := B.sub_mem ha h'; rwa [sub_sub_cancel] at this
        · intro ha'; have := B.add_mem h' ha'; rwa [sub_add_cancel] at this
      simp only [hf]
      by_cases ha : a ∈ B
      · rw [if_pos ha, if_pos (hiff.mp ha), hchi a a' ha (hiff.mp ha) h]
      · rw [if_neg ha, if_neg (fun h' => ha (hiff.mpr h'))]
    have hcard : (Ideal.absNorm C : ℂ) = (Fintype.card (𝓞 E ⧸ C) : ℂ) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    refine (Finset.sum_congr rfl fun y _ => ?_).trans (sum_crt_weight_eq_zero I C hIC f hfper σ hσ)
    by_cases hy : σ y ∈ B
    · simp only [hf, hF, ← hcard, if_pos hy, hBC, Ideal.mem_inf, hy, true_and, if_true]
    · simp only [hf, if_neg hy, zero_mul]
end ReciprocityTheory.Cheb
