-- Prove2me | solution 1 for SponsoredAssort.claim_G_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:16:20.820947+00:00
-- url     : https://prove2.me/submissions/472e8be8-b678-4a14-8ee1-c6933f9e77a4

import Mathlib
import Definitions.Def_SponsoredAssort_choiceProb
import Definitions.Def_SponsoredAssort_others

open scoped NNReal

namespace Aux_SponsoredAssort_G1

open SponsoredAssort

theorem hcp {n : ℕ} (v : Attr n) (i : Fin n) (S : Finset (Fin n)) (hS : i ∈ S) (y : ℝ≥0) :
    choiceProb S (Function.update v i y) i = (y : ℝ) / (y + others v i S) := by
  unfold choiceProb others
  rw [if_pos hS, Function.update_self,
    ← Finset.add_sum_erase S (fun j => ((Function.update v i y j : ℝ≥0) : ℝ)) hS]
  simp only [Function.update_self]
  rw [Finset.sum_congr rfl (fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])]
  congr 1
  ring

theorem others_ge {n : ℕ} (v : Attr n) (i : Fin n) (S : Finset (Fin n)) : 1 ≤ others v i S := by
  unfold others
  have : 0 ≤ ∑ j ∈ S.erase i, (v j : ℝ) := Finset.sum_nonneg (fun j _ => (v j).coe_nonneg)
  linarith

end Aux_SponsoredAssort_G1

open SponsoredAssort in
theorem solution {n : ℕ} (r : Fin n → ℝ) (v : Attr n) (i : Fin n) (hr : 0 < r i)
    (S₁ S₂ : Finset (Fin n)) (h₁ : i ∈ S₁) (h₂ : i ∈ S₂) (ha : others v i S₁ < others v i S₂) :
    let δ : ℝ≥0 → ℝ := fun y =>
      r i * choiceProb S₁ (Function.update v i y) i - r i * choiceProb S₂ (Function.update v i y) i
    (∀ y z : ℝ≥0, y < z → (z : ℝ) ≤ Real.sqrt (others v i S₁ * others v i S₂) → δ y < δ z) ∧
    (∀ y z : ℝ≥0, Real.sqrt (others v i S₁ * others v i S₂) ≤ (y : ℝ) → y < z → δ z < δ y) ∧
    (∀ y : ℝ≥0, 0 < y →
      δ y = δ (Real.toNNReal (others v i S₁ * others v i S₂ / (y : ℝ)))) := by
  intro δ
  have hA1 := Aux_SponsoredAssort_G1.others_ge v i S₁
  have hB1 := Aux_SponsoredAssort_G1.others_ge v i S₂
  obtain ⟨A, hA⟩ : ∃ A, A = others v i S₁ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = others v i S₂ := ⟨_, rfl⟩
  rw [← hA] at hA1 ha ⊢
  rw [← hB] at hB1 ha ⊢
  have hg0 : ∀ y : ℝ, 0 ≤ y → r i * (y / (y + A)) - r i * (y / (y + B))
      = r i * (B - A) * (y / ((y + A) * (y + B))) := by
    intro y hy
    have h1 : y + A ≠ 0 := by linarith
    have h2 : y + B ≠ 0 := by linarith
    field_simp <;> ring
  have hδ : ∀ y : ℝ≥0, δ y = r i * (B - A) * ((y : ℝ) / ((y + A) * (y + B))) := by
    intro y
    show r i * choiceProb S₁ (Function.update v i y) i
      - r i * choiceProb S₂ (Function.update v i y) i = _
    rw [Aux_SponsoredAssort_G1.hcp v i S₁ h₁, Aux_SponsoredAssort_G1.hcp v i S₂ h₂, ← hA, ← hB]
    exact hg0 y y.coe_nonneg
  have hg : ∀ y z : ℝ, 0 ≤ y → 0 ≤ z → z / ((z + A) * (z + B)) - y / ((y + A) * (y + B))
      = (z - y) * (A * B - y * z) / ((y + A) * (y + B) * ((z + A) * (z + B))) := by
    intro y z hy hz
    have h1 : y + A ≠ 0 := by linarith
    have h2 : y + B ≠ 0 := by linarith
    have h3 : z + A ≠ 0 := by linarith
    have h4 : z + B ≠ 0 := by linarith
    field_simp <;> ring
  have hc : 0 < r i * (B - A) := mul_pos hr (by linarith)
  have hAB : 0 ≤ A * B := by positivity
  have hsq := Real.sq_sqrt hAB
  have hs0 := Real.sqrt_nonneg (A * B)
  refine ⟨?_, ?_, ?_⟩
  · intro y z hyz hz
    rw [hδ, hδ]
    have hy0 : (0 : ℝ) ≤ y := y.coe_nonneg
    have hyz' : (y : ℝ) < z := hyz
    have hz2 : (z : ℝ) ^ 2 ≤ A * B := by
      have := pow_le_pow_left₀ z.coe_nonneg hz 2
      linarith
    have hp : 0 < A * B - (y : ℝ) * z := by nlinarith
    have hden : 0 < ((y : ℝ) + A) * (y + B) * ((z + A) * (z + B)) := by positivity
    have hgpos : 0 < (z : ℝ) / ((z + A) * (z + B)) - y / ((y + A) * (y + B)) := by
      rw [hg y z hy0 z.coe_nonneg]
      exact div_pos (mul_pos (by linarith) hp) hden
    have := mul_pos hc hgpos
    linarith
  · intro y z hy hyz
    rw [hδ, hδ]
    have hy0 : (0 : ℝ) ≤ y := y.coe_nonneg
    have hyz' : (y : ℝ) < z := hyz
    have hy2 : A * B ≤ (y : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ hs0 hy 2
      linarith
    have hypos : (0 : ℝ) < y := lt_of_lt_of_le (Real.sqrt_pos.mpr (by nlinarith)) hy
    have hp : 0 < (y : ℝ) * z - A * B := by nlinarith [mul_lt_mul_of_pos_left hyz' hypos]
    have hden : 0 < ((y : ℝ) + A) * (y + B) * ((z + A) * (z + B)) := by positivity
    have hgneg : (z : ℝ) / ((z + A) * (z + B)) - y / ((y + A) * (y + B)) < 0 := by
      rw [hg y z hy0 z.coe_nonneg]
      apply div_neg_of_neg_of_pos _ hden
      apply mul_neg_of_pos_of_neg (by linarith)
      linarith
    have := mul_pos hc (neg_pos.mpr hgneg)
    linarith
  · intro y hy
    rw [hδ, hδ]
    have hy' : (0 : ℝ) < y := hy
    have hq : 0 ≤ A * B / (y : ℝ) := by positivity
    rw [Real.coe_toNNReal _ hq]
    rw [mul_right_inj' hc.ne']
    have hA0 : 0 < A := by linarith
    have hB0 : 0 < B := by linarith
    have h3 : (y : ℝ) ≠ 0 := hy'.ne'
    have hD1 : ((y : ℝ) + A) * (y + B) ≠ 0 := by positivity
    have hq' : 0 < A * B / (y : ℝ) := by positivity
    have hD2 : (A * B / (y : ℝ) + A) * (A * B / y + B) ≠ 0 := by positivity
    rw [div_eq_div_iff hD1 hD2]
    field_simp
    ring
