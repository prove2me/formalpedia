-- Prove2me | solution 1 for OfflineZeroSumMG.eq_B_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:09:51.427452+00:00
-- url     : https://prove2.me/submissions/60052229-9502-457c-9128-92bf557873a6

import Mathlib
import Definitions.Def_OfflineZeroSumMG_VILCBGame

namespace Aux_OZSMG_B3
open OfflineZeroSumMG TheoryOfGames.Minimax

lemma mem01 {n : ℕ} (w : stdSimplex ℝ (Fin n)) (i : Fin n) : 0 ≤ (w : Fin n → ℝ) i ∧ (w : Fin n → ℝ) i ≤ 1 := by
  refine ⟨w.2.1 i, ?_⟩
  have := Finset.single_le_sum (fun j _ => w.2.1 j) (Finset.mem_univ i) (f := (w : Fin n → ℝ))
  have hw : ∑ j, (w : Fin n → ℝ) j = 1 := w.2.2
  linarith

lemma K_abs {A B : ℕ} (M : Fin A → Fin B → ℝ) (w : stdSimplex ℝ (Fin A)) (η : stdSimplex ℝ (Fin B)) :
    |K M w η| ≤ ∑ a, ∑ b, |M a b| := by
  unfold K
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  obtain ⟨h1, h2⟩ := mem01 w a
  obtain ⟨h3, h4⟩ := mem01 η b
  rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h3]
  have := abs_nonneg (M a b)
  calc |M a b| * (w : Fin A → ℝ) a * (η : Fin B → ℝ) b ≤ |M a b| * 1 * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h2 this) h4 h3 (by positivity)
    _ = |M a b| := by ring

lemma K_le {A B : ℕ} (M1 M2 : Fin A → Fin B → ℝ) (δ : ℝ) (h : ∀ a b, M1 a b ≤ M2 a b + δ)
    (w : stdSimplex ℝ (Fin A)) (η : stdSimplex ℝ (Fin B)) : K M1 w η ≤ K M2 w η + δ := by
  have hw : ∑ a, (w : Fin A → ℝ) a = 1 := w.2.2
  have hη : ∑ b, (η : Fin B → ℝ) b = 1 := η.2.2
  have hsum : ∑ a, ((w : Fin A → ℝ) a * ∑ b, (η : Fin B → ℝ) b) = 1 := by
    rw [← Finset.sum_mul, hw, hη, one_mul]
  have : K M2 w η + δ = ∑ a, ∑ b, (M2 a b + δ) * (w : Fin A → ℝ) a * (η : Fin B → ℝ) b := by
    unfold K
    have e : ∀ a b, (M2 a b + δ) * (w : Fin A → ℝ) a * (η : Fin B → ℝ) b
        = M2 a b * (w : Fin A → ℝ) a * (η : Fin B → ℝ) b
          + δ * ((w : Fin A → ℝ) a * (η : Fin B → ℝ) b) := by intros; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_one]
  rw [this]
  unfold K
  apply Finset.sum_le_sum; intro a _
  apply Finset.sum_le_sum; intro b _
  obtain ⟨h1, _⟩ := mem01 w a
  obtain ⟨h3, _⟩ := mem01 η b
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h a b) h1) h3

lemma gval_le {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (M1 M2 : Fin A → Fin B → ℝ) (δ : ℝ)
    (h : ∀ a b, M1 a b ≤ M2 a b + δ) : gval M1 ≤ gval M2 + δ := by
  haveI : Nonempty (stdSimplex ℝ (Fin A)) := ⟨⟨_, single_mem_stdSimplex ℝ (⟨0, hA⟩ : Fin A)⟩⟩
  haveI : Nonempty (stdSimplex ℝ (Fin B)) := ⟨⟨_, single_mem_stdSimplex ℝ (⟨0, hB⟩ : Fin B)⟩⟩
  have hbb : ∀ (M : Fin A → Fin B → ℝ) (w : stdSimplex ℝ (Fin A)),
      BddBelow (Set.range fun η : stdSimplex ℝ (Fin B) => K M w η) := by
    intro M w
    refine ⟨-(∑ a, ∑ b, |M a b|), ?_⟩
    rintro _ ⟨η, rfl⟩
    have := K_abs M w η
    exact neg_le_of_abs_le this
  have hba : ∀ (M : Fin A → Fin B → ℝ),
      BddAbove (Set.range fun w : stdSimplex ℝ (Fin A) => minK M w) := by
    intro M
    refine ⟨∑ a, ∑ b, |M a b|, ?_⟩
    rintro _ ⟨w, rfl⟩
    obtain ⟨η⟩ := (inferInstance : Nonempty (stdSimplex ℝ (Fin B)))
    unfold minK
    exact (ciInf_le (hbb M w) η).trans (le_of_abs_le (K_abs M w η))
  unfold gval
  apply ciSup_le
  intro w
  have hmin : minK M1 w ≤ minK M2 w + δ := by
    have : minK M1 w - δ ≤ minK M2 w := by
      unfold minK
      apply le_ciInf
      intro η
      have := (ciInf_le (hbb M1 w) η).trans (K_le M1 M2 δ h w η)
      linarith
    linarith
  linarith [le_ciSup (hba M2) w]

end Aux_OZSMG_B3

open OfflineZeroSumMG Aux_OZSMG_B3 in
theorem solution {S A B : ℕ} (hS : 0 < S) (hA : 0 < A) (hB : 0 < B)
    (Q₁ Q₂ : Fin S → Fin A → Fin B → ℝ) :
    ‖Vof Q₁ - Vof Q₂‖ ≤ ‖Q₁ - Q₂‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun s => ?_
  have hab : ∀ a b, |Q₁ s a b - Q₂ s a b| ≤ ‖Q₁ - Q₂‖ := by
    intro a b
    calc |Q₁ s a b - Q₂ s a b| = ‖(Q₁ - Q₂) s a b‖ := by simp [Real.norm_eq_abs]
      _ ≤ ‖(Q₁ - Q₂) s a‖ := norm_le_pi_norm _ b
      _ ≤ ‖(Q₁ - Q₂) s‖ := norm_le_pi_norm _ a
      _ ≤ ‖Q₁ - Q₂‖ := norm_le_pi_norm _ s
  have h1 := gval_le hA hB (Q₁ s) (Q₂ s) ‖Q₁ - Q₂‖ (fun a b => by
    have := (abs_le.1 (hab a b)).2; linarith)
  have h2 := gval_le hA hB (Q₂ s) (Q₁ s) ‖Q₁ - Q₂‖ (fun a b => by
    have := (abs_le.1 (hab a b)).1; linarith)
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  simp only [Vof]
  constructor <;> linarith
