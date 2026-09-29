-- Prove2me | solution 1 for WangZahlKakeya.kakeya_maximal_wolff_axioms
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-20T15:09:01.24798+00:00
-- url     : https://prove2.me/submissions/801046a9-8f08-4827-97d6-73eda3d7dfde
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WangZahlKakeya_union_volume_KTCW
import Theorems.Thm_WangZahlKakeya_tubeVol_comparable
import Theorems.Thm_WangZahlKakeya_tube_volume_eq
import Theorems.Thm_WangZahlKakeya_KTCW_pos
import Theorems.Thm_WangZahlKakeya_KTCW_le_wolff

/-!
# Theorem 1.2 of Wang–Zahl as a special case of Corollary 1.10

"Theorem 1.2 is now a special case of Corollary 1.10 — the hypotheses of Theorem 1.2 ensure that
`C_{KT-CW}(𝕋) ≤ 1000`."  This file carries out that deduction.
-/

open MeasureTheory Metric Set WangZahlKakeya

theorem solution :
    ∀ ε > (0 : ℝ), ∃ K > (1 : ℝ), ∃ δ₀ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3) (lam : ℝ),
        IsTubeSystem δ n p v Y → 0 < lam →
        (∀ a b : ℝ, 0 < a → 0 < b → ∀ W : Set E3, IsPrismOfDims W ![a, b, 2] →
          (tubeCountIn δ n p v W : ℝ) ≤ 100 * a * b * δ ^ (-2 : ℝ)) →
        (∀ i, (volume (Y i)).toReal ≥ lam * tubeVol δ) →
        (volume (shadingUnion Y)).toReal ≥ δ ^ ε * lam ^ K * ((n : ℝ) * tubeVol δ) := by
  intro ε hε
  obtain ⟨K₀, hK₀, δ₀, hδ₀, H⟩ := union_volume_KTCW (ε / 2) (by linarith)
  obtain ⟨M, hM, hMle⟩ := KTCW_le_wolff
  -- the scale below which the loss `M` is absorbed by `δ^{ε/2}`
  set c₀ : ℝ := (1 / M) ^ (2 / ε) with hc₀def
  have hc₀ : 0 < c₀ := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨max K₀ 2, lt_of_lt_of_le one_lt_two (le_max_right _ _),
    min δ₀ (min 1 c₀), by positivity, ?_⟩
  intro δ hδ hδlt n p v Y lam hTS hlam hprism hshade
  have hδ0 : δ < δ₀ := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδc : δ ≤ c₀ := le_of_lt (lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (min_le_right _ _)))
  obtain ⟨hTVlow, -⟩ := tubeVol_comparable δ hδ hδ1
  have hTVpos : 0 < tubeVol δ := lt_of_lt_of_le (by positivity) hTVlow
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    simp only [Nat.cast_zero, zero_mul, mul_zero]
    exact ENNReal.toReal_nonneg
  -- `λ ≤ 1`, because each shading is contained in its tube
  have hlam1 : lam ≤ 1 := by
    set i : Fin n := ⟨0, hn⟩ with hi
    have hsub : Y i ⊆ tube (p i) (v i) δ := hTS.2.2.2.2.1 i
    have hfin : volume (tube (p i) (v i) δ) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (hTS.2.2.1 i))
      exact (measure_closedBall_lt_top).ne
    have hle : (volume (Y i)).toReal ≤ (volume (tube (p i) (v i) δ)).toReal :=
      ENNReal.toReal_mono hfin (measure_mono hsub)
    rw [tube_volume_eq (p i) (v i) δ (hTS.2.1 i)] at hle
    have := hshade i
    nlinarith
  -- the system is `λ`-dense
  have hdense : IsDenseSystem δ n Y lam := by
    unfold IsDenseSystem
    have hsum : ∑ _i : Fin n, (lam * tubeVol δ) ≤ ∑ i, (volume (Y i)).toReal :=
      Finset.sum_le_sum (fun i _ => hshade i)
    simpa [Finset.sum_const, Finset.card_univ, mul_comm, mul_assoc, mul_left_comm] using hsum
  have hm := KTCW_pos δ n p v Y hTS hn
  have hmM := hMle δ n p v Y hTS hprism
  have Hc := H δ hδ hδ0 n p v Y lam hn hTS hlam hdense
  -- absorb the constant `M` into `δ^{ε/2}`
  have hδhalf : δ ^ (ε / 2) ≤ 1 / M := by
    have h1 : δ ^ (ε / 2) ≤ c₀ ^ (ε / 2) := Real.rpow_le_rpow hδ.le hδc (by linarith)
    have h2 : c₀ ^ (ε / 2) = 1 / M := by
      rw [hc₀def, ← Real.rpow_mul (by positivity)]
      rw [show 2 / ε * (ε / 2) = 1 by field_simp]
      exact Real.rpow_one _
    linarith [h2 ▸ h1]
  have hinv : 1 / M ≤ (KTCW δ n p v)⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hm hmM
  have hlampow : lam ^ (max K₀ 2) ≤ lam ^ K₀ :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (le_max_left _ _)
  have hBnn : (0:ℝ) ≤ (n : ℝ) * tubeVol δ := by positivity
  refine le_trans ?_ Hc
  have hstep1 : δ ^ ε * lam ^ (max K₀ 2) ≤ δ ^ (ε / 2) * lam ^ K₀ * (1 / M) := by
    have hδε : δ ^ ε = δ ^ (ε / 2) * δ ^ (ε / 2) := by
      rw [← Real.rpow_add hδ]; ring_nf
    have hp1 : (0:ℝ) < δ ^ (ε / 2) := Real.rpow_pos_of_pos hδ _
    have hp2 : (0:ℝ) < lam ^ K₀ := Real.rpow_pos_of_pos hlam _
    have hp3 : (0:ℝ) < lam ^ (max K₀ 2) := Real.rpow_pos_of_pos hlam _
    calc δ ^ ε * lam ^ (max K₀ 2) = δ ^ (ε / 2) * lam ^ (max K₀ 2) * δ ^ (ε / 2) := by
          rw [hδε]; ring
      _ ≤ δ ^ (ε / 2) * lam ^ K₀ * (1 / M) := by
          have hA : δ ^ (ε / 2) * lam ^ (max K₀ 2) ≤ δ ^ (ε / 2) * lam ^ K₀ :=
            mul_le_mul_of_nonneg_left hlampow hp1.le
          exact mul_le_mul hA hδhalf hp1.le (by positivity)
  calc δ ^ ε * lam ^ (max K₀ 2) * ((n : ℝ) * tubeVol δ)
      ≤ (δ ^ (ε / 2) * lam ^ K₀ * (1 / M)) * ((n : ℝ) * tubeVol δ) :=
        mul_le_mul_of_nonneg_right hstep1 hBnn
    _ ≤ (δ ^ (ε / 2) * lam ^ K₀ * (KTCW δ n p v)⁻¹) * ((n : ℝ) * tubeVol δ) := by
        refine mul_le_mul_of_nonneg_right ?_ hBnn
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = δ ^ (ε / 2) * lam ^ K₀ * (KTCW δ n p v)⁻¹ * ((n : ℝ) * tubeVol δ) := rfl
