-- Prove2me | solution 1 for WangZahlKakeya.union_volume_KTCW
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-20T15:26:14.293851+00:00
-- url     : https://prove2.me/submissions/96e8430d-1f5c-4245-b5d4-c92dc1a7e1a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WangZahlKakeya_assertion_D_E_zero
import Theorems.Thm_WangZahlKakeya_tubeVol_comparable
import Theorems.Thm_WangZahlKakeya_tube_volume_eq
import Theorems.Thm_WangZahlKakeya_KTCW_ball_bound

/-!
# Corollary 1.10 of Wang–Zahl from Theorem 1.9

Theorem 1.9 supplies the estimate for systems that are `δ^η`-dense; Corollary 1.10 is its
rephrasing for a system that is merely `λ`-dense, the density entering as a power `λ^K`.
-/

open MeasureTheory Metric Set WangZahlKakeya

theorem solution :
    ∀ ε > (0 : ℝ), ∃ K > (0 : ℝ), ∃ δ₀ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3) (lam : ℝ),
        0 < n → IsTubeSystem δ n p v Y → 0 < lam → IsDenseSystem δ n Y lam →
        (volume (shadingUnion Y)).toReal ≥
          δ ^ ε * lam ^ K * (KTCW δ n p v)⁻¹ * ((n : ℝ) * tubeVol δ) := by
  obtain ⟨-, hE00⟩ := assertion_D_E_zero
  obtain ⟨B, hB, hBle⟩ := KTCW_ball_bound
  intro ε hε
  obtain ⟨κ, hκ, η, hη, H⟩ := hE00 (ε / 2) (by linarith)
  refine ⟨2 + 3 / η, by positivity, min 1 (min (κ ^ (2 / ε)) (3 / B)), by positivity, ?_⟩
  intro δ hδ hδlt n p v Y lam hn hTS hlam hdense
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδlt (min_le_left _ _))
  have hδκ : δ ≤ κ ^ (2 / ε) :=
    le_of_lt (lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδB : δ ≤ 3 / B :=
    le_of_lt (lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (min_le_right _ _)))
  obtain ⟨hTVlow, -⟩ := tubeVol_comparable δ hδ hδ1
  have hTVpos : 0 < tubeVol δ := lt_of_lt_of_le (by positivity) hTVlow
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hBnn : (0:ℝ) ≤ (n : ℝ) * tubeVol δ := by positivity
  set K : ℝ := 2 + 3 / η with hK
  have hK0 : 0 ≤ K := by positivity
  -- every shading is contained in its tube, so `λ ≤ 1`
  have hYle : ∀ i, (volume (Y i)).toReal ≤ tubeVol δ := by
    intro i
    have hfin : volume (tube (p i) (v i) δ) ≠ ⊤ :=
      ne_top_of_le_ne_top (measure_closedBall_lt_top).ne (measure_mono (hTS.2.2.1 i))
    have hle : (volume (Y i)).toReal ≤ (volume (tube (p i) (v i) δ)).toReal :=
      ENNReal.toReal_mono hfin (measure_mono (hTS.2.2.2.2.1 i))
    rwa [tube_volume_eq (p i) (v i) δ (hTS.2.1 i)] at hle
  have hlam1 : lam ≤ 1 := by
    have h1 : ∑ i, (volume (Y i)).toReal ≤ ∑ _i : Fin n, tubeVol δ :=
      Finset.sum_le_sum (fun i _ => hYle i)
    have h2 : lam * ((n : ℝ) * tubeVol δ) ≤ (n : ℝ) * tubeVol δ := by
      have h3 := le_trans hdense h1
      simpa [Finset.sum_const, Finset.card_univ, mul_comm, mul_assoc, mul_left_comm] using h3
    nlinarith [mul_pos hnpos hTVpos]
  -- the Katz–Tao constant is positive and controls `m⁻¹ (#𝕋)|T|`
  have hm := hBle δ n p v Y hTS
  have hmpos : 0 < KTCW δ n p v := by nlinarith [mul_pos hnpos hTVpos]
  have hmB : (KTCW δ n p v)⁻¹ * ((n : ℝ) * tubeVol δ) ≤ B := by
    rw [inv_mul_le_iff₀ hmpos]
    linarith [hm]
  rcases le_or_gt (δ ^ η) lam with hcase | hcase
  · -- the system is already `δ^η`-dense, so Theorem 1.9 applies directly
    have hdense' : IsDenseSystem δ n Y (δ ^ η) := by
      unfold IsDenseSystem at hdense ⊢
      exact le_trans (mul_le_mul_of_nonneg_right hcase hBnn) hdense
    have Hmain := H δ hδ n p v Y hn hTS hdense'
    simp only [neg_zero, Real.rpow_zero, mul_one, zero_add] at Hmain
    refine le_trans ?_ Hmain
    have hstep : δ ^ ε * lam ^ K ≤ κ * δ ^ (ε / 2) := by
      have hlamK : lam ^ K ≤ 1 := Real.rpow_le_one hlam.le hlam1 hK0
      have hδhalf : δ ^ (ε / 2) ≤ κ := by
        have h1 : δ ^ (ε / 2) ≤ (κ ^ (2 / ε)) ^ (ε / 2) :=
          Real.rpow_le_rpow hδ.le hδκ (by linarith)
        have h2 : (κ ^ (2 / ε)) ^ (ε / 2) = κ := by
          rw [← Real.rpow_mul hκ.le, show 2 / ε * (ε / 2) = 1 by field_simp]
          exact Real.rpow_one _
        linarith [h2 ▸ h1]
      have hδε : δ ^ ε = δ ^ (ε / 2) * δ ^ (ε / 2) := by
        rw [← Real.rpow_add hδ]; ring_nf
      have hp : (0:ℝ) < δ ^ (ε / 2) := Real.rpow_pos_of_pos hδ _
      have hq : (0:ℝ) < lam ^ K := Real.rpow_pos_of_pos hlam _
      calc δ ^ ε * lam ^ K = δ ^ (ε / 2) * lam ^ K * δ ^ (ε / 2) := by rw [hδε]; ring
        _ ≤ δ ^ (ε / 2) * 1 * κ := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hlamK hp.le) hδhalf hp.le (by positivity)
        _ = κ * δ ^ (ε / 2) := by ring
    have hnn : (0:ℝ) ≤ (KTCW δ n p v)⁻¹ * ((n : ℝ) * tubeVol δ) := by positivity
    calc δ ^ ε * lam ^ K * (KTCW δ n p v)⁻¹ * ((n : ℝ) * tubeVol δ)
        = (δ ^ ε * lam ^ K) * ((KTCW δ n p v)⁻¹ * ((n : ℝ) * tubeVol δ)) := by ring
      _ ≤ (κ * δ ^ (ε / 2)) * ((KTCW δ n p v)⁻¹ * ((n : ℝ) * tubeVol δ)) :=
          mul_le_mul_of_nonneg_right hstep hnn
      _ = κ * δ ^ (ε / 2) * (KTCW δ n p v)⁻¹ * ((n : ℝ) * tubeVol δ) := by ring
  · -- the density is below `δ^η`; a single shaded tube already beats the right-hand side
    have huniv : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hsum : ∑ _i : Fin n, lam * tubeVol δ ≤ ∑ i, (volume (Y i)).toReal := by
      refine le_trans (le_of_eq ?_) hdense
      simp [Finset.sum_const, Finset.card_univ]
      ring
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le huniv hsum
    have hvol : lam * tubeVol δ ≤ (volume (shadingUnion Y)).toReal := by
      refine le_trans hi ?_
      have hsubU : shadingUnion Y ⊆ closedBall (0 : E3) 1 :=
        iUnion_subset fun j => subset_trans (hTS.2.2.2.2.1 j) (hTS.2.2.1 j)
      have hfin : volume (shadingUnion Y) ≠ ⊤ :=
        ne_top_of_le_ne_top (measure_closedBall_lt_top).ne (measure_mono hsubU)
      exact ENNReal.toReal_mono hfin (measure_mono (subset_iUnion _ i))
    refine le_trans ?_ hvol
    -- bound the right-hand side by `λ B δ^{ε+η+3}` and compare with `3 λ δ²`
    have hlamK : lam ^ K ≤ lam * δ ^ (η + 3) := by
      have hK1 : (0:ℝ) ≤ K - 1 := by
        have h : (0:ℝ) < 3 / η := by positivity
        rw [hK]; linarith
      have h1 : lam ^ (K - 1) ≤ (δ ^ η) ^ (K - 1) := Real.rpow_le_rpow hlam.le hcase.le hK1
      have h2 : (δ ^ η) ^ (K - 1) = δ ^ (η + 3) := by
        rw [← Real.rpow_mul hδ.le]
        congr 1
        rw [hK]
        field_simp
        ring
      have hKe : (1:ℝ) + (K - 1) = K := by ring
      have h3 : lam ^ K = lam * lam ^ (K - 1) := by
        nth_rewrite 1 [← hKe]
        rw [Real.rpow_add hlam, Real.rpow_one]
      rw [h3, ← h2]
      exact mul_le_mul_of_nonneg_left h1 hlam.le
    have hδpow : B * δ ^ (ε + (η + 3)) ≤ 3 * δ ^ (2:ℝ) := by
      have h1 : δ ^ (ε + (η + 3)) ≤ δ ^ ((2:ℝ) + 1) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      have h2 : δ ^ ((2:ℝ) + 1) = δ ^ (2:ℝ) * δ := by
        rw [Real.rpow_add hδ, Real.rpow_one]
      have h3 : B * δ ≤ 3 := by
        rw [le_div_iff₀ hB] at hδB
        linarith
      have h4 : (0:ℝ) < δ ^ (2:ℝ) := Real.rpow_pos_of_pos hδ _
      calc B * δ ^ (ε + (η + 3)) ≤ B * (δ ^ (2:ℝ) * δ) := by
            rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hB.le
        _ = (B * δ) * δ ^ (2:ℝ) := by ring
        _ ≤ 3 * δ ^ (2:ℝ) := mul_le_mul_of_nonneg_right h3 h4.le
    have hsq : δ ^ (2:ℝ) = δ ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hεpos : (0:ℝ) < δ ^ ε := Real.rpow_pos_of_pos hδ _
    calc δ ^ ε * lam ^ K * (KTCW δ n p v)⁻¹ * ((n : ℝ) * tubeVol δ)
        = (δ ^ ε * lam ^ K) * ((KTCW δ n p v)⁻¹ * ((n : ℝ) * tubeVol δ)) := by ring
      _ ≤ (δ ^ ε * (lam * δ ^ (η + 3))) * B := by
          refine mul_le_mul ?_ hmB (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hlamK hεpos.le
      _ = lam * (B * (δ ^ ε * δ ^ (η + 3))) := by ring
      _ = lam * (B * δ ^ (ε + (η + 3))) := by rw [← Real.rpow_add hδ]
      _ ≤ lam * (3 * δ ^ (2:ℝ)) := mul_le_mul_of_nonneg_left hδpow hlam.le
      _ = lam * (3 * δ ^ 2) := by rw [hsq]
      _ ≤ lam * tubeVol δ := mul_le_mul_of_nonneg_left hTVlow hlam.le
