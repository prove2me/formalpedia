-- Prove2me | solution 1 for ObfImpossibility.PseudoOracle.density_bound
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-23T23:52:16.318764+00:00
-- url     : https://prove2.me/submissions/b2610b2b-e0d9-4c6c-b202-7390e1e5fbe6

import Mathlib
import Theorems.Thm_ObfImpossibility_PseudoOracle_lemma_B_1

open Filter ObfImpossibility.PseudoOracle

private lemma exponential_tail (q : ℝ) (hq : 16 ≤ q) :
    (2 : ℝ) ^ (-q) < 1 / q := by
  have hq0 : 0 < q := by linarith
  have hlarge : q < (2 : ℝ) ^ q := by
    calc
      q < (1 + q / 4) ^ 2 := by
        nlinarith [mul_nonneg hq0.le (sub_nonneg.mpr hq)]
      _ ≤ (Real.exp (q / 4)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (q / 4)]) 2
      _ = Real.exp (q / 2) := by
        rw [pow_two, ← Real.exp_add]
        congr 1 <;> ring
      _ ≤ (2 : ℝ) ^ q := by
        rw [Real.rpow_def_of_pos (by norm_num)]
        apply Real.exp_le_exp.mpr
        nlinarith [Real.log_two_gt_d9]
  rw [Real.rpow_neg (by norm_num), inv_eq_one_div]
  exact one_div_lt_one_div_of_lt hq0 hlarge

theorem solution :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ K₀ : ℕ, ∀ K L : ℕ,
      K₀ ≤ K → K ^ 2 ≤ L → ∀ D : Fin L → QTree K L,
      (∀ y, ((D y).depth : ℝ) ≤ (K : ℝ) ^ δ) →
        ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
            1 / (K : ℝ) ^ δ < |prX D G - prY D G|).card : ℝ) /
          (Fintype.card (Fin K ↪ Fin L) : ℝ) < (K : ℝ) ^ (-δ) := by
  classical
  obtain ⟨d, hd, N, hmain⟩ := lemma_B_1
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδd
  have ev : ∀ᶠ K : ℕ in atTop, (16 : ℝ) ≤ (K : ℝ) ^ d :=
    ((tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 16
  obtain ⟨M, hM⟩ := eventually_atTop.mp ev
  refine ⟨max N (max M 1), ?_⟩
  intro K L hK hKL D hD
  have hKN : N ≤ K := le_trans (le_max_left _ _) hK
  have hKM : M ≤ K := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK
  have hK1 : 1 ≤ K := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK
  have hKr1 : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hKpos : (0 : ℝ) < K := by linarith
  have hpow : (K : ℝ) ^ δ ≤ (K : ℝ) ^ d :=
    Real.rpow_le_rpow_of_exponent_le hKr1 hδd
  have hthreshold : 1 / (K : ℝ) ^ d ≤ 1 / (K : ℝ) ^ δ :=
    one_div_le_one_div_of_le (by positivity) hpow
  have hBpos : (0 : ℝ) < Fintype.card (Fin K ↪ Fin L) := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    exact_mod_cast Nat.descFactorial_pos.mpr (by nlinarith)
  have hgood := hmain K L hKN hKL D (fun y => (hD y).trans hpow)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin K ↪ Fin L)))
    (fun G => |prX D G - prY D G| ≤ 1 / (K : ℝ) ^ d)
  simp only [not_le, Finset.card_univ] at hsplit
  have hsplit' :
      ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
          |prX D G - prY D G| ≤ 1 / (K : ℝ) ^ d).card : ℝ) +
      ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
          1 / (K : ℝ) ^ d < |prX D G - prY D G|).card : ℝ) =
        (Fintype.card (Fin K ↪ Fin L) : ℝ) := by exact_mod_cast hsplit
  have hbad :
      ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
          1 / (K : ℝ) ^ d < |prX D G - prY D G|).card : ℝ) /
        (Fintype.card (Fin K ↪ Fin L) : ℝ) ≤ (2 : ℝ) ^ (-(K : ℝ) ^ d) := by
    rw [div_le_iff₀ hBpos]
    rw [le_div_iff₀ hBpos] at hgood
    nlinarith
  have hsub : (Finset.univ.filter fun G : Fin K ↪ Fin L =>
          1 / (K : ℝ) ^ δ < |prX D G - prY D G|) ⊆
      (Finset.univ.filter fun G : Fin K ↪ Fin L =>
          1 / (K : ℝ) ^ d < |prX D G - prY D G|) := by
    intro G hG
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ G,
      hthreshold.trans_lt (Finset.mem_filter.mp hG).2⟩
  calc
    _ ≤ ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
            1 / (K : ℝ) ^ d < |prX D G - prY D G|).card : ℝ) /
          (Fintype.card (Fin K ↪ Fin L) : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hBpos.le
    _ ≤ (2 : ℝ) ^ (-(K : ℝ) ^ d) := hbad
    _ < 1 / (K : ℝ) ^ d := exponential_tail _ (hM K hKM)
    _ ≤ 1 / (K : ℝ) ^ δ := hthreshold
    _ = (K : ℝ) ^ (-δ) := by rw [Real.rpow_neg hKpos.le, one_div]
