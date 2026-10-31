-- Prove2me | solution 1 for WainwrightHDS.NucNorm.nuclear_norm_ls_frobenius_oracle_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:41:54.267157+00:00
-- url     : https://prove2.me/submissions/cd006861-ae6f-4816-968c-f5bda4d52ddc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_obsOp
import Definitions.Def_WainwrightHDS_NucNorm_frobSq
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_WainwrightHDS_NucNorm_lsNucObjective
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Theorems.Thm_WainwrightHDS_NucNorm_nuclear_norm_ls_quadratic_bound

namespace WainwrightHDS.NucNorm

lemma frobSq_nonneg {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₂) ℝ) : 0 ≤ frobSq A := by
  unfold frobSq
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem nuclear_norm_ls_frobenius_oracle_bound {n d₁ d₂ : ℕ}
    (X : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ) (Θstar : Matrix (Fin d₁) (Fin d₂) ℝ)
    (w y : Fin n → ℝ) (hy : ∀ i, y i = obsOp X Θstar i + w i)
    (κ c₀ lam : ℝ) (hκ : 0 < κ) (hc₀ : 0 < c₀) (hlam : 0 < lam)
    (hRSC : ∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ,
      1 / (2 * (n : ℝ)) * ∑ i, (obsOp X Δ i) ^ 2 ≥
        κ / 2 * frobSq Δ - c₀ * (((d₁ : ℝ) + d₂) / n) * nucNorm Δ ^ 2)
    (hG : opNorm2 ((1 / (n : ℝ)) • ∑ i, w i • X i) ≤ lam / 2)
    (Θhat : Matrix (Fin d₁) (Fin d₂) ℝ)
    (hmin : ∀ Θ : Matrix (Fin d₁) (Fin d₂) ℝ, lsNucObjective X y lam Θhat ≤ lsNucObjective X y lam Θ)
    (r : ℕ) (hr₁ : 1 ≤ r) (hrd : r ≤ min d₁ d₂)
    (hrκ : 128 * c₀ * ((d₁ : ℝ) + d₂) * r ≤ κ * n) :
    frobSq (Θhat - Θstar) ≤
      9 / 2 * (lam ^ 2 / κ ^ 2) * r +
        1 / κ * (2 * lam * ∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar +
          32 * c₀ * ((d₁ : ℝ) + d₂) / n *
            (∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar) ^ 2) := by
  have hquad := nuclear_norm_ls_quadratic_bound X Θstar w y hy κ c₀ lam hκ hc₀ hlam hRSC hG Θhat hmin r hr₁ hrd hrκ
  set Δ := Θhat - Θstar
  set F := Real.sqrt (frobSq Δ)
  set S := ∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar
  have hF_sq : F ^ 2 = frobSq Δ := Real.sq_sqrt (frobSq_nonneg Δ)
  have h2r_nonneg : (0 : ℝ) ≤ 2 * (r : ℝ) := by positivity
  have hsqrt2r_sq : (Real.sqrt (2 * (r : ℝ))) ^ 2 = 2 * (r : ℝ) := Real.sq_sqrt h2r_nonneg
  set b := 3 / 2 * (lam / κ) * Real.sqrt (2 * (r : ℝ))
  set C := 1 / κ * (lam * S + 16 * c₀ * ((d₁ : ℝ) + d₂) / n * S ^ 2)
  have h_ineq : F ^ 2 ≤ b * F + C := by
    have h1 : κ * F ^ 2 ≤ κ * (b * F + C) := by
      calc κ * F ^ 2 = κ * frobSq Δ := by rw [hF_sq]
        _ ≤ 3 / 2 * lam * Real.sqrt (2 * r) * F + lam * S +
              16 * c₀ * ((d₁ : ℝ) + d₂) / n * S ^ 2 := hquad
        _ = κ * (b * F + C) := by
              dsimp [b, C]
              field_simp [hκ.ne']
              ring
    exact le_of_mul_le_mul_left h1 hκ
  have hb_sq : b ^ 2 = 9 / 2 * (lam ^ 2 / κ ^ 2) * (r : ℝ) := by
    calc b ^ 2 = (3 / 2 * (lam / κ)) ^ 2 * (Real.sqrt (2 * (r : ℝ))) ^ 2 := by ring
      _ = (3 / 2 * (lam / κ)) ^ 2 * (2 * (r : ℝ)) := by rw [hsqrt2r_sq]
      _ = 9 / 2 * (lam ^ 2 / κ ^ 2) * (r : ℝ) := by ring
  have h_complete_sq : F ^ 2 ≤ b ^ 2 + 2 * C := by
    nlinarith [sq_nonneg (F - b)]
  calc frobSq Δ = F ^ 2 := hF_sq.symm
    _ ≤ b ^ 2 + 2 * C := h_complete_sq
    _ = 9 / 2 * (lam ^ 2 / κ ^ 2) * r +
          1 / κ * (2 * lam * S + 32 * c₀ * ((d₁ : ℝ) + d₂) / n * S ^ 2) := by
        rw [hb_sq]
        dsimp [C]
        ring

end WainwrightHDS.NucNorm

abbrev solution := @WainwrightHDS.NucNorm.nuclear_norm_ls_frobenius_oracle_bound

