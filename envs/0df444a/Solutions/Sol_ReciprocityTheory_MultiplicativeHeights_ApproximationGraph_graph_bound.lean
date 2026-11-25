-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.graph_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:06:06.123677+00:00
-- url     : https://prove2.me/submissions/6791ba0f-4bed-4a27-9d1c-ad3c3c6d63ca

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_approxR_nonneg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_euc_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_euc_smul
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_negPart_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_negPart_smul
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_norm_err_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_norm_negPart_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_norm_posPart_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posPart_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posPart_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
open ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
theorem _root_.solution {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    ‖euc (negPart p (∑ j, w j • X j))‖ ≤ ρ / 3 * ‖euc (posPart p (∑ j, w j • X j))‖ ∧
      3 * (√(r : ℝ) * μ * ‖euc w‖) ≤ ‖euc (posPart p (∑ j, w j • X j))‖ := by
  set R := approxR r μ ρ with hRdef
  have hR0 : 0 ≤ R := approxR_nonneg r hμ hρ
  set E : Fin r → ℂ := ∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) with hE
  have hEn : ‖euc E‖ ≤ √(r : ℝ) * μ * ‖euc w‖ := norm_err_le X hX hμ.le w hw

  have hsum : ∑ j, w j • X j = (R : ℂ) • w + E := by
    ext k
    simp [hE, Finset.sum_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hpw : posPart p w = w := by
    ext k
    simp only [posPart]
    split_ifs with h
    · rfl
    · exact (hw k (not_lt.mp h)).symm
  have hnw : negPart p w = 0 := by
    ext k
    simp only [negPart, Pi.zero_apply]
    split_ifs with h
    · rfl
    · exact hw k (not_lt.mp h)
  have hpos : posPart p (∑ j, w j • X j) = (R : ℂ) • w + posPart p E := by
    rw [hsum, posPart_add, posPart_smul, hpw]
  have hneg : negPart p (∑ j, w j • X j) = negPart p E := by
    rw [hsum, negPart_add, negPart_smul, hnw, smul_zero, zero_add]
  set s := √(r : ℝ) * μ * ‖euc w‖ with hs
  have hs0 : 0 ≤ s := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hμ.le) (norm_nonneg _)
  have hnegle : ‖euc (negPart p (∑ j, w j • X j))‖ ≤ s := by
    rw [hneg]; exact (norm_negPart_le p E).trans hEn
  have hRw : ‖euc ((R : ℂ) • w)‖ = 4 * s / ρ := by
    rw [euc_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hR0, hRdef, approxR, hs]
    ring
  have hposge : 4 * s / ρ - s ≤ ‖euc (posPart p (∑ j, w j • X j))‖ := by
    rw [hpos, euc_add]
    have h1 := norm_sub_le (euc ((R : ℂ) • w) + euc (posPart p E)) (euc (posPart p E))
    rw [add_sub_cancel_right] at h1
    have h2 := (norm_posPart_le p E).trans hEn
    linarith
  have hq : 4 * s ≤ 4 * s / ρ := by
    rw [le_div_iff₀ hρ]; nlinarith
  have hqρ : 4 * s / ρ * ρ = 4 * s := div_mul_cancel₀ _ hρ.ne'
  refine ⟨?_, by linarith⟩
  calc ‖euc (negPart p (∑ j, w j • X j))‖ ≤ s := hnegle
    _ ≤ ρ / 3 * (4 * s / ρ - s) := by nlinarith [mul_le_mul_of_nonneg_right hρ1 hs0]
    _ ≤ ρ / 3 * ‖euc (posPart p (∑ j, w j • X j))‖ :=
      mul_le_mul_of_nonneg_left hposge (by positivity)
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
