-- Prove2me | solution 1 for PositivityTheory.RgJS.convergence_of_landau_euler
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:34.008099+00:00
-- url     : https://prove2.me/submissions/716b7255-ed6d-4c46-8eb2-8436e6b358a6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_DiagonalTermNorms_ConvergenceOfLandauEuler
import Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_ll_nonneg
import Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_cd_nonneg
import Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_lterm_diag
import Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_norm_lterm_diag
import Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_norm_lterm_le
import Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_norm_lterm_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.RgJS
open DiagonalEntryNormBounds
namespace PositivityTheory.RgJS
theorem _root_.solution : LandauL → EulerLog → Conv1 := by
  intro hL hE W q X d A hS
  have hq := hS.primes.two

  have diag : ∀ x : X, ∀ σ : ℝ, 1 < σ → Summable fun p => ‖lterm q (A x) (A x) σ p‖ := by
    intro x
    obtain ⟨F, σ₀, hF, hFe⟩ := hS.rs x x
    set σ₁ : ℝ := max σ₀ 2 with hσ₁
    have hsum : ∀ σ : ℝ, σ₁ < σ → Summable fun p => cd (A x) p * Real.exp (-(ll q p * σ)) := by
      intro σ hσ
      have h2 : 2 < (σ : ℂ).re := by simp; exact lt_of_le_of_lt (le_max_right _ _) hσ
      have := (hE W q _ _ (A x) (A x) σ hS.primes (hS.bd x) (hS.bd x) h2).1
      exact this.congr fun p => norm_lterm_diag q hq (A x) σ p
    have key := hL (W × ℕ) (cd (A x)) (ll q) 1 σ₁ (fun s => F s / (s - 1)) (cd_nonneg (A x)) (ll_nonneg q hq)
      (fun σ hσ => by
        have h1 : ((σ : ℂ) - 1) ≠ 0 := by
          intro h; have := congrArg Complex.re h; simp at this; linarith
        exact (hF σ (by linarith)).div (analyticAt_id.sub analyticAt_const) h1)
      hsum
      (fun σ hσ => by
        have hσ0 : σ₀ < σ := lt_of_le_of_lt (le_max_left _ _) hσ
        have h2 : 2 < (σ : ℂ).re := by simp; exact lt_of_le_of_lt (le_max_right _ _) hσ
        have h1 : ((σ : ℂ) - 1) ≠ 0 := by
          intro h; have := congrArg Complex.re h; simp at this; linarith [le_max_right σ₀ 2]
        rw [hFe σ hσ0, if_pos rfl, mul_div_cancel_left₀ _ h1,
          (hE W q _ _ (A x) (A x) σ hS.primes (hS.bd x) (hS.bd x) h2).2.1]
        have e : (∑' p, lterm q (A x) (A x) (σ : ℂ) p) = ((∑' p, cd (A x) p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_tsum]
          exact tsum_congr fun p => lterm_diag q hq (A x) σ p
        rw [e, ← Complex.ofReal_exp])
    intro σ hσ
    exact (key σ hσ).congr fun p => (norm_lterm_diag q hq (A x) σ p).symm
  have all : ∀ x y : X, ∀ σ : ℝ, 1 < σ → Summable fun p => ‖lterm q (A x) (A y) σ p‖ := by
    intro x y σ hσ
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_lterm_le q hq (A x) (A y) σ p) ?_
    exact ((diag x σ hσ).add (diag y σ hσ)).div_const 2
  intro x y
  refine ⟨all x y, fun σ₁ hσ₁ => ⟨∑' p, ‖lterm q (A x) (A y) σ₁ p‖, fun σ hσ => ?_⟩⟩
  refine (norm_tsum_le_tsum_norm (all x y σ (by linarith))).trans ?_
  exact (all x y σ (by linarith)).tsum_le_tsum (fun p => norm_lterm_anti q hq (A x) (A y) hσ p) (all x y σ₁ hσ₁)
end PositivityTheory.RgJS
