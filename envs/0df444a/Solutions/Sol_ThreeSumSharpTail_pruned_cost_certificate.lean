-- Prove2me | solution 1 for ThreeSumSharpTail.pruned_cost_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T17:55:09.637601+00:00
-- url     : https://prove2.me/submissions/4d26284b-72e5-4610-ac64-8629366f320c

import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_APSP299791_Defs4
import Theorems.Thm_ThreeSumSharpTail_pruned_encoding_comparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ThreeSumApsp

namespace ThreeSumSharpTail

private theorem actual_entropy_eq_sharp (x : ℝ) :
    ThreeSumApsp.entropy x = ThreeSumSharpTail.entropy x := by
  rfl

private theorem actual_GammaOf_eq_sharpSaving (c θ : ℝ) :
    ThreeSumApsp.GammaOf c θ = ThreeSumSharpTail.sharpSaving c θ := by
  simp [ThreeSumApsp.GammaOf, ThreeSumApsp.entropy,
    ThreeSumSharpTail.sharpSaving, ThreeSumSharpTail.entropy]

private theorem actual_qOf_eq_queryExponent (θ : ℝ) :
    ThreeSumApsp.qOf θ = ThreeSumSharpTail.queryExponent θ := by
  simp [ThreeSumApsp.qOf, ThreeSumApsp.entropy,
    ThreeSumSharpTail.queryExponent, ThreeSumSharpTail.entropy]

end ThreeSumSharpTail

open ThreeSumSharpTail

theorem solution (c : ℕ) (θ : ℝ) (a s : ℚ)
    (hc : 10 < c) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10)
    (ha0 : 0 < a)
    (henc : (a : ℝ) * (encodingExponent c + sharpSaving c θ) < 1)
    (hprep : (s : ℝ) < sharpSaving c θ)
    (hquery : (s : ℝ) < 1 / 2 - queryExponent θ) :
    ∃ C m₀, 0 ≤ C ∧ ∀ D₀ N m : ℕ,
      2 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
      m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → m₀ ≤ m →
      sqrtKN0 (levelsOf (c : ℝ) m) m ≤ N ∧
      cost8p (levelsOf (c : ℝ) m) m (switchOf θ m) N ≤
        C * ((N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ (s : ℝ)) ∧
      costQuery (levelsOf (c : ℝ) m) m (switchOf θ m) ≤
        C * ((D₀ : ℝ) ^ (1 / 2 - (s : ℝ)) * Real.log (D₀ : ℝ)) := by
  have hcR : 10 < (c : ℝ) := by exact_mod_cast hc
  have hApruned : ThreeSumApsp.Apruned (c : ℝ) ≤ encodingExponent (c : ℝ) := by
    have hcmp := ThreeSumSharpTail.pruned_encoding_comparison (c : ℝ) (by linarith)
    rw [ThreeSumApsp.Apruned, actual_entropy_eq_sharp]
    convert hcmp using 1 <;> ring_nf
  have hGamma := actual_GammaOf_eq_sharpSaving (c : ℝ) θ
  have hthin : (a : ℝ) *
      (ThreeSumApsp.Apruned (c : ℝ) + ThreeSumApsp.GammaOf (c : ℝ) θ) < 1 := by
    calc
      _ ≤ (a : ℝ) * (encodingExponent (c : ℝ) + sharpSaving (c : ℝ) θ) := by
        apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast ha0.le)
        rw [hGamma]
        nlinarith [hApruned]
      _ < 1 := henc
  let hp : ThreeSumApsp.AdmissibleP (c : ℝ) θ (a : ℝ) :=
    ⟨hcR, hθ0, by norm_num at hθ9 ⊢; exact hθ9, hthin⟩
  obtain ⟨C, m₀, hC, hcosts⟩ := ThreeSumApsp.CorollaryP.costs hp
  refine ⟨C, m₀, hC, fun D₀ N m hD hDN hm hm₀ => ?_⟩
  obtain ⟨hsize, hpre, hq⟩ := hcosts D₀ N m hD hDN hm hm₀
  have hD1 : 1 ≤ (D₀ : ℝ) := by exact_mod_cast (show 1 ≤ D₀ by omega)
  have hDpos : 0 < (D₀ : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (D₀ : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ D₀ by omega))
  have hsGamma : (s : ℝ) ≤ ThreeSumApsp.GammaOf (c : ℝ) θ := by
    rw [hGamma]
    exact le_of_lt hprep
  have hden : (D₀ : ℝ) ^ (s : ℝ) ≤
      (D₀ : ℝ) ^ ThreeSumApsp.GammaOf (c : ℝ) θ :=
    Real.rpow_le_rpow_of_exponent_le hD1 hsGamma
  have hfrac :
      ((N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2) /
          (D₀ : ℝ) ^ ThreeSumApsp.GammaOf (c : ℝ) θ ≤
      ((N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2) / (D₀ : ℝ) ^ (s : ℝ) := by
    apply div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos hDpos _)
    exact hden
  have hqexp : ThreeSumApsp.qOf θ ≤ 1 / 2 - (s : ℝ) := by
    rw [actual_qOf_eq_queryExponent]
    linarith
  have hqpow : (D₀ : ℝ) ^ ThreeSumApsp.qOf θ ≤
      (D₀ : ℝ) ^ (1 / 2 - (s : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hD1 hqexp
  refine ⟨hsize, ?_, ?_⟩
  · exact hpre.trans (mul_le_mul_of_nonneg_left hfrac hC)
  · calc
      costQuery (levelsOf (c : ℝ) m) m (switchOf θ m) ≤
          C * ((D₀ : ℝ) ^ ThreeSumApsp.qOf θ * Real.log (D₀ : ℝ)) := hq
      _ ≤ C * ((D₀ : ℝ) ^ (1 / 2 - (s : ℝ)) * Real.log (D₀ : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hqpow hlog) hC

#print axioms solution
