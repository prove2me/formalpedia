-- Prove2me | solution 1 for QAlgorithms.Nannicini.adiabatic_theorem_linInterp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T01:09:42.251274+00:00
-- url     : https://prove2.me/submissions/d8aa0956-ddd1-46c8-9b2a-a1b621d36ff0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QAlgorithms_Nannicini_adiabatic_theorem_integral_gap
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
universe u

open QAlgorithms
open MeasureTheory
open scoped Matrix.Norms.L2Operator

theorem solution :
    ∃ c : ℝ, ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (HI HF : Matrix ι ι ℂ),
      HI.IsHermitian → HF.IsHermitian →
      ∀ (lam : ℝ → ℝ), ContinuousOn lam (Set.Icc 0 1) →
      ∀ (φ : ℝ → EuclideanSpace ℂ ι),
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsState (φ s) ∧ act (linInterp HI HF s) (φ s) = (lam s : ℂ) • φ s) →
      ∀ (γ : ℝ), 0 < γ →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (linInterp HI HF s) (lam s) γ) →
      ∀ (δ : ℝ), 0 < δ → ∀ (T : ℝ),
      c / δ * (specNorm (HF - HI) / γ ^ 2 + specNorm (HF - HI) ^ 2 / γ ^ 3) ≤ T →
      ∀ (ψ : ℝ → EuclideanSpace ℂ ι), SolvesAdiabaticPlus (linInterp HI HF) T ψ → ψ 0 = φ 0 →
      ∃ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) • ψ 1 - φ 1‖ ≤ δ := by
  obtain ⟨c, hc⟩ := QAlgorithms.Nannicini.adiabatic_theorem_integral_gap.{u}
  refine ⟨2 * |c|, ?_⟩
  intro ι _ _ HI HF _hHI _hHF lam hlam φ hφ γ hγ hgap δ hδ T hT ψ hψ hψ0
  let D := HF - HI
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => linInterp HI HF t i j) (D i j) (Set.Icc 0 1) s := by
    intro s _hs i j
    have h := ((hasDerivAt_const s (1 : ℂ)).sub (Complex.ofRealCLM.hasDerivAt (x := s))).mul_const (HI i j)
    have h' := (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (HF i j)
    convert (h.add h').hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1) using 1
    · rfl
    · funext t
      simp [linInterp, Complex.ofRealCLM_apply, sub_eq_add_neg, add_comm]
    · simp [D, Complex.ofRealCLM_apply, sub_eq_add_neg, add_comm]
  have hdd : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun _ : ℝ => D i j) ((0 : Matrix ι ι ℂ) i j) (Set.Icc 0 1) s := by
    intro s _ i j
    simpa using hasDerivWithinAt_const s (Set.Icc (0 : ℝ) 1) (D i j)
  have hzero : specNorm (0 : Matrix ι ι ℂ) = 0 := by simp [specNorm]
  have hn : 0 ≤ specNorm D := by unfold specNorm; positivity
  have hint : IntervalIntegrable
      (fun _ : ℝ => specNorm D ^ 2 / γ ^ 3 + specNorm (0 : Matrix ι ι ℂ) / γ ^ 2)
      volume 0 1 := intervalIntegrable_const
  have hbound : c / δ * (specNorm D / γ ^ 2 + specNorm D / γ ^ 2 +
      ∫ _ in (0 : ℝ)..1, (specNorm D ^ 2 / γ ^ 3 + specNorm (0 : Matrix ι ι ℂ) / γ ^ 2)) ≤ T := by
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, one_smul, hzero, zero_div, add_zero]
    have ha : 0 ≤ specNorm D / γ ^ 2 := by positivity
    have hb : 0 ≤ specNorm D ^ 2 / γ ^ 3 := by positivity
    calc
      c / δ * (specNorm D / γ ^ 2 + specNorm D / γ ^ 2 + specNorm D ^ 2 / γ ^ 3)
          ≤ |c| / δ * (specNorm D / γ ^ 2 + specNorm D / γ ^ 2 + specNorm D ^ 2 / γ ^ 3) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self c) hδ.le) (by positivity)
      _ ≤ 2 * |c| / δ * (specNorm D / γ ^ 2 + specNorm D ^ 2 / γ ^ 3) := by
        have hc0 : 0 ≤ |c| / δ := by positivity
        calc
          _ ≤ |c| / δ * (2 * (specNorm D / γ ^ 2 + specNorm D ^ 2 / γ ^ 3)) :=
            mul_le_mul_of_nonneg_left (by linarith) hc0
          _ = _ := by ring
      _ ≤ T := hT
  exact hc (linInterp HI HF) (fun _ => D) (fun _ => 0) hd hdd
    lam hlam φ hφ (fun _ => γ) γ hγ (fun s hs => ⟨le_rfl, hgap s hs⟩)
    hint δ hδ T hbound ψ hψ hψ0
