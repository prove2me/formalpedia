-- Prove2me | solution 1 for SchwartzSpaceWiki.lipschitz_and_uniformContinuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:07:08.569991+00:00
-- url     : https://prove2.me/submissions/5ec9e150-686e-434f-ac48-90072ca44a13

import Definitions.Def_SchwartzSpaceWiki_Defs

open SchwartzSpaceWiki
open scoped NNReal ENNReal

private lemma multi_single {n : ℕ} (i : Fin n) (f : Rn n → ℂ) :
    iteratedPartialDeriv (Pi.single i 1) f = partialDeriv i f := by
  classical
  have aux : ∀ l : List (Fin n), l.Nodup →
      l.foldr (fun j g => (partialDeriv j)^[(Pi.single i (1 : ℕ) : MultiIndex n) j] g) f =
        if i ∈ l then partialDeriv i f else f := by
    intro l hl
    induction l with
    | nil => simp
    | cons j l ih =>
      rw [List.nodup_cons] at hl
      rw [List.foldr_cons, ih hl.2]
      by_cases h : j = i
      · subst j
        simp [hl.1]
      · simp [h, Ne.symm h]
  simpa [iteratedPartialDeriv] using aux (List.finRange n) (List.nodup_finRange n)

theorem solution (n : ℕ) (f : Rn n → ℂ) (hf : f ∈ schwartzSpace n) :
    (∃ K : NNReal, LipschitzWith K f) ∧ UniformContinuous f := by
  classical
  let C : Fin n → ℝ≥0 := fun i => (schwartzSeminorm 0 (Pi.single i 1) f).toNNReal
  have hC (i : Fin n) (x : Rn n) : ‖partialDeriv i f x‖₊ ≤ C i := by
    apply ENNReal.le_toNNReal_of_coe_le _ (hf.2 0 (Pi.single i 1)).ne
    have h := le_iSup (fun y : Rn n =>
      ‖(monomial (0 : MultiIndex n) y : ℂ) * iteratedPartialDeriv (Pi.single i 1) f y‖ₑ) x
    simpa [monomial, multi_single, schwartzSeminorm, enorm] using h
  let K : ℝ≥0 := ∑ i, C i
  have hK : LipschitzWith K f := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hf.1.differentiable (by simp))
    intro x
    change ‖fderiv ℝ f x‖ ≤ (K : ℝ)
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hv : v = ∑ i : Fin n, (v i) • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      simp [EuclideanSpace.single, Pi.single_apply, Finset.sum_apply]
    calc
      ‖fderiv ℝ f x v‖ = ‖∑ i : Fin n, (v i) • partialDeriv i f x‖ := by
        conv_lhs => rw [hv]
        congr 1
        simp [map_sum, partialDeriv]
      _ ≤ ∑ i : Fin n, ‖(v i) • partialDeriv i f x‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ‖v‖ * (C i : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul]
        exact mul_le_mul (PiLp.norm_apply_le v i) (hC i x) (norm_nonneg _) (norm_nonneg _)
      _ = (K : ℝ) * ‖v‖ := by simp [K, Finset.sum_mul, mul_comm]
  exact ⟨⟨K, hK⟩, hK.uniformContinuous⟩
