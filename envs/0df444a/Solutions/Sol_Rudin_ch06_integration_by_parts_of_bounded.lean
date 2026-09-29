-- Prove2me | solution 1 for Rudin.ch06_integration_by_parts_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T13:22:05.515329+00:00
-- url     : https://prove2.me/submissions/6761f03b-61eb-4021-a51d-cc4801f92fa9

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_ch06_linearity
import Theorems.Thm_Rudin_ch06_continuous_integrable
import Theorems.Thm_Rudin_ch06_fundamental_theorem_of_bounded
import Theorems.Thm_Rudin_ch06_product_integrable_of_bounded

open Filter Topology

open Rudin in
/-- Rudin, Theorem 6.22 (integration by parts), with the boundedness hypotheses of Chapter 6. -/
theorem solution (a b : ℝ) (hab : a ≤ b) (F G f g : ℝ → ℝ)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x)
    (hG : ∀ x ∈ Set.Icc a b, HasDerivAt G (g x) x)
    (hf : RiemannIntegrable a b f) (hg : RiemannIntegrable a b g)
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hgb : ∃ M, ∀ x ∈ Set.Icc a b, |g x| ≤ M) :
    RiemannIntegral a b (fun x => F x * g x) =
      F b * G b - F a * G a - RiemannIntegral a b (fun x => f x * G x) := by
  have hmonoid : MonotoneOn (id : ℝ → ℝ) (Set.Icc a b) := monotone_id.monotoneOn _
  -- `F` and `G` are continuous, hence integrable and bounded on `[a, b]`
  have hFc : ContinuousOn F (Set.Icc a b) := fun x hx => ((hF x hx).continuousAt).continuousWithinAt
  have hGc : ContinuousOn G (Set.Icc a b) := fun x hx => ((hG x hx).continuousAt).continuousWithinAt
  obtain ⟨CF, hCF⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hFc
  obtain ⟨CG, hCG⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hGc
  have hFb : ∃ M, ∀ x ∈ Set.Icc a b, |F x| ≤ M := ⟨CF, fun x hx => by simpa [Real.norm_eq_abs] using hCF x hx⟩
  have hGb : ∃ M, ∀ x ∈ Set.Icc a b, |G x| ≤ M := ⟨CG, fun x hx => by simpa [Real.norm_eq_abs] using hCG x hx⟩
  have hFi : RiemannIntegrable a b F := ch06_continuous_integrable a b hab F id hmonoid hFc
  have hGi : RiemannIntegrable a b G := ch06_continuous_integrable a b hab G id hmonoid hGc
  -- the two products are integrable and bounded
  have hFg : RSIntegrable a b (fun x => F x * g x) id :=
    ch06_product_integrable_of_bounded a b hab F g id hmonoid hFi hg hFb hgb
  have hfG : RSIntegrable a b (fun x => f x * G x) id :=
    ch06_product_integrable_of_bounded a b hab f G id hmonoid hf hGi hfb hGb
  obtain ⟨MF, hMF⟩ := hFb
  obtain ⟨MG, hMG⟩ := hGb
  obtain ⟨Mf, hMf⟩ := hfb
  obtain ⟨Mg, hMg⟩ := hgb
  have hFgb : ∃ M, ∀ x ∈ Set.Icc a b, |F x * g x| ≤ M :=
    ⟨MF * Mg, fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hMF x hx) (hMg x hx) (abs_nonneg _)
        (le_trans (abs_nonneg _) (hMF x hx))⟩
  have hfGb : ∃ M, ∀ x ∈ Set.Icc a b, |f x * G x| ≤ M :=
    ⟨Mf * MG, fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hMf x hx) (hMG x hx) (abs_nonneg _)
        (le_trans (abs_nonneg _) (hMf x hx))⟩
  -- the sum `h = f G + F g` is integrable, with integral the sum of the two integrals
  have hhb : ∃ M, ∀ x ∈ Set.Icc a b, |f x * G x + F x * g x| ≤ M :=
    ⟨Mf * MG + MF * Mg, fun x hx => by
      refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul (hMf x hx) (hMG x hx) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hMf x hx))
      · rw [abs_mul]
        exact mul_le_mul (hMF x hx) (hMg x hx) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hMF x hx))⟩
  obtain ⟨hsum, hsumval, -, -⟩ :=
    ch06_linearity a b hab (fun x => f x * G x) (fun x => F x * g x) id 0 hmonoid hfG hFg hfGb hFgb
  -- the fundamental theorem applied to `F G`
  have hderiv : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun y => F y * G y) (f x * G x + F x * g x) x :=
    fun x hx => (hF x hx).mul (hG x hx)
  have hFTC : RiemannIntegral a b (fun x => f x * G x + F x * g x)
      = F b * G b - F a * G a :=
    ch06_fundamental_theorem_of_bounded a b hab (fun x => f x * G x + F x * g x)
      (fun x => F x * G x) hsum hhb hderiv
  have e1 : RiemannIntegral a b (fun x => f x * G x + F x * g x)
      = RiemannIntegral a b (fun x => f x * G x) + RiemannIntegral a b (fun x => F x * g x) :=
    hsumval
  linarith [hFTC, e1]
