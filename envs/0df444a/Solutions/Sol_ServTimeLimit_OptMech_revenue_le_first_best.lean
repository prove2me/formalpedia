-- Prove2me | solution 1 for ServTimeLimit.OptMech.revenue_le_first_best
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:38:33.027764+00:00
-- url     : https://prove2.me/submissions/dfc02691-af25-49bc-8947-0ad1b9336a73

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

open MeasureTheory

open ServTimeLimit.OptMech in
theorem solution (P : Params) (hP : P.Standing) (Φ : Set ℝ) (t p : ℝ → ℝ)
    (hM : IsMechanism P Φ t p) (hIR : IsIR P Φ t p) :
    revenue P Φ p ≤ welfare P Φ t ∧
    ∀ (Φs : Set ℝ) (ts : ℝ → ℝ), IsFirstBest P Φs ts → revenue P Φ p ≤ welfare P Φs ts := by
  obtain ⟨hA, hpm, hpi, hp0⟩ := hM
  obtain ⟨hΦ, hsub, htm, ht, hload⟩ := hA
  have hfin : volume Φ ≠ ⊤ := ((measure_mono hsub).trans_lt measure_Icc_lt_top).ne
  have hti : IntegrableOn t Φ volume := by
    refine Measure.integrableOn_of_bounded (M := P.θbar) hfin htm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hΦ).mpr (Filter.Eventually.of_forall fun θ hθ => ?_)
    have h1 := ht θ hθ
    have h2 := (hsub hθ).2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h1.1, h1.2]
  have hgi : IntegrableOn (fun θ => t θ - P.c * waitTime P Φ t) Φ volume :=
    hti.sub (integrableOn_const hfin)
  have hint : ∫ θ in Φ, p θ ≤ ∫ θ in Φ, (t θ - P.c * waitTime P Φ t) := by
    refine setIntegral_mono_on hpi hgi hΦ (fun θ hθ => ?_)
    have h1 := hIR θ hθ
    have h2 : min (t θ) θ ≤ t θ := min_le_left _ _
    linarith
  have hcoef : 0 ≤ P.Lam / P.θbar := div_nonneg hP.1.le hP.2.2.le
  have h1 : revenue P Φ p ≤ welfare P Φ t := by
    unfold revenue welfare
    exact mul_le_mul_of_nonneg_left hint hcoef
  refine ⟨h1, fun Φs ts hfb => h1.trans (hfb.2 Φ t ⟨hΦ, hsub, htm, ht, hload⟩)⟩
