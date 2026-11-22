-- Prove2me | solution 1 for PettisIntegral.hasPettisIntegral_integral
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:29:42.994802+00:00
-- url     : https://prove2.me/submissions/e23f6186-3d8a-4708-bbe5-033e1d14399f

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

open PettisIntegral

theorem solution {𝕜 E X : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace X] (μ : Measure X)
    (f : X → E) (hf : Integrable f μ) :
    HasPettisIntegral 𝕜 μ f (∫ x, f x ∂μ) ∧ pettisIntegral 𝕜 μ f = ∫ x, f x ∂μ := by
  have h : HasPettisIntegral 𝕜 μ f (∫ x, f x ∂μ) :=
    ⟨fun φ => φ.integrable_comp hf, fun φ => (φ.integral_comp_comm hf).symm⟩
  refine ⟨h, ?_⟩
  have hI : PettisIntegrable 𝕜 μ f := ⟨_, h⟩
  unfold pettisIntegral
  rw [dif_pos hI]
  have h2 := Classical.choose_spec hI
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)]
  intro φ
  rw [h2.2 φ, h.2 φ]
