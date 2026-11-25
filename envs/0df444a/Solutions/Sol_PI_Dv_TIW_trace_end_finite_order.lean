-- Prove2me | solution 1 for PI.Dv.TIW.trace_end_finite_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:47:17.743086+00:00
-- url     : https://prove2.me/submissions/5dfa405c-f095-4ef0-a8d8-cb61185fbf89

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Theorems.Thm_PI_Dv_TIW_trace_finite_order

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Matrix
namespace PI.Dv.TIW
theorem _root_.solution {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (f : Module.End K W) (m : ℕ) (hm : 0 < m) (hf : f ^ m = 1) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K W f)‖ ≤ Module.finrank K W ∧ IsIntegral ℤ (LinearMap.trace K W f) := by
  set b := Module.finBasis K W
  set A := LinearMap.toMatrixAlgEquiv b f with hA
  have htr : LinearMap.trace K W f = A.trace := by
    rw [LinearMap.trace_eq_matrix_trace K b f, hA]; rfl
  have hAm : A ^ m = 1 := by rw [hA, ← map_pow, hf, map_one]
  set B := σ.mapMatrix A with hB
  have hBm : B ^ m = 1 := by rw [hB, ← map_pow, hAm, map_one]
  have hσtr : σ (A.trace) = B.trace := by
    simp [Matrix.trace, hB, map_sum]
  obtain ⟨h1, h2⟩ := trace_finite_order B m hm hBm
  rw [htr, hσtr]
  refine ⟨by simpa using h1, ?_⟩
  rw [← hσtr] at h2
  exact (isIntegral_algHom_iff σ.toIntAlgHom σ.injective).mp h2
end PI.Dv.TIW
