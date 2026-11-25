-- Prove2me | solution 1 for PI.IsoInvMetricW.hv_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:59.956195+00:00
-- url     : https://prove2.me/submissions/1cd05806-93f6-4a88-ba0a-fa09be055e8b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_HvScalar
import Theorems.Thm_PI_IsoInvMetricW_hv_tri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical
open PI PI.IsoInvMetricW
open PI.IsoInvMetric
namespace PI.IsoInvMetricW
theorem _root_.solution {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} (nu : Lt → YoungDiagram)
    (w : Lt → Fin N → ℕ → ℂ) (hw : ∀ s (a : Fin N) (j : ℕ), j < a → w s a j = 0) :
    hvC N nu w =
      (∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), dg w s i) • u0 N nu := by
  have h1 : ∀ s (a : Fin N) (j : ℕ), j < a →
      (fun _ : Lt => colsOf (1 : Matrix (Fin N) (Fin N) ℂ)) s a j = 0 := by
    intro s a j hja
    simp only [colsOf]
    split_ifs with hj
    · rw [Matrix.one_apply_ne]
      intro h
      rw [h] at hja
      simp at hja
    · rfl
  funext J
  rw [Pi.smul_apply, smul_eq_mul, u0, hv_tri nu w hw J, hv_tri nu _ h1 J]
  split_ifs with hstd
  · have : ∀ s (c : Fin ((nu s).rowLen 0)) (i : Fin ((nu s).colLen c)),
        dg (fun _ : Lt => colsOf (1 : Matrix (Fin N) (Fin N) ℂ)) s i = 1 := by
      intro s c i
      have hi : (i : ℕ) < N := by
        have := (J s c i).2
        rw [hstd s c i] at this
        exact this
      simp [dg, hi, colsOf]
    simp [this]
  · simp
end PI.IsoInvMetricW
