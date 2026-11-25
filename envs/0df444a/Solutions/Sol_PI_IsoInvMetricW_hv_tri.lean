-- Prove2me | solution 1 for PI.IsoInvMetricW.hv_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:51.404491+00:00
-- url     : https://prove2.me/submissions/3ed42f9c-86a3-4d1b-95fa-362e80f31185

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_HvScalar
import Theorems.Thm_PI_IsoInvMetricW_oe_ge
import Theorems.Thm_PI_IsoInvMetricW_det_tri

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
    (w : Lt → Fin N → ℕ → ℂ) (hw : ∀ s (a : Fin N) (j : ℕ), j < a → w s a j = 0)
    (J : ColChoice N nu) :
    hvC N nu w J = if (∀ s c i, (J s c i : ℕ) = i) then
      ∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), dg w s i else 0 := by
  have e : hvC N nu w J =
      ∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), w s (J s c i) i := by
    unfold hvC minY
    exact Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ =>
      det_tri (J s c) (w s) (hw s)
  rw [e]
  split_ifs with hstd
  · refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ =>
      Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) < N := by
      have := (J s c i).2
      rw [hstd s c i] at this
      exact this
    have : J s c i = ⟨i, hi⟩ := Fin.ext (hstd s c i)
    simp only [dg, hi, dite_true, this]
  · push_neg at hstd
    obtain ⟨s, c, i, hne⟩ := hstd
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply hw
    have := oe_ge (J s c) i
    omega
end PI.IsoInvMetricW
