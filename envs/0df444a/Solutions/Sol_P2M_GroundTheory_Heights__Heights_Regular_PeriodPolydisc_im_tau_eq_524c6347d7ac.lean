-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_im_tau_eq_524c6347d7ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:59.247497+00:00
-- url     : https://prove2.me/submissions/64ec5ab0-712a-46a3-be4c-568c5131ca1b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PImTauBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
variable {n a g : ℕ} (P : PeriodPolydisc n a g)
namespace GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
theorem _root_.solution {T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hT0 : P.IsTau0Ext T0)
    {w : Fin n → ℂ} (hw : w ∈ logCover P.a_le) :
    (P.τ w).map Complex.im = (T0 (expCover a w)).map Complex.im +
      ∑ i : Fin a, (-(w (Fin.castLE P.a_le i)).re / (2 * Real.pi)) • P.realB i := by
  have hτ : P.τ w = T0 (expCover a w) + ∑ i : Fin a,
      (w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) • (P.B i).map (Int.cast : ℤ → ℂ) := by
    rw [← hT0.2 w hw, PeriodPolydisc.tau0, sub_add_cancel]
  ext p q
  rw [hτ]
  simp [Matrix.sum_apply, Complex.im_sum, Complex.mul_im, im_div_two_pi_I, realB]
end GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
