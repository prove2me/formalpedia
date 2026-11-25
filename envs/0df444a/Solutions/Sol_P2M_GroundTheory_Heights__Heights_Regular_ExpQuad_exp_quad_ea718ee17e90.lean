-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_exp_quad_ea718ee17e90
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:28:33.865737+00:00
-- url     : https://prove2.me/submissions/3591229d-8223-477f-ad0c-e249973cd07f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_tau_3dfc944c5bc2

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
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.ExpQuad
variable {n a g : ℕ} (P : PeriodPolydisc n a g) (v : Fin g → ℤ)
namespace GroundTheory.Heights₂.Heights.Regular.ExpQuad
theorem _root_.solution (w : Fin n → ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * qf (P.τ w) v) =
      Complex.exp (phi P v w) *
        Complex.exp (∑ i, w (Fin.castLE P.a_le i) * ((intQuad (P.B i) v : ℤ) : ℂ)) := by
  rw [qf_tau, mul_add, Complex.exp_add, phi, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp [two_pi_I_ne_zero]
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
