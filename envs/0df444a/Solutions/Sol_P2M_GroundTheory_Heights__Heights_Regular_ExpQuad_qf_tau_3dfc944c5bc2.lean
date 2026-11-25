-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_tau_3dfc944c5bc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:02.566523+00:00
-- url     : https://prove2.me/submissions/87886874-38bd-4c74-aa3f-7e8a590774c4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_add_1afce1407430
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_smul_641471b9b616
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_sum_4e58130a36e0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_intCast_76da25faf6e4

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
    qf (P.τ w) v = qf (P.tau0 w) v +
      ∑ i, w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I) * ((intQuad (P.B i) v : ℤ) : ℂ) := by
  have h : P.τ w = P.tau0 w + ∑ i : Fin a, (w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) •
      (P.B i).map (Int.cast : ℤ → ℂ) := by
    simp [PeriodPolydisc.tau0]
  rw [h, qf_add, qf_sum]
  simp [qf_smul, qf_intCast]
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
