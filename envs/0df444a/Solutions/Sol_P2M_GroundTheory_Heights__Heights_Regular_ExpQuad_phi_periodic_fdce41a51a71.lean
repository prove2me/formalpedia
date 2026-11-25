-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_phi_periodic_fdce41a51a71
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:32.728897+00:00
-- url     : https://prove2.me/submissions/c5c0f59e-f7e9-4bfa-b9ba-77d57c371cc9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_tau_shifted_periodic_411cd6442807

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
theorem _root_.solution (j : Fin a) (w : Fin n → ℂ) (hw : w ∈ logCover P.a_le) :
    phi P v (w + Pi.single (Fin.castLE P.a_le j) (2 * Real.pi * Complex.I)) = phi P v w := by
  simp only [phi, tau_shifted_periodic P j w hw]
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
