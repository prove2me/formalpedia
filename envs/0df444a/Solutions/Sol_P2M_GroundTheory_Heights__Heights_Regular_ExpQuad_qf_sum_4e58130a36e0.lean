-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_sum_4e58130a36e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:37.635236+00:00
-- url     : https://prove2.me/submissions/63e671ba-75db-4978-b3d6-5537ee0df6b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_qf_add_1afce1407430

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
namespace GroundTheory.Heights₂.Heights.Regular.ExpQuad
theorem _root_.solution {g : ℕ} {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) :
    qf (∑ i ∈ s, A i) v = ∑ i ∈ s, qf (A i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qf]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, qf_add, ih]
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
