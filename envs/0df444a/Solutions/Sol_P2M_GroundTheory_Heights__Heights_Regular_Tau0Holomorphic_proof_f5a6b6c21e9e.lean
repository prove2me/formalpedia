-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_Tau0Holomorphic_proof_f5a6b6c21e9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:39:03.311477+00:00
-- url     : https://prove2.me/submissions/8f8427f0-4a4d-4895-a822-f1e8d2e53df0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_posSemidef_of_intQuad_nonneg_ee0928ce48ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_tau_shifted_transpose_3683cff9c7b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_exists_quad_ext_4e755da53d8a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_polarise_1454c871b39d

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
open Metric Matrix Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace Tau0Holomorphic
theorem _root_.solution (h0 : ExpQuadMonomial.Statement) : Tau0Holomorphic.Statement := by
  intro n a g P
  refine ⟨fun i => posSemidef_of_intQuad_nonneg (P.B i) (P.B_symm i) fun v => (h0 n a g P v).1 i,
    ?_⟩
  choose Q hQa hQe using P.exists_quad_ext h0
  refine ⟨fun z p q => (Q (Pi.single p 1 + Pi.single q 1) z - Q (Pi.single p 1) z -
      Q (Pi.single q 1) z) / 2, fun p q => ?_, fun w hw => ?_⟩
  · exact (((hQa _).sub (hQa _)).sub (hQa _)).div analyticOnNhd_const fun _ _ => two_ne_zero
  · ext p q
    simp only [hQe _ w hw]
    exact (polarise _ (P.tau_shifted_transpose hw) p q).symm
end Tau0Holomorphic
end GroundTheory.Heights₂.Heights.Regular
