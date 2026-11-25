-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_PBD_bSt_pos__d344a790c9c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:51.065135+00:00
-- url     : https://prove2.me/submissions/e03e2687-c4e9-434a-894f-d3960f57578f

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution (κ : ℝ) (hκ : 0 < κ) (p : C.LPt) : 0 < D.bSt κ p := by
  unfold D.bSt
  refine List.prod_pos fun x hx => ?_
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
  exact Finset.prod_pos fun m _ => zpow_pos (div_pos (zpow_pos hκ _) Real.pi_pos) _
end Formalism.FourierDecayAlt.P.PBD
