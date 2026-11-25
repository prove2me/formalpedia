-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_PBD_rd_pos__cb5bba46fb5e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:04.115314+00:00
-- url     : https://prove2.me/submissions/5ec17dd5-e238-4b37-90fe-9d0f1e100086

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] : 0 < S6.rd E := by
  unfold S6.rd
  refine Real.rpow_pos_of_pos ?_ _
  exact_mod_cast abs_pos.2 (discr_ne_zero E)
end Formalism.FourierDecayAlt.P.PBD
