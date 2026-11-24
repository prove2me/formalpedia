-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_PBD_toStd_size__257163185415
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:35:04.484961+00:00
-- url     : https://prove2.me/submissions/5f4bf78a-099b-453c-9892-1de7f8f55baf

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
theorem _root_.solution (r : ℕ) (g : ℝ) : ∀ (p : C.LPt) (b : ℕ), D.ptSize (D.toStd r g b p) = D.ptSize p
  | [], _ => rfl
  | (s, t) :: rest, b => by
    have ih := solution r g rest (b + s)
    simp only [D.ptSize, D.toStd, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
end Formalism.FourierDecayAlt.P.PBD
