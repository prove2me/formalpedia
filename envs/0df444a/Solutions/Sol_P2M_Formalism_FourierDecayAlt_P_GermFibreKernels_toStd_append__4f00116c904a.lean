-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_GermFibreKernels_toStd_append__4f00116c904a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:34:07.705999+00:00
-- url     : https://prove2.me/submissions/658da801-3d3c-4466-adde-091ea7621ce2

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNegBetaL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ToStdAppend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermFibreKernels
open Formalism.FourierDecayAlt NumberField
noncomputable section
namespace Formalism.FourierDecayAlt.P.GermFibreKernels
theorem _root_.solution (r : ℕ) (g : ℝ) : ∀ (P Q : C.LPt) (b : ℕ),
    D.toStd r g b (P ++ Q) = D.toStd r g b P ++ D.toStd r g (b + D.ptSize P) Q
  | [], Q, b => by simp [D.toStd, D.ptSize]
  | (s, t) :: rest, Q, b => by
    have ih := solution r g rest Q (b + s)
    simp only [List.cons_append, D.toStd, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc]
end Formalism.FourierDecayAlt.P.GermFibreKernels
