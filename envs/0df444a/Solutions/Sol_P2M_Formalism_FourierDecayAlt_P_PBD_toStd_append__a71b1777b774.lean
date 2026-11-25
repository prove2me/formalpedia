-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_PBD_toStd_append__a71b1777b774
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:46:28.63585+00:00
-- url     : https://prove2.me/submissions/9e8f8b5e-57c5-4a32-90d0-ec34068e47be

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
theorem _root_.solution (r : ℕ) (g : ℝ) (c : ℂ) : ∀ (h : C.LPt) (b : ℕ),
    D.toStd r g b (h ++ [(1, c)]) = D.toStd r g b h ++
      [(1, (((g / (2 * Real.pi)) ^ S6.nuBlock r ((b + D.ptSize h : ℕ) : ℤ) ((1 : ℕ) : ℤ) : ℝ) : ℂ) * c)]
  | [], b => by simp [D.toStd, D.ptSize]
  | (s, t) :: rest, b => by
    have ih := solution r g c rest (b + s)
    simp only [List.cons_append, D.toStd, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc]
end Formalism.FourierDecayAlt.P.PBD
