-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Mx7_modY1__87e636a5f50a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:32.860801+00:00
-- url     : https://prove2.me/submissions/5cf0b93c-9d7d-4d18-a7f4-1a540dfea4b1

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_lowering_intertwine_gamma
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absLG3
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_mA_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_raising_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_sc_Um
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_upper_shift_commute_coordinate
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kappa_commute_raising_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kappa_commute_raising_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLNs : LevNabs) (P : Par) (Y : ℂ)
    (h0 : ∀ π, xC P π Y ≠ 0) (h1 : ∀ π, xC P π (Y + 1) ≠ 0) :
    mA P (Y + 1) * t22 P Y = t22 P Y * mA P Y := by
  obtain ⟨_, _, _, _, _, _, hGGi, hGiG, _⟩ := hLF P
  obtain ⟨_, _, _, _, nG, _, _⟩ := hLNs P
  have cGz : Commute (ggA P) (zA P) := fn_comm P _ _ _ _
  have cGGi : Commute (ggA P) (ggiA P) := fn_comm P _ _ _ _
  have hGb : ggA P * (zA P * ggiA P) = zA P := by rw [← mul_assoc, cGz.eq, mul_assoc, hGGi, mul_one]
  have hbG : (zA P * ggiA P) * ggA P = ggA P * (zA P * ggiA P) := (cGz.mul_right cGGi).eq.symm
  have hLG : m0A P (Y + 1) * ggA P = ggA P * m0A P Y := by
    rw [raising_constant_eq_shift, raising_constant_eq_shift]
    exact absLG3 _ _ _ _ nG hbG hGb _ _ (by ring)
  rw [mA_eq, mA_eq, t22]
  exact lowering_intertwine_gamma _ _ _ _ _ _ _ hLG (kappa_commute_raising_constant P _ _) (upper_shift_commute_coordinate hSh hR P Y h0 h1) (sc_Um hSc P _ _)
    (kap_comm_sc P _ _).symm cGGi
end Formalism.FourierDecayAlt.P.Mx7
