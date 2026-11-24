-- Prove2me | solution 1 for P2M_Formalism_L2_KerInert_VC_subst_C__f714b10ebe9d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:40:11.724805+00:00
-- url     : https://prove2.me/submissions/4a6c1fa2-2f37-4502-9d5b-f0b30debf733

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_C
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_apply
import Theorems.Thm_Formalism_L2_Th1_A_Plus_subHom_C
import Theorems.Thm_Formalism_L2_Th1_A_Plus_subHom_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.KerInert Formalism.L2.KerInert.VC
open Formalism.L2.Th1.A
variable {R : Type} [CommRing R]
namespace Formalism.L2.KerInert.VC
theorem _root_.solution {s : R⟦X⟧} (hs0 : constantCoeff s = 0) (a : R) : (PowerSeries.C a).subst s = PowerSeries.C a := by
  rw [← ISer.subHom_apply _ hs0, ISer.subHom_C]
end Formalism.L2.KerInert.VC
