-- Prove2me | solution 1 for P2M_Formalism_L2_KerInert_VC_intPS_subst__f54d4fdeff52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:36.081394+00:00
-- url     : https://prove2.me/submissions/7177cecc-6822-45ef-be4d-c0f623bb322d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_intMv_of_intPS
import Theorems.Thm_Formalism_L2_Th1_C_Pts_intPS_of_intMv


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
open Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] (R' : Subring K)
namespace Formalism.L2.KerInert.VC
theorem _root_.solution {f a : K⟦X⟧} (hf : IntPS R' f) (ha : IntPS R' a) (ha0 : constantCoeff a = 0) :
    IntPS R' (f.subst a) :=
  Pts.intPS_of_intMv (IntegralMvPolynomialLemmas.intMv_subst hf ⟨ha0, Pts.intMv_of_intPS ha⟩)
end Formalism.L2.KerInert.VC
