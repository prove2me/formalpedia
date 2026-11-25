-- Prove2me | solution 1 for P2M_Formalism_L2_KerInert_VC_derivative_C_mul__5469c3081b6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:27.884644+00:00
-- url     : https://prove2.me/submissions/7bf15a66-e472-4418-bd10-0b6305ea2cf1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange

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
variable {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)
namespace Formalism.L2.KerInert.VC
theorem _root_.solution (a : K) (f : K⟦X⟧) :
    derivative K (PowerSeries.C a * f) = PowerSeries.C a * derivative K f := by
  rw [Derivation.leibniz, derivative_C, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
end Formalism.L2.KerInert.VC
