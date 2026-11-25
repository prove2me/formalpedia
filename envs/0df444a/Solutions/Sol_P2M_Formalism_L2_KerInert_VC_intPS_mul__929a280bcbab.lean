-- Prove2me | solution 1 for P2M_Formalism_L2_KerInert_VC_intPS_mul__929a280bcbab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:33.913347+00:00
-- url     : https://prove2.me/submissions/ce08663e-d4c6-40b5-80a8-9ca1bfb460ee

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
open Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] (R' : Subring K)
namespace Formalism.L2.KerInert.VC
theorem _root_.solution {f g : K⟦X⟧} (hf : IntPS R' f) (hg : IntPS R' g) : IntPS R' (f * g) := by
  intro n; rw [coeff_mul]; exact R'.sum_mem fun p _ => R'.mul_mem (hf _) (hg _)
end Formalism.L2.KerInert.VC
