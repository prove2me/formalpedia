-- Prove2me | solution 1 for P2M_Formalism_L2_KerInert_VC_intPS_sub__f29ebb1ea461
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:35.072982+00:00
-- url     : https://prove2.me/submissions/cb85d59c-0774-40c5-9e89-cfdb7849f579

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub


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
theorem _root_.solution {f g : K⟦X⟧} (hf : IntPS R' f) (hg : IntPS R' g) : IntPS R' (f - g) := by
  intro n; rw [map_sub]; exact R'.sub_mem (hf n) (hg n)
end Formalism.L2.KerInert.VC
