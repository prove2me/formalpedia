-- Prove2me | solution 1 for P2M_PI_VolStabW_SdTestInfW_pairHerm_add_right__b5dc66635d8a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:25.924438+00:00
-- url     : https://prove2.me/submissions/6a8d67b3-009c-4fdb-93b5-d294813e51bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RealCharacter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdTestInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.SdTestInfW
open MeasureTheory Complex Filter Topology
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation PI.VolFromSW SdUniqW
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
namespace PI.VolStabW.SdTestInfW
theorem _root_.solution (σ : E →ₐ[F] E) (n : ℕ) (S T U : HermR R σ n) :
    pairHerm R σ n S (T + U) = pairHerm R σ n S T + pairHerm R σ n S U := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, mul_add, Finset.sum_add_distrib,
    map_add]
end PI.VolStabW.SdTestInfW
