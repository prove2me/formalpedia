-- Prove2me | solution 1 for P2M_PI_VolStabW_SdTestInfW_BR_add_right__4f8a28ccbc2c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:15.355355+00:00
-- url     : https://prove2.me/submissions/8531975c-c221-47ba-bf35-caca2ab157bf

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
theorem _root_.solution (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y Y' : Fin n → Fin M → R ⊗[F] E) : BR R σ J X (Y + Y') = BR R σ J X Y + BR R σ J X Y' := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
end PI.VolStabW.SdTestInfW
