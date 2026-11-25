-- Prove2me | solution 1 for PI.VolStabW.FiniteThetaCoordinates.norm_emb_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:04:09.152001+00:00
-- url     : https://prove2.me/submissions/4fd56887-ca2b-4f8f-b88f-5971f5b305f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]
namespace PI.VolStabW.FiniteThetaCoordinates
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    ‖FinitePlace.embedding v x‖ ≤ 1 ↔ v.valuation F x ≤ 1 := by
  rw [FinitePlace.embedding_apply, Valued.toNormedField.norm_le_one_iff,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
end PI.VolStabW.FiniteThetaCoordinates
