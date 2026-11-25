-- Prove2me | solution 1 for PI.VolStabSW.FiniteThetaCoordinates.norm_emb_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:54:14.813141+00:00
-- url     : https://prove2.me/submissions/dbcc8246-ccc8-4f46-b13b-75d9bb4653c2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]
namespace PI.VolStabSW.FiniteThetaCoordinates
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    ‖FinitePlace.embedding v x‖ ≤ 1 ↔ v.valuation F x ≤ 1 := by
  rw [FinitePlace.embedding_apply, Valued.toNormedField.norm_le_one_iff,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
end PI.VolStabSW.FiniteThetaCoordinates
