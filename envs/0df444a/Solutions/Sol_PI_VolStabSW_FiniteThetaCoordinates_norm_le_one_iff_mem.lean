-- Prove2me | solution 1 for PI.VolStabSW.FiniteThetaCoordinates.norm_le_one_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:39.512902+00:00
-- url     : https://prove2.me/submissions/65d83bfb-caee-4391-8249-18475f44138e

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
variable (F : Type) [Field F] [NumberField F]
namespace PI.VolStabSW.FiniteThetaCoordinates
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) :
    ‖x‖ ≤ 1 ↔ x ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff
end PI.VolStabSW.FiniteThetaCoordinates
