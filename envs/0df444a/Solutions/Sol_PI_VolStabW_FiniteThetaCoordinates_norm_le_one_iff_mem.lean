-- Prove2me | solution 1 for PI.VolStabW.FiniteThetaCoordinates.norm_le_one_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:30.215909+00:00
-- url     : https://prove2.me/submissions/bd263bee-0922-4101-9e85-4f6cfc21f5ca

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
variable (F : Type) [Field F] [NumberField F]
namespace PI.VolStabW.FiniteThetaCoordinates
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) :
    ‖x‖ ≤ 1 ↔ x ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff
end PI.VolStabW.FiniteThetaCoordinates
