-- Prove2me | solution 1 for PIW.AdelicOrbitU.norm_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:26.586172+00:00
-- url     : https://prove2.me/submissions/5aeab462-6ddf-4b26-abfb-cf14029c6d55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
namespace PIW.AdelicOrbitU
theorem _root_.solution {S : Type} [CommRing S] (B p q a b D Θ : S) (h : Θ ^ 2 = D) :
    (B - (p - q * Θ) * (a + b * Θ)) * (B - (p + q * Θ) * (a - b * Θ)) =
      (B - p * a + q * b * D) ^ 2 - D * (q * a - p * b) ^ 2 := by
  linear_combination (2 * B * q * b - p ^ 2 * b ^ 2 - q ^ 2 * a ^ 2 + q ^ 2 * b ^ 2 * (Θ ^ 2 + D)) * h
end PIW.AdelicOrbitU
