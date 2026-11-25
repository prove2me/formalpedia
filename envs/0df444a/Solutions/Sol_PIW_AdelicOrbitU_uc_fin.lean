-- Prove2me | solution 1 for PIW.AdelicOrbitU.uc_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:58.554695+00:00
-- url     : https://prove2.me/submissions/1676fbe2-6c81-407a-a373-cd771fdf713e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_LocalSum
import Theorems.Thm_PIW_AdelicOrbitU_local_sum
import Theorems.Thm_PIW_AdelicOrbitU_uc_rp

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
open scoped RestrictedProduct
namespace PIW.AdelicOrbitU
theorem _root_.solution (F : Type) [Field F] [NumberField F] :
    UnitChoice (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) := by
  exact uc_rp (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
    v.adicCompletion F) (fun v => v.adicCompletionIntegers F) Filter.cofinite
    (fun v k a f h => local_sum a f h)
end PIW.AdelicOrbitU
