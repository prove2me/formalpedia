-- Prove2me | solution 1 for PI.VolStabSW.continuous_sizeTup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:56.431251+00:00
-- url     : https://prove2.me/submissions/39b34736-f8bc-4459-8f89-4b526823c9b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SWeqOm
import Theorems.Thm_PI_VolStabSW_continuous_sizeInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace PI.VolStabSW
theorem _root_.solution {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeTup (M := M) (n := n) b) := by
  unfold sizeTup
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => ?_
  exact (continuous_sizeInf b).comp ((continuous_apply i).comp (continuous_apply a))
end PI.VolStabSW
