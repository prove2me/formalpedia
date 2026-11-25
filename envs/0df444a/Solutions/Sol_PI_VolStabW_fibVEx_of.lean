-- Prove2me | solution 1 for PI.VolStabW.fibVEx_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:01:46.806702+00:00
-- url     : https://prove2.me/submissions/0c4dbe2c-7d75-440f-876f-bf9dc0ce001a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibOfTens
import Theorems.Thm_PI_VolStabW_fib_of_tens

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution (hG : FibOfDens) (hT : TensAll) (hD : DensV) : FibVEx := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  exact fib_of_tens hG ((hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v) μv νv hμ.1 hν.1
    (hD F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν)
end PI.VolStabW
