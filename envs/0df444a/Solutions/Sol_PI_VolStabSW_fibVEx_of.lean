-- Prove2me | solution 1 for PI.VolStabSW.fibVEx_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:55.938831+00:00
-- url     : https://prove2.me/submissions/86e0e87a-897e-4c42-a7fe-b7ec64ad4582

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibOfTens
import Theorems.Thm_PI_VolStabSW_fib_of_tens

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (hG : FibOfDens) (hT : TensAll) (hD : DensV) : FibVEx := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  exact fib_of_tens hG ((hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v) μv νv hμ.1 hν.1
    (hD F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν)
end PI.VolStabSW
