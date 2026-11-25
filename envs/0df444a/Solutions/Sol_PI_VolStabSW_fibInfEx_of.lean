-- Prove2me | solution 1 for PI.VolStabSW.fibInfEx_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:51.724711+00:00
-- url     : https://prove2.me/submissions/92204680-6468-4885-8afc-33a171909df8

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
theorem _root_.solution (hG : FibOfDens) (hT : TensAll) (hD : DensInf) : FibInfEx := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ μinf hμ νinf hν
  exact fib_of_tens hG (hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).1 μinf νinf hμ.1 hν.1
    (hD F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ μinf hμ νinf hν)
end PI.VolStabSW
