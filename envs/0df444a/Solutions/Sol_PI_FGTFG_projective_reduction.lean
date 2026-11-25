-- Prove2me | solution 1 for PI.FGTFG.projective_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:34.905799+00:00
-- url     : https://prove2.me/submissions/de334031-0cdf-47e4-b5b1-d495e9fa58af

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_RankOneStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_ProjectiveReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FGTFG
namespace PI.FGTFG
theorem _root_.solution : ProjStep := by
  intro R M _ _ _ _ _ _
  have htor : Submodule.torsion R M = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    rw [Submonoid.smul_def, smul_eq_zero] at ha
    exact (Submodule.mem_bot R).mpr (ha.resolve_left (nonZeroDivisors.coe_ne_zero a))
  haveI : Module.Flat R M := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htor
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact Module.Flat.projective_of_finitePresentation
end PI.FGTFG
