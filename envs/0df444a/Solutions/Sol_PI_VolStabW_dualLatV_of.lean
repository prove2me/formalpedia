-- Prove2me | solution 1 for PI.VolStabW.dualLatV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:31.426272+00:00
-- url     : https://prove2.me/submissions/64413603-54ac-4399-968d-ebea53216ce4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
import Theorems.Thm_PI_VolStabW_SdDualW_dualAt_alt
import Theorems.Thm_PI_VolStabW_SdDualW_nondeg_BR
import Theorems.Thm_PI_VolStabW_sigma_invol


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
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW
namespace PI.VolStabW
theorem _root_.solution (hH : DualHV) : DualLatV := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  refine ⟨?_, hH F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v⟩
  exact SdDualW.dualAt_alt v (Module.finBasis F E) σ J
    (fun Y hY => SdDualW.nondeg_BR v σ hσ J hJ.2 Y hY)
end PI.VolStabW
