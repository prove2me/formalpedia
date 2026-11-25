-- Prove2me | solution 1 for PI.VolStabSW.nuInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:36.75227+00:00
-- url     : https://prove2.me/submissions/1c80dc23-e83f-462a-bb02-b1d6b45c58bf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoNuFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_NuInvSt
import Theorems.Thm_PI_VolStabSW_continuous_smul_tup

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
open scoped TensorProduct ENNReal
namespace PI.VolStabSW
theorem _root_.solution (hU : OmUniq) (hI : OmInv) : NuInv := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν g s hs
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hm : Measurable (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) :=
    (continuous_smul_tup σ J g).measurable
  rw [← Measure.map_apply hm hs,
    hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ _ _
      (hI F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν g) hν]
end PI.VolStabSW
