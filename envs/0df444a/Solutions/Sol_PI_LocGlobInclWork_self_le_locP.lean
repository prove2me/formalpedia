-- Prove2me | solution 1 for PI.LocGlobInclWork.self_le_locP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:50:48.265536+00:00
-- url     : https://prove2.me/submissions/901b58df-7bec-47b9-8d00-952b40424fcf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul
import Theorems.Thm_PI_LocGlobInclWork_mem_localization_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.LocGlobInclWork
variable {K : Type} [Field K] [NumberField K]
namespace PI.LocGlobInclWork
theorem _root_.solution {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (p : Ideal (𝓞 K)) [p.IsPrime]
    (L : Submodule (𝓞 K) W) : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L :=
  fun x hx => (mem_localization_iff p L x).mpr ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact hx⟩
end PI.LocGlobInclWork
