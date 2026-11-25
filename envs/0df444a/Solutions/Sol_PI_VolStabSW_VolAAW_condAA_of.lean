-- Prove2me | solution 1 for PI.VolStabSW.VolAAW.condAA_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:18:03.371979+00:00
-- url     : https://prove2.me/submissions/8dea90d7-4670-45ce-920f-14535df4b774

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolT
import Theorems.Thm_PI_VolStabSW_VolAAW_ev_triv

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
open PI.VolStabSW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
variable {F : Type} [Field F] [NumberField F]
namespace PI.VolStabSW.VolAAW
theorem _root_.solution (hE : CondExact) : CondAA := by
  intro F _ _ ψ hψ
  filter_upwards [hE F ψ hψ, ev_triv ψ hψ] with v h1 h2
  intro t
  refine ⟨h1 t, fun ht s hs => h2 _ (mul_mem hs ht)⟩
end PI.VolStabSW.VolAAW
