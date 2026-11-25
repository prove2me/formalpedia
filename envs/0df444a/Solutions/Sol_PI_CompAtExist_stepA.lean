-- Prove2me | solution 1 for PI.CompAtExist.stepA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:30.010493+00:00
-- url     : https://prove2.me/submissions/25351459-92e7-49fb-9d39-582f030e5e3e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionExistence_LeOneIffOfMulEqOne
import Theorems.Thm_PI_CompAtExist_muV_apply
import Theorems.Thm_PI_CompAtExist_muV_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CompAtExist
open NumberField IsDedekindDomain ReciprocityTheory.Aut
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
namespace PI.CompAtExist
theorem _root_.solution : StepA L := by
  intro s k
  rw [← muV_apply, muV_eq]
  exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' s.w k).symm
end PI.CompAtExist
