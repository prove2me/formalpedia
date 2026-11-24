-- Prove2me | solution 1 for PI.ScRefExists.LG.Phi_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:50.830851+00:00
-- url     : https://prove2.me/submissions/6b1e7e85-d8fc-410f-9045-0e925c957cd7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocGlob
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open PI PI.ScRefExists PI.ScRefExists.LG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.ScRefExists.LG
theorem _root_.solution (a x : E) (c : Af F) :
    Phi a (x ⊗ₜ[F] c) = algebraMap F (Af F) (Algebra.trace F E (a * x)) * c := by
  simp [Phi, lam, Algebra.smul_def]
end PI.ScRefExists.LG
