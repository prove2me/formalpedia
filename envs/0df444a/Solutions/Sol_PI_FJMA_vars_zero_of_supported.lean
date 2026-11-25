-- Prove2me | solution 1 for PI.FJMA.vars_zero_of_supported
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:31.003073+00:00
-- url     : https://prove2.me/submissions/59fa7757-5633-48a2-8e5c-6a68b43c0426

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMA
open PI.FJM
variable {σ : Type}
namespace PI.FJMA
theorem _root_.solution {S : Set σ} {F : MvPolynomial σ ℂ} (hF : F ∈ supported ℂ S) :
    ∀ x ∈ F.support, ∀ v ∉ S, x v = 0 := by
  intro x hx v hv
  by_contra h
  exact hv ((mem_supported.1 hF) ((mem_vars_iff_mem_support v).2 ⟨x, hx, Finsupp.mem_support_iff.2 h⟩))
end PI.FJMA
