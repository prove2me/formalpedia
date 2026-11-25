-- Prove2me | solution 1 for PI.FJMA.disj_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:37.979903+00:00
-- url     : https://prove2.me/submissions/b4dd37a0-04d1-4a8f-8478-8600f2a24a17

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
variable (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)
namespace PI.FJMA
theorem _root_.solution {S : Set (Ln p q r s)} {m n : ℕ} (ι : Fin m × Fin n → Ln p q r s) (h : ∀ x, ι x ∉ S) :
    Disjoint (Set.range ι) S := by
  refine Set.disjoint_left.2 ?_
  rintro v ⟨x, rfl⟩ hv
  exact h x hv
end PI.FJMA
