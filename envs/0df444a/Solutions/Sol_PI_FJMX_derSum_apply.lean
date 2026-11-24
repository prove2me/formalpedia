-- Prove2me | solution 1 for PI.FJMX.derSum_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:45.811087+00:00
-- url     : https://prove2.me/submissions/5b40afca-f9ca-4494-a07b-fe8bc4976091

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {σ : Type*} {m n : ℕ}
namespace PI.FJMX
theorem _root_.solution {ι : Type*} (t : Finset ι) (D : ι → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (f : MvPolynomial σ ℂ) : (∑ c ∈ t, D c) f = ∑ c ∈ t, D c f := by
  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl
end PI.FJMX
