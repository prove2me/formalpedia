-- Prove2me | solution 1 for PI.FJMA.shapeProd_supported
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:09.953204+00:00
-- url     : https://prove2.me/submissions/3e2c4670-6cb3-463a-87b0-d554c0d6a773

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported
import Theorems.Thm_PI_FJMD_shapeProd_mem


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
theorem _root_.solution {m n : ℕ} (ι : Fin m × Fin n → σ) (α : List ℕ) :
    shapeProd (Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)) α ∈ supported ℂ (Set.range ι) :=
  PI.FJMD.shapeProd_mem _ _ _ (fun i k _ _ => by
    simp only [Matrix.of_apply]
    exact X_mem_supported.2 ⟨(i, k), rfl⟩)
end PI.FJMA
