-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Cz_CGlue_pm_apply__c94cc9d97d61
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:48:09.035984+00:00
-- url     : https://prove2.me/submissions/f4606bc7-beb8-4340-b7fc-ec4cc120c269

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CoefficientGluing_SumFinVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Formalism.REAL
open scoped TensorProduct
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CGlue
variable {n : ℕ} {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.CGlue
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (σ : Equiv.Perm P) (f : TV n M P) (I : P → Fin n) :
    pm σ f I = f (I ∘ σ) := rfl
end PositivityTheory.Rg.Cz.CGlue
