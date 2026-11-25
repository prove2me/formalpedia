-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CGlue.actT_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:14.075882+00:00
-- url     : https://prove2.me/submissions/14ebd956-ef86-4959-ba29-5bf27de4115e

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
variable {M : Type} [AddCommGroup M] [Module ℂ M] {d : ℕ}
namespace PositivityTheory.Rg.Cz.CGlue
theorem _root_.solution {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (γ : Γ) (f : TV n M P) (I : P → Fin n) :
    actT lab κ ρ γ f I = ∑ J : P → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) • ρ γ (f J) := by
  simp [actT]
end PositivityTheory.Rg.Cz.CGlue
