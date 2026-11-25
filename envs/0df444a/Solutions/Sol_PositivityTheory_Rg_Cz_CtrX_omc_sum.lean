-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.omc_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:30:59.293202+00:00
-- url     : https://prove2.me/submissions/82a75797-a83f-4da6-8374-32304e757261

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.CtrX
theorem _root_.solution {m : ℕ} {β : Type} [AddCommMonoid β] (j : Fin m) (h : (Fin m → Fin n) → β) :
    ∑ J, h J = ∑ b, ∑ R, h (omcGlue j b R) := by
  rw [← (omcEquiv (n := n) j).symm.sum_comp, Fintype.sum_prod_type]
  rfl
end PositivityTheory.Rg.Cz.CtrX
