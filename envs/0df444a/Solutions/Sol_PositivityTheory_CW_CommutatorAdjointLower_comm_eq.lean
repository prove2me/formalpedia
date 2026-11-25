-- Prove2me | solution 1 for PositivityTheory.CW.CommutatorAdjointLower.comm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:22:23.023196+00:00
-- url     : https://prove2.me/submissions/ea1dbd06-5c7f-48d6-83d9-d3ec5fc3f6ca

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_IdentityFiltrationBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.CommutatorAdjointLower
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.CW.CommutatorAdjointLower
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    (Mm E * Md ε E - Md ε E * Mm E) a b = ∑ c, (adjSign ε c b - adjSign ε a c) • (E a c * E c b) := by
  simp only [Mm, Md, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, mul_smul_comm, smul_mul_assoc,
    sub_smul, Finset.sum_sub_distrib]
end PositivityTheory.CW.CommutatorAdjointLower
