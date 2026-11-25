-- Prove2me | solution 1 for PositivityTheory.CW.commutator_adjoint_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:35:25.278241+00:00
-- url     : https://prove2.me/submissions/46a90a05-9b97-4f36-b911-ac3a0cae0dc7

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_IdentityFiltrationBound
import Theorems.Thm_PositivityTheory_CW_CommutatorAdjointLower_comm_eq
import Theorems.Thm_PositivityTheory_CW_CommutatorAdjointLower_Z_eq

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
namespace PositivityTheory.CW
theorem _root_.solution : A1 → CommutatorAdjointModLower := by
  intro hA n ε V _ _ E h a b
  obtain ⟨-, -, hE1, -, hcomm, -, -⟩ := hA n ε V E h
  rw [CommutatorAdjointLower.comm_eq, CommutatorAdjointLower.Z_eq ε h.gl, ← Finset.sum_add_distrib]
  have key : ∀ c, (adjSign ε c b - adjSign ε a c) • (E a c * E c b) +
      ((if ε c = ε a then E a c * E c b + E c b * E a c else 0) -
        (if ε c = ε b then E a c * E c b + E c b * E a c else 0)) =
      ((if ε c = ε a then (1 : ℂ) else 0) - (if ε c = ε b then 1 else 0)) • (E c b * E a c - E a c * E c b) := by
    intro c
    simp only [adjSign, @eq_comm _ (ε a) (ε c)]
    split_ifs <;> module
  rw [Finset.sum_congr rfl fun c _ => key c]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hcomm 1 1 _ (hE1 c b) _ (hE1 a c))
end PositivityTheory.CW
