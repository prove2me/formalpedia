-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ChainP.xJ_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:06.374221+00:00
-- url     : https://prove2.me/submissions/ca5b1742-0721-4b35-ae5f-dc54665d0273

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChain
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.ChainP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.ChainP
theorem _root_.solution (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (m : ℕ) (j : Fin m)
    (a b : Fin n) : Commute (xJ E j) (tE (Finset.univ : Finset (Fin m)) E a b) := by
  obtain ⟨-, h2, h3, -⟩ := hT n M (Fin m) E hE Finset.univ
  unfold xJ
  exact (h2 j (Finset.mem_univ _) a b).add_left
    (Commute.sum_left _ _ _ fun i _ => h3 _ (fun p => by simp) a b)
end PositivityTheory.Rg.Cz.ChainP
