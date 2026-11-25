-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.chain_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:40.619597+00:00
-- url     : https://prove2.me/submissions/c66fc280-bfb8-4a8f-85b5-bb21ba9063ff

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChain
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_base
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_step

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : TensorGl → JMComm → Curry → StepFormula → QdetFacts → StepChar → Height → WallQuot →
    Chain := by
  intro hT _ hC _ _ hS hH hW n M _ _ E hE l hl ℓ hℓ hWh top htop m
  induction m with
  | zero => intro co; exact ⟨1, ChainP.base E l hl ℓ hℓ top co⟩
  | succ m ih =>
    intro co
    exact ChainP.step hT hC hS hH hW E hE l ℓ hWh top htop m co (ih (co ∘ Fin.castSucc))
end PositivityTheory.Rg.Cz
