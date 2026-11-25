-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ChainP.card3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:34.872059+00:00
-- url     : https://prove2.me/submissions/26d46a4f-5a30-4e6c-89db-80c036926ea5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChain

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
open PositivityTheory.Rg.Cz.ChainP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.ChainP
theorem _root_.solution {m : ℕ} (co : Fin (m + 1) → Fin n) (k : Fin n) :
    (Finset.univ.filter fun p : Fin (m + 1) => co p = k).card =
      (Finset.univ.filter fun p : Fin m => (co ∘ Fin.castSucc) p = k).card + if co (Fin.last m) = k then 1 else 0 := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  rfl
end PositivityTheory.Rg.Cz.ChainP
