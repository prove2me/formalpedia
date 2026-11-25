-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.KTy.alt_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:46:24.838271+00:00
-- url     : https://prove2.me/submissions/66ae33a7-b04d-4f5d-9b12-b0da84689e18

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA

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
open PositivityTheory.Rg.Cz.KTy
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace PositivityTheory.Rg.Cz.KTy
theorem _root_.solution {P : Type} [Fintype P] [DecidableEq P] {M : Type} [AddCommGroup M] [Module ℂ M]
    (G : Finset (Equiv.Perm P)) (x : Module.End ℂ (TV n M P)) (h : ∀ σ ∈ G, Commute (pm σ) x) :
    Commute (alt G) x := by
  unfold alt
  exact Commute.sum_left _ _ _ fun σ hσ => (h σ hσ).smul_left _
end PositivityTheory.Rg.Cz.KTy
