-- Prove2me | solution 1 for PositivityTheory.CW.SecondMomentAlgebra.zsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:52.160123+00:00
-- url     : https://prove2.me/submissions/82099a46-ab72-49e2-b1fa-3fcd43f552f9

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MatrixActionSingle

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
open PositivityTheory.CW.SecondMomentAlgebra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.SecondMomentAlgebra
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (hZc : ∀ a b, ε a = ε b → Z ε E a b = 0) (w : V) :
    ∑ c, ∑ d, ‖Z ε E c d w‖ ^ 2 = ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 w‖ ^ 2 := by
  rw [← Fintype.sum_prod_type' (fun c d => ‖Z ε E c d w‖ ^ 2), nc, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs with h
  · rfl
  · simp [hZc _ _ (not_not.mp h)]
end PositivityTheory.CW.SecondMomentAlgebra
