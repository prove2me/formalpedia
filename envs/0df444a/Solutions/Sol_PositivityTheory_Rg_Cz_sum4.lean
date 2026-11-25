-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.sum4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:54.767689+00:00
-- url     : https://prove2.me/submissions/38841185-a829-4c92-ae8a-8cc88ce3a118

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_ReSwapSumLe
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_Expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution {α β : Type} (s : Finset α) (t : Finset β) (F : Fin n → Fin n → α → β → ℂ) :
    ∑ a, ∑ c, ∑ p ∈ s, ∑ q ∈ t, F a c p q = ∑ p ∈ s, ∑ q ∈ t, ∑ a, ∑ c, F a c p q := by
  calc _ = ∑ a, ∑ p ∈ s, ∑ c, ∑ q ∈ t, F a c p q := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ p ∈ s, ∑ a, ∑ c, ∑ q ∈ t, F a c p q := Finset.sum_comm
    _ = ∑ p ∈ s, ∑ a, ∑ q ∈ t, ∑ c, F a c p q := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
end PositivityTheory.Rg.Cz
