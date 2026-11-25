-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.Coch.sum_sum_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:30:49.994968+00:00
-- url     : https://prove2.me/submissions/b39816a7-564a-4f4c-974f-1c583bc794ea

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CochainExpansions_SumSumProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.Coch
variable {H V : Type*} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.Rg.Cz.Coch
theorem _root_.solution {N : ℕ} {α β R : Type*} [Fintype α] [Fintype β] [CommSemiring R] (g : Fin N → α → β → R) :
    ∑ A : Fin N → α, ∑ B : Fin N → β, ∏ k, g k (A k) (B k) = ∏ k, ∑ a, ∑ b, g k a b := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Fintype.prod_sum]
end PositivityTheory.Rg.Cz.Coch
