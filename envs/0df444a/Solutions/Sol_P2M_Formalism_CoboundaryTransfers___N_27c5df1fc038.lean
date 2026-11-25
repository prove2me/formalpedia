-- Prove2me | solution 1 for P2M_Formalism_CoboundaryTransfers___N_27c5df1fc038
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:34.87379+00:00
-- url     : https://prove2.me/submissions/fa81a945-55c7-4715-b26c-f2d16497d4f5

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
namespace Formalism.CoboundaryTransfers
theorem _root_.solution (W : WachMod B M D) (δ : D →ₗ[O] D) (h2 : ∀ y, B.X • δ y = W.γ y - y) :
    ∀ n ∈ W.N, δ n ∈ W.N := by
  intro n hn
  obtain ⟨x', hx', hxx⟩ := W.γ_N n hn
  have h3 : δ n = x' := by
    have h := W.X_inj (δ n - x') (by rw [smul_sub, h2, hxx, sub_self])
    exact sub_eq_zero.mp h
  rw [h3]
  exact hx'
end Formalism.CoboundaryTransfers
