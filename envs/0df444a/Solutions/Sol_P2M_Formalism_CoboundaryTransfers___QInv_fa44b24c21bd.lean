-- Prove2me | solution 1 for P2M_Formalism_CoboundaryTransfers___QInv_fa44b24c21bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:30:48.40087+00:00
-- url     : https://prove2.me/submissions/b69f0d82-5709-4e80-9f84-dc3c3b0d615c

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
    ∀ y, W.QInv y → W.QInv (δ y) := by
  intro y hy
  obtain ⟨y', hy', hyy⟩ := W.γ_QN y hy
  have h3 : δ y = y' := by
    have h := W.X_inj (δ y - y') (by rw [smul_sub, h2, hyy, sub_self])
    exact sub_eq_zero.mp h
  show B.Q ^ M • δ y ∈ W.N
  rw [h3]
  exact hy'
end Formalism.CoboundaryTransfers
