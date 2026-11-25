-- Prove2me | solution 1 for P2M_Formalism_H_inner__isSymm_d7d5f164fe07
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:56.44319+00:00
-- url     : https://prove2.me/submissions/08cf72c2-8509-4a57-a810-225ca2d832e3

import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_DualLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.H
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace Formalism.H
theorem _root_.solution : LinearMap.BilinForm.IsSymm (innerₗ V) := by
  first
    | exact fun x y => by
        simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _
    | exact ⟨fun x y => by
        simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _⟩
    | (intro x y; simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _)
    | (constructor; intro x y; simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _)
end Formalism.H
