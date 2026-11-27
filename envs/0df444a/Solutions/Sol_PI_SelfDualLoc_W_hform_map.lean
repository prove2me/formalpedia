-- Prove2me | solution 1 for PI.SelfDualLoc.W.hform_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:18:51.461836+00:00
-- url     : https://prove2.me/submissions/e5e78b40-1381-4ba4-b899-6d2da745f44f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  (σ : A →+* A) (J : Matrix n n A)
namespace PI.SelfDualLoc.W
theorem _root_.solution {B : Type} [CommRing B] (τ : B →+* B) (f : A →+* B)
    (hf : ∀ a, f (σ a) = τ (f a)) (x y : n → A) :
    hform τ (J.map f) (fun i => f (x i)) (fun i => f (y i)) = f (hform σ J x y) := by
  simp only [PI.SelfDualLoc.hform, map_sum, map_mul, hf, Matrix.map_apply]
end PI.SelfDualLoc.W
