-- Prove2me | solution 1 for PositivityTheory.ThKF.Abs.fd_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:44.990468+00:00
-- url     : https://prove2.me/submissions/001f53fc-6b12-4be7-bc5a-406aadae91d7

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.Abs
open scoped InnerProductSpace
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
namespace PositivityTheory.ThKF.Abs
theorem _root_.solution {K : Type} [Group K] (κ : K →* Module.End ℂ U) (W : Submodule ℂ U) [FiniteDimensional ℂ W]
    [FiniteDimensional ℂ (homs κ W)] : FiniteDimensional ℂ ↥(ck (homs κ W))ᗮ := by
  let ev : ↥(ck (homs κ W))ᗮ →ₗ[ℂ] (homs κ W →ₗ[ℂ] W) :=
    { toFun := fun z => { toFun := fun L => ⟨L.1 z, L.2.1 z⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      map_add' := fun a b => LinearMap.ext fun L => Subtype.ext (map_add L.1 a.1 b.1)
      map_smul' := fun c a => LinearMap.ext fun L => Subtype.ext (map_smul L.1 c a.1) }
  refine Module.Finite.of_injective ev ((injective_iff_map_eq_zero ev).2 fun z hz => ?_)
  have h1 : z.1 ∈ ck (homs κ W) := fun L hL => congrArg Subtype.val (LinearMap.congr_fun hz ⟨L, hL⟩)
  exact Subtype.ext (inner_self_eq_zero.1 (z.2 _ h1))
end PositivityTheory.ThKF.Abs
