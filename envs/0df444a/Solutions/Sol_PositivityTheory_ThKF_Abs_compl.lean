-- Prove2me | solution 1 for PositivityTheory.ThKF.Abs.compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:42.935398+00:00
-- url     : https://prove2.me/submissions/ee3628c1-381d-4179-874c-9da78d347c2f

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
theorem _root_.solution {St : Submodule ℂ U → Prop} (h : Proj St) (S : Submodule ℂ U) (hS : St S) (f : U) :
    ∃ a ∈ S, f - a ∈ Sᗮ := by
  obtain ⟨Z, Z', hZ, hf, e, hd⟩ := h f
  let A : Submodule ℂ U := S ⊓ Z
  haveI : FiniteDimensional ℂ A := Submodule.finiteDimensional_of_le (S₂ := Z) inf_le_right
  have ha := A.starProjection_apply_mem f
  refine ⟨_, ha.1, fun u hu => ?_⟩
  obtain ⟨y, hy, z, -, hyZ, hz, rfl⟩ := hd S hS u hu
  have h1 : f - A.starProjection f ∈ Z'ᗮ := e ▸ sub_mem hf ha.2
  rw [inner_add_left, A.sub_starProjection_mem_orthogonal f y ⟨hy, hyZ⟩, h1 z hz, add_zero]
end PositivityTheory.ThKF.Abs
