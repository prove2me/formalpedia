-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.g_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:52:16.670411+00:00
-- url     : https://prove2.me/submissions/38d94b26-bf4c-4c60-9769-aaa034219c19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_gX
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_g_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.ScPiBuildW PI.ScPiBuildW.Loc
open PI.ScPiExists
open PI.ScPiBuildW.Loc.LocFrame
variable {n r k : ℕ} {ε : Fin n → Bool} (L : LocFrame n r k ε)
variable {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g)
include hg hS
namespace PI.ScPiBuildW.Loc.LocFrame
theorem _root_.solution {x : Fin n → ℂ} (hx : x ∈ L.X) : ∃ x' ∈ L.X, g *ᵥ x' = x := by
  let f : L.X →ₗ[ℂ] L.X := (Matrix.mulVecLin g).restrict (fun v hv => L.gX hS hv)
  have hinj : Function.Injective f := by
    intro u v huv
    have h1 : g *ᵥ ((u : Fin n → ℂ) - v) = 0 := by
      rw [Matrix.mulVec_sub, sub_eq_zero]
      exact congrArg Subtype.val huv
    exact Subtype.ext (sub_eq_zero.mp (g_inj hg h1))
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨x, hx⟩
  exact ⟨v, v.2, congrArg Subtype.val hv⟩
end PI.ScPiBuildW.Loc.LocFrame
