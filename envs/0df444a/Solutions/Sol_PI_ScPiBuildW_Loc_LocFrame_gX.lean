-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.gX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:19.981935+00:00
-- url     : https://prove2.me/submissions/55b4fbd0-cec4-4fa5-8468-4f1e4513f772

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_e_mem
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_spanLt_le

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
omit hg
namespace PI.ScPiBuildW.Loc.LocFrame
theorem _root_.solution {x : Fin n → ℂ} (hx : x ∈ L.X) : g *ᵥ x ∈ L.X := by
  have key : ∀ a : Fin r, g *ᵥ L.e a ∈ L.X := fun a => by
    have h1 : g *ᵥ L.e a = L.e a + (g - 1) *ᵥ L.e a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [h1]
    exact L.X.add_mem (L.e_mem a) (L.spanLt_le a.1 a.isLt.le (hS.1 a))
  have hx' : x ∈ Submodule.span ℂ (L.e '' {b | b.1 < r}) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, _, rfl⟩ := hv
    exact key a
  | zero =>
    rw [Matrix.mulVec_zero]
    exact L.X.zero_mem
  | add u v _ _ hu hv =>
    rw [Matrix.mulVec_add]
    exact L.X.add_mem hu hv
  | smul c u _ hu =>
    rw [Matrix.mulVec_smul]
    exact L.X.smul_mem c hu
end PI.ScPiBuildW.Loc.LocFrame
