-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.M_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:56.090643+00:00
-- url     : https://prove2.me/submissions/e629c59c-3342-4a97-8f21-3873c9aafa9e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_add_right
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_we
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_hJ_X_right

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
namespace PI.ScPiBuildW.Loc.LocFrame
theorem _root_.solution {g : Matrix (Fin n) (Fin n) ℂ} (hN : InN ε L.e L.z g) : L.M g = 1 := by
  ext c b
  have hx := hN.2 (L.w b) (fun a => L.ew a b)
  have h1 : g *ᵥ L.w b = L.w b + (g - 1) *ᵥ L.w b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  show hJ ε (L.w c) (g *ᵥ L.w b) = (1 : Matrix (Fin k) (Fin k) ℂ) c b
  rw [h1, hJ_add_right, L.ww, L.hJ_X_right hx (fun a => L.we c a), add_zero, Matrix.one_apply]
end PI.ScPiBuildW.Loc.LocFrame
