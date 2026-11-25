-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.gw_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:00.113874+00:00
-- url     : https://prove2.me/submissions/d2cfd75f-179d-4fb1-ab8f-8b3cc2e1e9ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_decomp
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_g_perp
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_local_frame_preserves_orthogonal

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
theorem _root_.solution {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g) (b : Fin k) :
    g *ᵥ L.w b = ∑ c, L.M g c b • L.w c + ∑ a, hJ ε (L.f a) (g *ᵥ L.w b) • L.e a :=
  L.decomp _ (L.g_perp hg hS fun a => L.ew a b) (L.local_frame_preserves_orthogonal hg hS (fun a => L.ew a b) (L.zw b))
end PI.ScPiBuildW.Loc.LocFrame
