-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.g_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:22.186796+00:00
-- url     : https://prove2.me/submissions/888179e2-6c1b-4fda-b9c0-524308164608

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_zero_right
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_nondeg_right
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_unitary

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
omit hS
namespace PI.ScPiBuildW.Loc.LocFrame
theorem _root_.solution {x : Fin n → ℂ} (hx : g *ᵥ x = 0) : x = 0 :=
  hJ_nondeg_right ε x fun x' => by rw [← hJ_unitary ε hg x' x, hx, hJ_zero_right]
end PI.ScPiBuildW.Loc.LocFrame
