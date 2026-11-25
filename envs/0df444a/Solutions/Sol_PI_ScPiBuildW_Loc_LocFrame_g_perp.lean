-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.g_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:03.410375+00:00
-- url     : https://prove2.me/submissions/97351150-805f-466b-9873-3af60365feb2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_unitary
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_e_mem
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_hJ_X_left
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_g_surj

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
theorem _root_.solution {y : Fin n → ℂ} (hy : ∀ a, hJ ε (L.e a) y = 0) (a : Fin r) : hJ ε (L.e a) (g *ᵥ y) = 0 := by
  obtain ⟨x', hx', hgx⟩ := L.g_surj hg hS (L.e_mem a)
  rw [← hgx, hJ_unitary ε hg]
  exact L.hJ_X_left hx' hy
end PI.ScPiBuildW.Loc.LocFrame
