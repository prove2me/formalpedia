-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.local_frame_preserves_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:29:37.58314+00:00
-- url     : https://prove2.me/submissions/f73d757a-fa13-4f9b-9ac0-48c4d19de394

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_add_left
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_unitary
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_hJ_X_left
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_g_perp

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
theorem _root_.solution {y : Fin n → ℂ} (hy : ∀ a, hJ ε (L.e a) y = 0) (hz : hJ ε L.z y = 0) :
    hJ ε L.z (g *ᵥ y) = 0 := by
  have h1 : g *ᵥ L.z = L.z + (g - 1) *ᵥ L.z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have h2 : hJ ε (g *ᵥ L.z) (g *ᵥ y) = 0 := by rw [hJ_unitary ε hg, hz]
  rw [h1, hJ_add_left, L.hJ_X_left hS.2 (L.g_perp hg hS hy), add_zero] at h2
  exact h2
end PI.ScPiBuildW.Loc.LocFrame
