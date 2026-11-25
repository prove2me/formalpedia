-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.wd_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:29.67249+00:00
-- url     : https://prove2.me/submissions/6d9b814c-9870-4e56-b754-1bef97ba347b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_wd_smooth
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_diffAt
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_dd_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open PositivityTheory.Rg.Sw.WR.K.GB.Inv
namespace PositivityTheory.Rg.Sw.WR.K.GB.Inv
theorem _root_.solution (T : Mc n →L[ℂ] Mc n) {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U)
    (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (L : List (Mc n)) :
    ∀ x, T x ∈ U → wd L (fun c => F (T c)) x = wd (L.map T) F (T x) := by
  induction L with
  | nil => intro x _; rfl
  | cons H L ih =>
    intro x hx
    have hV : IsOpen (T ⁻¹' U) := hU.preimage T.continuous
    show dd H (wd L (fun c => F (T c))) x = dd (T H) (wd (L.map T) F) (T x)
    rw [dd_congr hV (g := fun c => wd (L.map T) F (T c)) (fun y hy => ih y hy) H hx]
    unfold dd
    have hG : DifferentiableAt ℂ (wd (L.map T) F) (T x) := diffAt hU (wd_smooth hU hF _) hx
    have h := hG.hasFDerivAt.comp x T.hasFDerivAt
    exact congrArg (fun L => L H) h.fderiv
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
