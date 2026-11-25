-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.dd_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:52:07.637299+00:00
-- url     : https://prove2.me/submissions/ced175aa-4d0b-46e1-bc39-617dca8fb5e8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_top_succ_le
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_WR_K_GB_Inv_two_le_top__23b5670f2749

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
theorem _root_.solution {g : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hg : ContDiffOn ℂ (⊤ : ℕ∞) g U)
    (a b : Mc n) {x : Mc n} (hx : x ∈ U) : dd b (dd a g) x = dd a (dd b g) x := by
  have hc : ContDiffAt ℂ (⊤ : ℕ∞) g x := hg.contDiffAt (hU.mem_nhds hx)
  have hsymm : IsSymmSndFDerivAt ℂ g x :=
    hc.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact two_le_top')
  have hd : DifferentiableAt ℂ (fderiv ℂ g) x := (hc.fderiv_right top_succ_le).differentiableAt (by simp)
  have key : ∀ v w : Mc n, fderiv ℂ (fun y => fderiv ℂ g y v) x w = fderiv ℂ (fderiv ℂ g) x w v := by
    intro v w
    have h := (ContinuousLinearMap.apply ℂ ℂ v).hasFDerivAt.comp x hd.hasFDerivAt
    exact congrArg (fun L => L w) h.fderiv
  unfold dd
  rw [key, key]
  exact hsymm b a
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
