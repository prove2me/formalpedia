-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.deltaC_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:28.503632+00:00
-- url     : https://prove2.me/submissions/c89e1d34-5411-4d00-879e-f6d3d8f1ba4f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_wd_smooth
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_deltaC_eq

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
theorem _root_.solution {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC F) U := by
  have : DeltaC F = fun x => ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * wd (List.ofFn fun t => E (σ t, t)) F x := funext (deltaC_eq F)
  rw [this]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (wd_smooth hU hF _)
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
