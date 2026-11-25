-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.wd_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:59:10.121799+00:00
-- url     : https://prove2.me/submissions/f82f30d3-7fc9-4577-9867-ee0215600d80

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
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
theorem _root_.solution {f g : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (h : ∀ y ∈ U, f y = g y)
    (L : List (Mc n)) : ∀ x ∈ U, wd L f x = wd L g x := by
  induction L with
  | nil => exact h
  | cons H L ih => intro x hx; exact dd_congr hU ih H hx
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
