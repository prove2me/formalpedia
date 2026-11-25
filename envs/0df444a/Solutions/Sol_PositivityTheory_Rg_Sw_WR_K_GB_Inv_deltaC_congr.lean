-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.deltaC_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:21.936325+00:00
-- url     : https://prove2.me/submissions/1623c1ed-c880-4e9a-bef9-5ce3ed901fc6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_wd_congr
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
theorem _root_.solution {f g : Mc n → ℂ} {V : Set (Mc n)} (hV : IsOpen V) (h : ∀ y ∈ V, f y = g y)
    {x : Mc n} (hx : x ∈ V) : DeltaC f x = DeltaC g x := by
  rw [deltaC_eq, deltaC_eq]
  exact Finset.sum_congr rfl fun σ _ => by rw [wd_congr hV h _ x hx]
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
