-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.det_sub_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:52:12.383619+00:00
-- url     : https://prove2.me/submissions/0551a481-d0c0-4177-a365-0478eace6ae4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar

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
theorem _root_.solution (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) (hc : ¬ Function.Injective c) :
    (A.submatrix c id).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hc
  exact Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
