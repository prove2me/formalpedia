-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.deltaC_eq_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:32.713126+00:00
-- url     : https://prove2.me/submissions/41f8994d-970e-4687-a98a-97a7450ec237

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBLink

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {F G : Mc n → ℂ} {U : Set (Mc n)}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (H : Mc n → ℂ) :
    DeltaC H = fun b => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * word (blk σ) H b := by
  funext b
  simp only [DeltaC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, word, blk, List.foldr_map]
end PositivityTheory.Rg.Sw.WR.K.GB
