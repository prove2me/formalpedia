-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.act_emb_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:49:25.606862+00:00
-- url     : https://prove2.me/submissions/284224cf-ff75-4ac0-b79f-3fe1071be75c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_sum_blk
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_sum_blk_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
theorem _root_.solution (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) :
    (act (n := n) (blk ε β v)).comp (emb ε β) = (emb ε β).comp (sub v (v.map star)) := by
  refine MvPolynomial.algHom_ext fun x => ?_
  rcases x with ⟨i, a⟩ | ⟨i, a⟩
  · simp [act, emb, sub, jv, sum_blk, map_sum]
  · simpa [act, emb, sub, jv, map_sum] using sum_blk_star (n := n) β v i a true
end PositivityTheory.Rg.Sw.FFTSteps.CycF
