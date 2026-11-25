-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.sum_blk_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:12.881185+00:00
-- url     : https://prove2.me/submissions/eaa434ce-bb65-4c11-aedf-fa376ff81761

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_blk_of
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_sum_rw


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
theorem _root_.solution (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (a : Rw ε β) (i : Fin n) (t : Bool) :
    ∑ b, C (star (blk ε β v a.1 b)) * (X (b, i, t) : PX m n) = ∑ j : Rw ε β, C (star (v a j)) * X (j.1, i, t) := by
  rw [← sum_rw β (fun j => C (star (v a j)) * (X (j.1, i, t) : PX m n))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [blk_of β v a.2]
  split_ifs <;> simp
end PositivityTheory.Rg.Sw.FFTSteps.CycF
