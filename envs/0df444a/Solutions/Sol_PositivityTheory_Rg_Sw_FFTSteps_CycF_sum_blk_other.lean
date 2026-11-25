-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.sum_blk_other
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:10.759451+00:00
-- url     : https://prove2.me/submissions/08ca8827-814c-4ef0-9e78-99c478bfb90f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_blk_of_not


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
theorem _root_.solution (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) {a : Fin m} (ha : ¬ ε a = β) (i : Fin n)
    (t : Bool) (st : Bool) :
    ∑ b, C (if st then star (blk ε β v a b) else blk ε β v a b) * (X (b, i, t) : PX m n) = X (a, i, t) := by
  simp only [blk_of_not β v ha]
  cases st <;> simp [apply_ite star, ite_mul]
end PositivityTheory.Rg.Sw.FFTSteps.CycF
