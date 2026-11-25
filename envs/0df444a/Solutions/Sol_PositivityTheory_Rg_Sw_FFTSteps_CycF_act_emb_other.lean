-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.act_emb_other
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:14.569572+00:00
-- url     : https://prove2.me/submissions/e39345f3-cc30-4911-b899-85a14d436e4f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_sum_blk_other

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
theorem _root_.solution (β β' : Bool) (hne : β' ≠ β) (v : Matrix (Rw ε β) (Rw ε β) ℂ) :
    (act (n := n) (blk ε β v)).comp (emb ε β') = emb ε β' := by
  refine MvPolynomial.algHom_ext fun x => ?_
  rcases x with ⟨i, a⟩ | ⟨i, a⟩
  · have hi : ¬ ε i.1 = β := fun h => hne (i.2.symm.trans h)
    have := sum_blk_other (n := n) β v hi a false false
    simp only [Bool.false_eq_true, if_false] at this
    simp [act, emb, jv, this]
  · have hi : ¬ ε i.1 = β := fun h => hne (i.2.symm.trans h)
    have := sum_blk_other (n := n) β v hi a true true
    simp only [if_true] at this
    simpa [act, emb, jv] using this
end PositivityTheory.Rg.Sw.FFTSteps.CycF
