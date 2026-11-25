-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.rdeg_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:22.433245+00:00
-- url     : https://prove2.me/submissions/a066d476-ac7c-4785-a150-28c01e61a38c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (ε : Fin m → Bool) (k : Fin m × Fin n × Bool) (hk : inF1 ε k) :
    rdeg ε (Finsupp.single k 1) = fun a => if a = k.1 then 1 else 0 := by
  funext a
  unfold rdeg
  obtain ⟨a0, i0, b0⟩ := k
  simp only [inF1] at hk
  subst hk
  by_cases ha : a = a0
  · subst ha
    rw [if_pos rfl, Finset.sum_eq_single i0]
    · simp
    · intro i _ hi; simp [Finsupp.single_apply, Ne.symm hi]
    · simp
  · rw [if_neg ha]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h; exact ha (congrArg Prod.fst h).symm
end PositivityTheory.Rg.Sw.LC.CoreC
