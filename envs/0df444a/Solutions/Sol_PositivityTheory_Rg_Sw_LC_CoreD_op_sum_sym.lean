-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreD.op_sum_sym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:22.466463+00:00
-- url     : https://prove2.me/submissions/67451d01-11b5-4f6d-afda-2b862b3a8f3a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BoxLeFirstFamily

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreD
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.LC.CoreD
theorem _root_.solution {ι : Type*} (F : Finset ι) (g : ι → Sym m n) (f : PX m n) :
    op (∑ i ∈ F, g i) f = ∑ i ∈ F, op (g i) f := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [op]
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add_sym, ih]
end PositivityTheory.Rg.Sw.LC.CoreD
