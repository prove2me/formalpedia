-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreD.psi_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:36:54.583663+00:00
-- url     : https://prove2.me/submissions/b62ca7a1-1485-4cd0-bc65-844c6c9c101e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymbolFirstFamilyOfMem
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_psi_add_right

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
theorem _root_.solution {ι : Type*} (p : Sym m n) (F : Finset ι) (f : ι → Sym m n) :
    psi p (∑ x ∈ F, f x) = ∑ x ∈ F, psi p (f x) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [psi]
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, psi_add_right, ih]
end PositivityTheory.Rg.Sw.LC.CoreD
