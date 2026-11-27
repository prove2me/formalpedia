-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreD.psi_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:55.936484+00:00
-- url     : https://prove2.me/submissions/a4a3c224-1980-4a04-b376-5bcce499086c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymbolFirstFamilyOfMem
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_psi_eq

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
theorem _root_.solution (p q : Sym m n) (r : ℂ) : psi p (r • q) = r * psi p q := by
  classical
  rw [psi_eq p (r • q) (p.support ∪ q.support) (Finset.union_subset_union le_rfl support_smul),
    psi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [coeff_smul, smul_eq_mul]; ring
end PositivityTheory.Rg.Sw.LC.CoreD
