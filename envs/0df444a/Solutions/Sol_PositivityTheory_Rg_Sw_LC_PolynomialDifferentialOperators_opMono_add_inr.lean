-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.opMono_add_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:53.068451+00:00
-- url     : https://prove2.me/submissions/b3e4bf7e-4ccd-46fe-8847-003b8859cbb3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ComapDomainInlAdd
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_dvE_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_dvE_single
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_opMono_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_comapDomain_inl_add

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
theorem _root_.solution (t : Ix m n ⊕ Ix m n →₀ ℕ) (k : Ix m n) (f : PX m n) :
    opMono (t + Finsupp.single (Sum.inr k) 1) f = opMono t (pderiv k f) := by
  rw [opMono_eq, opMono_eq, comapDomain_inl_add]
  have h1 : (Finsupp.single (Sum.inr k) 1 : Ix m n ⊕ Ix m n →₀ ℕ).comapDomain Sum.inl Sum.inl_injective.injOn = 0 := by
    ext j; simp [Finsupp.comapDomain_apply, Finsupp.single_apply]
  have h2 : (fun j : Ix m n => (t + Finsupp.single (Sum.inr k) 1 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr j)) =
      (fun j => t (Sum.inr j)) + Pi.single k 1 := by
    ext j; simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  rw [h1, add_zero, h2, ← dvE_mul, dvE_single]
  rfl
end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
