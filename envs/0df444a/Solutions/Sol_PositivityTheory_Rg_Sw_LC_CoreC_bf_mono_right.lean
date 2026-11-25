-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.bf_mono_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:44:18.500051+00:00
-- url     : https://prove2.me/submissions/bcdfa261-d214-4dae-96b1-1ddd3222fb1f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SecondOperatorMemSecondFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_bf_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LC.CoreC.pE_apply
attribute [local simp] PositivityTheory.Rg.Sw.LC.CoreC.pE_pE



set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (w : (Fin m × Fin n × Bool →₀ ℕ) → ℂ) (p : PX m n) (t : Fin m × Fin n × Bool →₀ ℕ) :
    bf w p (monomial t 1) = p.coeff t * w t := by
  classical
  rw [bf_eq w (p.support ∪ {t}) Finset.subset_union_left ((support_monomial_subset).trans Finset.subset_union_right)]
  rw [Finset.sum_eq_single t]
  · simp [coeff_monomial]
  · intro s _ hs; simp [coeff_monomial, Ne.symm hs]
  · intro h; simp [coeff_monomial]; left; by_contra h'; exact h (Finset.mem_union_left _
      (MvPolynomial.mem_support_iff.mpr h'))
end PositivityTheory.Rg.Sw.LC.CoreC
