-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.monomial_mem_first_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:42:14.870846+00:00
-- url     : https://prove2.me/submissions/c70751f8-cf68-44dd-82c0-0658659da691

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_mem_first_family_iff


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
theorem _root_.solution (ε : Fin m → Bool) {t : Fin m × Fin n × Bool →₀ ℕ} (ht : ∀ k ∈ t.support, inF1 ε k) (d : ℂ) :
    (monomial t d : PX m n) ∈ F1 ε := by
  rw [mem_first_family_iff]
  intro s hs
  have : s = t := by
    by_contra h; exact (MvPolynomial.mem_support_iff.mp hs) (by rw [coeff_monomial, if_neg (Ne.symm h)])
  subst this; exact ht
end PositivityTheory.Rg.Sw.LC.CoreC
