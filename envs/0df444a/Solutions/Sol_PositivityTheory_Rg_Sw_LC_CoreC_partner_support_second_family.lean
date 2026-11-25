-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.partner_support_second_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:15.484047+00:00
-- url     : https://prove2.me/submissions/5b57a76b-bcd5-46de-bd9f-0394d91437c1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_first_family_partner_iff
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_symm


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
theorem _root_.solution (ε : Fin m → Bool) {u : Fin m × Fin n × Bool →₀ ℕ} (hu : ∀ k ∈ u.support, inF1 ε k) :
    ∀ k ∈ (u.mapDomain pE).support, ¬ inF1 ε k := by
  intro k hk
  rw [Finsupp.mem_support_iff, Finsupp.mapDomain_equiv_apply, pE_symm] at hk
  have := hu (pE k) (Finsupp.mem_support_iff.mpr hk)
  rwa [first_family_partner_iff] at this
end PositivityTheory.Rg.Sw.LC.CoreC
