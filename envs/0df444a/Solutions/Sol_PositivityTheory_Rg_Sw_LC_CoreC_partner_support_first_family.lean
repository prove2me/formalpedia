-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.partner_support_first_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:13.478084+00:00
-- url     : https://prove2.me/submissions/d92d4d8a-34b0-4c75-a9e1-1fa5a2833d1f

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
theorem _root_.solution (ε : Fin m → Bool) {u : Fin m × Fin n × Bool →₀ ℕ} (hu : ∀ k ∈ u.support, ¬ inF1 ε k) :
    ∀ k ∈ (u.mapDomain pE).support, inF1 ε k := by
  intro k hk
  rw [Finsupp.mem_support_iff, Finsupp.mapDomain_equiv_apply, pE_symm] at hk
  have := hu (pE k) (Finsupp.mem_support_iff.mpr hk)
  rwa [first_family_partner_iff, not_not] at this
end PositivityTheory.Rg.Sw.LC.CoreC
