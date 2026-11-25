-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.Sm_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:43:48.956344+00:00
-- url     : https://prove2.me/submissions/34a5cc55-e2fc-4e25-a161-af84bec54d6c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_degree_mapDomain

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Basic
theorem _root_.solution (c : ℝ) (s : Ix m n →₀ ℕ) : DegLT (s.degree + 1) (Sm c s) := by
  intro t ht
  have := MvPolynomial.support_monomial_subset ht
  rw [Finset.mem_singleton] at this
  subst this
  rw [degree_mapDomain]
  omega
end PositivityTheory.Rg.Sw.LC.Basic
