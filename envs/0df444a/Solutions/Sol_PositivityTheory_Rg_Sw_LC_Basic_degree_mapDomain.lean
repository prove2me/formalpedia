-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.degree_mapDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:36.733556+00:00
-- url     : https://prove2.me/submissions/bc673fc5-e5a1-4031-b25f-320e3a67a57b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_flp_injective

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
theorem _root_.solution (t : Ix m n →₀ ℕ) : (Finsupp.mapDomain flp t).degree = t.degree := by
  simp only [Finsupp.degree_eq_sum]
  rw [← Equiv.sum_comp flpEquiv]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finsupp.mapDomain_apply flp_injective t i
end PositivityTheory.Rg.Sw.LC.Basic
