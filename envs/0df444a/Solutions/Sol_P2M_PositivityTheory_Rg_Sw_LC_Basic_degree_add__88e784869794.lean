-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LC_Basic_degree_add__88e784869794
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:59.522906+00:00
-- url     : https://prove2.me/submissions/228ff50e-9d84-4fdd-974d-8971bf7640d5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp

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
theorem _root_.solution (a b : Ix m n →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  simp only [Finsupp.degree_eq_sum, Finsupp.add_apply, Finset.sum_add_distrib]
end PositivityTheory.Rg.Sw.LC.Basic
