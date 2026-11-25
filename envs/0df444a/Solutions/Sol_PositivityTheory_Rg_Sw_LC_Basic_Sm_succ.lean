-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.Sm_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:42:37.640855+00:00
-- url     : https://prove2.me/submissions/2dbb93a4-227d-4d38-b111-5c9e3b58ad31

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_Basic_degree_add__88e784869794

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
theorem _root_.solution (c : ℝ) (s : Ix m n →₀ ℕ) (k : Ix m n) :
    Sm c (s + Finsupp.single k 1) = (2 * c : ℂ) • (X (flp k) * Sm c s) := by
  simp only [Sm, Finsupp.mapDomain_add, Finsupp.mapDomain_single, degree_add', Finsupp.degree_single, pow_succ]
  rw [add_comm (Finsupp.mapDomain flp s), monomial_single_add, pow_one, ← mul_smul_comm, smul_monomial, smul_eq_mul,
    mul_comm (2 * (c : ℂ))]
end PositivityTheory.Rg.Sw.LC.Basic
