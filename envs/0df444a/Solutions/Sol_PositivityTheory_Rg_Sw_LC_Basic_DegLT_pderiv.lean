-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.DegLT.pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:43:45.31879+00:00
-- url     : https://prove2.me/submissions/12499b9e-9355-400e-8f84-9828679d6e70

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
namespace DegLT
theorem _root_.solution {d : ℕ} {P : PX m n} (k : Ix m n) (hP : DegLT d P) : DegLT d (pderiv k P) := by
  classical
  intro t ht
  rw [P.as_sum, map_sum] at ht
  obtain ⟨s, hs, hts⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum ht)
  rw [pderiv_monomial] at hts
  have ht' := MvPolynomial.support_monomial_subset hts
  rw [Finset.mem_singleton] at ht'
  subst ht'
  refine lt_of_le_of_lt ?_ (hP s hs)
  simp only [Finsupp.degree_eq_sum]
  exact Finset.sum_le_sum fun i _ => tsub_le_self
end DegLT
end PositivityTheory.Rg.Sw.LC.Basic
