-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.vars_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:36.897047+00:00
-- url     : https://prove2.me/submissions/4f8c6832-6803-4f60-ab01-b9b50516e31e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_mem_range_phi

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
theorem _root_.solution (ε : Fin m → Bool) (s : Sym m n) (hs : SymbolInFirstFamily ε s) :
    (↑s.vars : Set ((Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool))) ⊆ Set.range (phi ε) := by
  intro v hv
  rw [Finset.mem_coe, mem_vars_iff_mem_support] at hv
  obtain ⟨d, hd, hvd⟩ := hv
  apply mem_range_phi
  rcases v with k | k
  · exact hs d hd k (Or.inl (Finsupp.mem_support_iff.mp hvd))
  · exact hs d hd k (Or.inr (Finsupp.mem_support_iff.mp hvd))
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
