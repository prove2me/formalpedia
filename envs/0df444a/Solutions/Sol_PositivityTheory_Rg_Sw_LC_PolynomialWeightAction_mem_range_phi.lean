-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.mem_range_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:46:26.458309+00:00
-- url     : https://prove2.me/submissions/3eb38416-883e-49b8-94ce-ef35c10d168b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv

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
theorem _root_.solution (ε : Fin m → Bool) (v : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool))
    (h : inF1 ε (Sum.elim id id v)) : v ∈ Set.range (phi ε) := by
  rcases v with ⟨a, i, b⟩ | ⟨a, i, b⟩
  · simp only [inF1, Sum.elim_inl, id] at h
    subst h
    cases hε : ε a
    · exact ⟨Sum.inr (i, a), by simp [phi, hε]⟩
    · exact ⟨Sum.inl (i, a), by simp [phi, hε]⟩
  · simp only [inF1, Sum.elim_inr, id] at h
    subst h
    cases hε : ε a
    · exact ⟨Sum.inl (i, a), by simp [phi, hε]⟩
    · exact ⟨Sum.inr (i, a), by simp [phi, hε]⟩
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
