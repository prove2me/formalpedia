-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreD.symK_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:43:14.577323+00:00
-- url     : https://prove2.me/submissions/c33a2318-2938-4d49-baa4-8e8f06e8c1e7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_EquivLift
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ZeroRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymbolFirstFamilyOfMem

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreD
variable {m n : ℕ} (ε : Fin m → Bool)
variable {ε}
namespace PositivityTheory.Rg.Sw.LC.CoreD
theorem _root_.solution (i j : Fin n) (v : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)) :
    symK ε i j (X v) = 0 ∨ ∃ v', ∃ c : ℂ, symK ε i j (X v) = c • (X v' : Sym m n) ∧ inF1 ε (Sum.elim id id v') := by
  unfold symK
  rw [mkDerivation_X]
  rcases v with ⟨a, b, e⟩ | ⟨a, b, e⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · by_cases ha : ε a = true
    · rw [if_pos ha]; split_ifs with h
      · exact Or.inr ⟨Sum.inl (a, i, false), 1, by simp, by simp [inF1, ha]⟩
      · exact Or.inl rfl
    · rw [if_neg ha]; split_ifs with h
      · exact Or.inr ⟨Sum.inl (a, j, true), -1, by simp, by simp [inF1]; simpa using ha⟩
      · exact Or.inl rfl
  · by_cases ha : ε a = true
    · rw [if_pos ha]; split_ifs with h
      · exact Or.inr ⟨Sum.inr (a, j, false), -1, by simp, by simp [inF1, ha]⟩
      · exact Or.inl rfl
    · rw [if_neg ha]; split_ifs with h
      · exact Or.inr ⟨Sum.inr (a, i, true), 1, by simp, by simp [inF1]; simpa using ha⟩
      · exact Or.inl rfl
end PositivityTheory.Rg.Sw.LC.CoreD
