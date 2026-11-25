-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.symK_rename_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:12.770749+00:00
-- url     : https://prove2.me/submissions/b0d8c195-dfcc-4f54-8a83-0aed6ca14428

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_Dsrc_inl
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_Dsrc_inr

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
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (v : FinalTheorems m n) :
    symK ε i j (rename (phi ε) (X v)) = rename (phi ε) (Dsrc (m := m) i j (X v)) := by
  rcases v with ⟨l, a⟩ | ⟨l, b⟩
  · rw [Dsrc_inl]
    by_cases hl : l = j <;> cases h : ε a <;> simp [phi, symK, mkDerivation_X, h, hl]
  · rw [Dsrc_inr]
    by_cases hl : l = i <;> cases h : ε b <;> simp [phi, symK, mkDerivation_X, h, hl]
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
