-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.symK_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:07.776512+00:00
-- url     : https://prove2.me/submissions/6d074d14-72ec-446d-b26e-6fc4f4b6aa35

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_symK_rename_X

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
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (p : MvPolynomial (FinalTheorems m n) ℂ) :
    symK ε i j (rename (phi ε) p) = rename (phi ε) (Dsrc (m := m) i j p) := by
  refine MvPolynomial.induction_on (motive := fun p => symK ε i j (rename (phi ε) p) =
    rename (phi ε) (Dsrc (m := m) i j p)) p ?_ ?_ ?_
  · intro a
    simp [MvPolynomial.derivation_C]
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro p v hp
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, symK_rename_X]
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
