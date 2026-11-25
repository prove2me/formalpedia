-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.Dsrc_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:48.803318+00:00
-- url     : https://prove2.me/submissions/4a0b9ced-2445-455f-a560-e80c2fc02f70

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_phi_injective
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_symK_rename

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
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (p : MvPolynomial (FinalTheorems m n) ℂ)
    (h : symK ε i j (rename (phi ε) p) = 0) : Dsrc (m := m) i j p = 0 := by
  rw [symK_rename] at h
  exact rename_injective _ (phi_injective ε) (h.trans (map_zero _).symm)
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
