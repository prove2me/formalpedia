-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.opH_rcp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:17.941368+00:00
-- url     : https://prove2.me/submissions/8c175998-25bb-4f6f-93f0-13e85d38a3cd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_opH_apply

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : RCP (opH s m b k l) := by
  intro R q
  have hd : ∀ v, pderiv v (R * MvPolynomial.C q) = pderiv v R * MvPolynomial.C q := by
    intro v
    rw [Derivation.leibniz, pderiv_C, smul_zero, zero_add, smul_eq_mul, mul_comm]
  rw [opH_apply, opH_apply]
  simp only [hd, add_mul, Finset.sum_mul, smul_mul_assoc, mul_assoc]
end PositivityTheory.Rg.Sw.SP
