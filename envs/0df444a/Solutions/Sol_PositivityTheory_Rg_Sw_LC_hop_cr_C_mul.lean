-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.hop_cr_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:42.876796+00:00
-- url     : https://prove2.me/submissions/6fff6b8b-bc8c-437e-b070-276051920398

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_cr_false
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_cr_true

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
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution (c : ℝ) (j : Fin m × Fin n × Bool) (r : ℂ) (Q : PX m n) : cr c j (C r * Q) = C r * cr c j Q := by
  obtain ⟨a, i, e⟩ := j
  cases e
  · rw [cr_false, cr_false, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul, smul_eq_C_mul, smul_eq_C_mul]; ring
  · rw [cr_true, cr_true, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul, smul_eq_C_mul, smul_eq_C_mul]; ring
end PositivityTheory.Rg.Sw.LC
