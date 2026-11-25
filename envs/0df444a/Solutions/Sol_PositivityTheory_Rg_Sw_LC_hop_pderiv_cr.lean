-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.hop_pderiv_cr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:24.132157+00:00
-- url     : https://prove2.me/submissions/5eb92459-2b08-44ce-a900-7a3f570562d9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_hop_pderiv_comm__fcbfde84e7a3
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
theorem _root_.solution (c : ℝ) (j k : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (cr c j Q) = cr c j (pderiv k Q) + C (2 * c : ℂ) * (if k = (j.1, j.2.1, !j.2.2) then Q else 0) := by
  obtain ⟨a, i, e⟩ := j
  cases e
  · rw [cr_false, cr_false]
    simp only [map_add, map_neg, map_smul, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_C_mul,
      hop_pderiv_comm' k (a, i, false)]
    by_cases h : k = (a, i, true)
    · subst h; simp [Pi.single_apply]; ring
    · simp [Pi.single_apply, h, Ne.symm h]
  · rw [cr_true, cr_true]
    simp only [map_add, map_neg, map_smul, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_C_mul,
      hop_pderiv_comm' k (a, i, true)]
    by_cases h : k = (a, i, false)
    · subst h; simp [Pi.single_apply]; ring
    · simp [Pi.single_apply, h, Ne.symm h]
end PositivityTheory.Rg.Sw.LC
