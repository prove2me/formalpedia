-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.hop_deriv_fock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:57:22.90331+00:00
-- url     : https://prove2.me/submissions/916b3666-c15b-4064-b30f-f25e3331db6a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_hop_fock_C
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_hop_pderiv_cr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_hop_cr_C_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_hop_fock_X_mul
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_fock_add___b68a5475b7b1
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_fock_zero__4e684ff1ea02

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
variable (hB : FockBasic)
include hB
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution {c : ℝ} (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (k.1, k.2.1, !k.2.2) (fock c p) = C (2 * c : ℂ) * fock c (pderiv k p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => rw [hop_fock_C, pderiv_C, pderiv_C, fock_zero' hB hc, mul_zero]
  | add p q hp hq =>
    rw [fock_add'' hB hc, map_add, hp, hq, map_add, fock_add'' hB hc, mul_add]
  | mul_X p j ih =>
    have hsplit : pderiv k (X j * p) = X j * pderiv k p + (if k = j then p else 0) := by
      rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
      by_cases h : k = j
      · subst h; simp
      · simp [Pi.single_apply, h, Ne.symm h]
    have hcond : ((k.1, k.2.1, !k.2.2) = (j.1, j.2.1, !j.2.2)) ↔ k = j := by
      obtain ⟨a, i, e⟩ := j
      obtain ⟨b, l, e'⟩ := k
      simp [Prod.ext_iff]
    rw [mul_comm p (X j), hop_fock_X_mul hB hc, hop_pderiv_cr, ih, hsplit, fock_add'' hB hc, hop_fock_X_mul hB hc, hop_cr_C_mul]
    by_cases h : k = j
    · rw [if_pos (hcond.2 h), if_pos h]; ring
    · rw [if_neg (mt hcond.1 h), if_neg h, fock_zero' hB hc]; ring
end PositivityTheory.Rg.Sw.LC
