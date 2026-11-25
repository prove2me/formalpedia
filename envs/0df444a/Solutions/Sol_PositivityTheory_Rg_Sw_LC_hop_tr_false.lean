-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.hop_tr_false
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:32.722714+00:00
-- url     : https://prove2.me/submissions/6b23c2af-5b04-4030-a497-f66346e50e70

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_cr_true
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_hop_fock_X_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_hop_deriv_fock

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
theorem _root_.solution {c : ℝ} (hc : 0 < c) (a : Fin m) (i : Fin n) (q : PX m n) :
    C (2 * c : ℂ) * (X (a, i, false) * fock c q) = fock c (X (a, i, true) * q) + C (2 * c : ℂ) * fock c (pderiv (a, i, false) q) := by
  have h1 := hop_fock_X_mul hB hc (a, i, true) q
  have h2 := hop_deriv_fock hB hc (a, i, false) q
  rw [cr_true, smul_eq_C_mul] at h1
  simp only [Bool.not_false] at h2
  rw [h1, h2]; ring
end PositivityTheory.Rg.Sw.LC
