-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.hop_tr_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:34.886803+00:00
-- url     : https://prove2.me/submissions/b1b5824f-fa88-482e-bc2c-3118266fe412

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_cr_false
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
    C (2 * c : ℂ) * (X (a, i, true) * fock c q) = fock c (X (a, i, false) * q) + C (2 * c : ℂ) * fock c (pderiv (a, i, true) q) := by
  have h1 := hop_fock_X_mul hB hc (a, i, false) q
  have h2 := hop_deriv_fock hB hc (a, i, true) q
  rw [cr_false, smul_eq_C_mul] at h1
  simp only [Bool.not_true] at h2
  rw [h1, h2]; ring
end PositivityTheory.Rg.Sw.LC
