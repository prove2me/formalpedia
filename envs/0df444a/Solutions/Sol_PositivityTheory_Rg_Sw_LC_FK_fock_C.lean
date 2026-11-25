-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.FK.fock_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:53:31.394186+00:00
-- url     : https://prove2.me/submissions/12ab2abb-7ae6-428c-bfdc-2eee8978f31d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivComm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_fock_one

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.FK
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.FK
theorem _root_.solution (hB : FockBasic) (c : ℝ) (hc : 0 < c) (a : ℂ) : fock c (C a : PX m n) = C a := by
  have hL := (hB m n c hc).1
  rw [show (C a : PX m n) = a • 1 by rw [smul_eq_C_mul, mul_one], hL.map_smul, fock_one, smul_eq_C_mul, mul_one]
end PositivityTheory.Rg.Sw.LC.FK
