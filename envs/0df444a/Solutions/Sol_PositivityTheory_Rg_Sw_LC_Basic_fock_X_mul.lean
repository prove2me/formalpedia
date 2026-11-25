-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.fock_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:37.994339+00:00
-- url     : https://prove2.me/submissions/4459215a-d18c-4694-ae6f-3e2119e6e56c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_eq

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Basic
theorem _root_.solution (c : ℝ) (k : Ix m n) (p : PX m n) : fock c (X k * p) = cr c k (fock c p) := by
  rw [fock_eq, fock_eq, map_mul, Subalgebra.coe_mul, Module.End.mul_apply]
  simp [phi, gen]
end PositivityTheory.Rg.Sw.LC.Basic
