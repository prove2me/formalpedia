-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.fock_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:55.721384+00:00
-- url     : https://prove2.me/submissions/ad0288d4-2810-4c38-80d8-6275997f114c

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
theorem _root_.solution (c : ℝ) (a : ℂ) (p : PX m n) : fock c (a • p) = a • fock c p := by
  simp only [fock_eq, map_smul, Subalgebra.coe_smul, LinearMap.smul_apply]
end PositivityTheory.Rg.Sw.LC.Basic
