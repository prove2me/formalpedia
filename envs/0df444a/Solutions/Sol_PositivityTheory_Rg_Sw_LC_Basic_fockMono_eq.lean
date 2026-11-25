-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.fockMono_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:50:45.050289+00:00
-- url     : https://prove2.me/submissions/3721bfd4-e15d-4ed2-8862-f8ffeecb6895

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_coe_phi_monomial

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
theorem _root_.solution (c : ℝ) (s : Ix m n →₀ ℕ) :
    fockMono c s = ((phi c (monomial s 1) : CrAlg m n c) : Module.End ℂ (PX m n)) 1 := by
  rw [coe_phi_monomial]; rfl
end PositivityTheory.Rg.Sw.LC.Basic
