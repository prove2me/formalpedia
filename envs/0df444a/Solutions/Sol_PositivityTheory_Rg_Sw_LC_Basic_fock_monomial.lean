-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.fock_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:50.618841+00:00
-- url     : https://prove2.me/submissions/28e41fb9-c420-464b-99f8-745a6a93d67d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fockMono_eq
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
theorem _root_.solution (c : ℝ) (s : Ix m n →₀ ℕ) : fock c (monomial s 1) = fockMono c s := by
  rw [fockMono_eq, fock_eq]
end PositivityTheory.Rg.Sw.LC.Basic
