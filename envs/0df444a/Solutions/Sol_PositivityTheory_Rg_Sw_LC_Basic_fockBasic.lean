-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.fockBasic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:34.091795+00:00
-- url     : https://prove2.me/submissions/9b2732b1-46f0-4692-9f13-4698239c151d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_X_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_injective
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_surjective

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
theorem _root_.solution : FockBasic := by
  intro m n c hc
  exact ⟨⟨fock_add c, fun a p => fock_smul c a p⟩, ⟨fock_injective c hc, fock_surjective c hc⟩, fun k p => fock_X_mul c k p⟩
end PositivityTheory.Rg.Sw.LC.Basic
