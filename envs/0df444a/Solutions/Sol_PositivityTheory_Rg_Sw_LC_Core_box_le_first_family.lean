-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Core.box_le_first_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:42:55.322048+00:00
-- url     : https://prove2.me/submissions/920e8ada-9004-4e20-8ac4-f40d00aa6c22

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_AdjoinFirstOperatorsPreservesFamily
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MonomialMemSupported
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_Core_monomial_mem_supported__ab1f28bee6a5

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Core
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Core
theorem _root_.solution (ε : Fin m → Bool) (R : Set (Fin m → ℕ)) : box ε R ≤ F1 (n := n) ε := by
  unfold box
  rw [Submodule.span_le]
  rintro _ ⟨s, hs, -, rfl⟩
  exact monomial_mem_supported' s hs 1
end PositivityTheory.Rg.Sw.LC.Core
