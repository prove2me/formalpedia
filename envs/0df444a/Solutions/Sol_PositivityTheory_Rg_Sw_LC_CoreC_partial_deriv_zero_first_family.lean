-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.partial_deriv_zero_first_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:42:16.395881+00:00
-- url     : https://prove2.me/submissions/78f2456f-b4d0-4248-9155-62883a6b1e65

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_mem_first_family_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (ε : Fin m → Bool) {k} (hk : ¬ inF1 ε k) {p : PX m n} (hp : p ∈ F1 ε) : pderiv k p = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨s, hs, hks⟩ := (mem_vars k).mp hv
  exact hk ((mem_first_family_iff ε p).mp hp s hs k hks)
end PositivityTheory.Rg.Sw.LC.CoreC
