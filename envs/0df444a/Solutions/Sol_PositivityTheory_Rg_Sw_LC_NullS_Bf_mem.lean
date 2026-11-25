-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.Bf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:39.380964+00:00
-- url     : https://prove2.me/submissions/265b76b8-7ea6-4671-9ac7-cc2307178e88

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_Bf_comm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_Bf_der
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_Bf_gen

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.NullS
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) : ∀ U ∈ QA ε, ∀ V ∈ QA ε, Bf ε i j U V ∈ QA ε := by
  intro U hU
  apply Bf_der ε i j U
  intro k l
  rw [Bf_comm]
  exact Bf_der ε i j (Qp ε k l) (fun k' l' => Bf_gen ε i j k l k' l') U hU
end PositivityTheory.Rg.Sw.LC.NullS
