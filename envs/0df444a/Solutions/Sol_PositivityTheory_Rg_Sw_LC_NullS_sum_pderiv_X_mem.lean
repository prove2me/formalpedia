-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.sum_pderiv_X_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:44:25.18681+00:00
-- url     : https://prove2.me/submissions/f48d46d3-9cb3-490b-b6ec-93aa541bc7d5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_pderiv_X_mem

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
theorem _root_.solution (ε : Fin m → Bool) (R : PX m n) (hR : R ∈ QA ε) (f : Fin m → Fin m × Fin n × Bool)
    (g : Fin m → Fin m × Fin n × Bool) : (∑ a, R * pderiv (f a) (X (g a) : PX m n)) ∈ QA ε := by
  apply Subalgebra.sum_mem
  intro a _
  exact mul_mem hR (pderiv_X_mem ε _ _)
end PositivityTheory.Rg.Sw.LC.NullS
