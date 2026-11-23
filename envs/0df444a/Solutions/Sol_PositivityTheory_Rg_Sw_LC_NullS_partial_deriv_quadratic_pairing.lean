-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.partial_deriv_quadratic_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:00.04354+00:00
-- url     : https://prove2.me/submissions/b96fd99f-44ab-413f-a9cb-e7fa4ac1ad91

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullOperatorEvaluation
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_Qp_eq

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
theorem _root_.solution (ε : Fin m → Bool) (a : Fin m) (j k l : Fin n) :
    pderiv (a, j, true) (Qp ε k l : PX m n) = if k = j then C (sgn ε a) * X (a, l, false) else 0 := by
  rw [Qp_eq]
  simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases h : k = j <;> simp [h]
end PositivityTheory.Rg.Sw.LC.NullS
