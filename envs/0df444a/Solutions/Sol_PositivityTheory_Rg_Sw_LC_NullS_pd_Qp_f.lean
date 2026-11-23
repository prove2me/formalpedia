-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.pd_Qp_f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:25.182582+00:00
-- url     : https://prove2.me/submissions/cba6475a-7c74-4061-a369-822897da13a6

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
theorem _root_.solution (ε : Fin m → Bool) (a : Fin m) (i k l : Fin n) :
    pderiv (a, i, false) (Qp ε k l : PX m n) = if l = i then C (sgn ε a) * X (a, k, true) else 0 := by
  rw [Qp_eq]
  simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases h : l = i <;> simp [h]
end PositivityTheory.Rg.Sw.LC.NullS
