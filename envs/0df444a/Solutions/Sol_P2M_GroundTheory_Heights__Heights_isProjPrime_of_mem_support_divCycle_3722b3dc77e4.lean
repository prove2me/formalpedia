-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_divCycle_3722b3dc77e4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:36.589884+00:00
-- url     : https://prove2.me/submissions/a9405eac-e473-4a10-abf3-a4078782ed85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_sup_span_linForm_b5797af1aa52
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_fundCycle_dd2dcd3ea52a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type*} [CommRing R] {n : ℕ}
variable [IsNoetherianRing R]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) R)} (hI : IsProjPrime I)
    (u : Fin n → R) {W : Ideal (MvPolynomial (Fin n) R)} (hW : W ∈ (divCycle I u).support) :
    IsProjPrime W :=
  isProjPrime_of_mem_support_fundCycle (isHomogIdeal_sup_span_linForm hI.isHomog u) hW
end GroundTheory.Heights₂.Heights
