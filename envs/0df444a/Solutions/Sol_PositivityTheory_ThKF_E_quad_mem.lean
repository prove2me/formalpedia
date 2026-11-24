-- Prove2me | solution 1 for PositivityTheory.ThKF.E.quad_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:41.791469+00:00
-- url     : https://prove2.me/submissions/ef485f3a-19b4-43d0-9cd5-0807d2c733c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_EqOfInner
import Theorems.Thm_GlobalTheory_RealWeil_dRho_mem_weylAlg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.E
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKF.E
theorem _root_.solution (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : quad X ∈ weylAlg l :=
  Subalgebra.smul_mem _ (sum_mem fun _ _ => sum_mem fun _ _ => Subalgebra.smul_mem _
    (add_mem (mul_mem (dRho_mem_weylAlg _) (dRho_mem_weylAlg _)) (mul_mem (dRho_mem_weylAlg _) (dRho_mem_weylAlg _))) _) _
end PositivityTheory.ThKF.E
