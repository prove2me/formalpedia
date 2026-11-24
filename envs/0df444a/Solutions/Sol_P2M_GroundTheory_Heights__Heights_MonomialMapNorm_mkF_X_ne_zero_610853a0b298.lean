-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_X_ne_zero_610853a0b298
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:31.215122+00:00
-- url     : https://prove2.me/submissions/7fa20d48-de54-4278-90a6-7e8cd1996fc6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (P : ArithVariety n)
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.MonomialMapNorm
theorem _root_.solution {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) :
    P.mkF (X ⟨k, c k⟩) ≠ 0 := fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)
end GroundTheory.Heights₂.Heights.MonomialMapNorm
