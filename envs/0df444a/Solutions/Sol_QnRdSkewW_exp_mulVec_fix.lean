-- Prove2me | solution 1 for QnRdSkewW.exp_mulVec_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:07.376562+00:00
-- url     : https://prove2.me/submissions/55788c75-df55-4906-954b-5cae15eb3ec6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_SkewReductionGroup
import Theorems.Thm_QnRdSkewW_exp_mul_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
namespace QnRdSkewW
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (hXv : X *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) *ᵥ v = v := by
  let E : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun j _ => v j
  have hXE : X * E = 0 := by
    ext j l
    have := congrFun hXv j
    simpa [E, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h := exp_mul_fix X E hXE t
  funext j
  have := congrFun (congrFun h j) j
  simpa [E, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
end QnRdSkewW
