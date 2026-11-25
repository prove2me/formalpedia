-- Prove2me | solution 1 for PI.IsoInvMetricW.metric_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:43:34.043136+00:00
-- url     : https://prove2.me/submissions/ca1ce5ce-48f7-4dc1-b411-c537acd2186d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_MetricConstantBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_HermitianVectorMap
import Theorems.Thm_PI_IsoInvMetricW_sum_prod_cc
import Theorems.Thm_PI_IsoInvMetricW_metric_constant_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset PI.IsoInvMetric
open PI PI.IsoInvMetricW
namespace PI.IsoInvMetricW
theorem _root_.solution : EMul := by
  intro Lt _ _ N nu f g I K
  simp only [E]
  simp_rw [← Finset.prod_mul_distrib]
  refine (sum_prod_cc (fun s c J =>
      (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J k)).det *
      (Matrix.of fun i k : Fin ((nu s).colLen c) => g s (J i) (K s c k)).det)).trans ?_
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  have hcb := metric_constant_bound _ _ (Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b)
    (Matrix.of fun (b : Fin N) (k : Fin ((nu s).colLen c)) => g s b (K s c k))
  calc _ = ∑ J : Fin ((nu s).colLen c) ↪o Fin N,
        ((Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b).submatrix id J).det *
        ((Matrix.of fun (b : Fin N) (k : Fin ((nu s).colLen c)) => g s b (K s c k)).submatrix J id).det := rfl
    _ = _ := hcb.symm
    _ = _ := by
      congr 1
end PI.IsoInvMetricW
