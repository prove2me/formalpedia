-- Prove2me | solution 1 for PI.IsoInvMetricW.hermitian_vector_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:44:51.218799+00:00
-- url     : https://prove2.me/submissions/3cb73b0a-0928-4d57-99fe-23c1fbb7987e

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
theorem _root_.solution : HvMap := by
  intro Lt _ _ N nu f x
  funext I
  simp only [VnuMap, hvC, minY, fr]
  rw [finsum_eq_sum_of_fintype]
  simp_rw [← Finset.prod_mul_distrib]
  refine (sum_prod_cc (fun s c K =>
      (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (K k)).det *
      (Matrix.of fun i j : Fin ((nu s).colLen c) => x s (K i) (j : ℕ)).det)).trans ?_
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  have hcb := metric_constant_bound _ _ (Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b)
    (Matrix.of fun (b : Fin N) (j : Fin ((nu s).colLen c)) => x s b (j : ℕ))
  calc _ = ∑ K : Fin ((nu s).colLen c) ↪o Fin N,
        ((Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b).submatrix id K).det *
        ((Matrix.of fun (b : Fin N) (j : Fin ((nu s).colLen c)) => x s b (j : ℕ)).submatrix K id).det := rfl
    _ = _ := hcb.symm
    _ = _ := by
      congr 1
end PI.IsoInvMetricW
