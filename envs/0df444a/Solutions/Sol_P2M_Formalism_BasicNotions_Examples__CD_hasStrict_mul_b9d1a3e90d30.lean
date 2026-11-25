-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_hasStrict_mul_b9d1a3e90d30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:06.60199+00:00
-- url     : https://prove2.me/submissions/d593a52a-c439-494d-97d5-a520e7ff1fc3

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hasStrict_logA_de7a3d570658
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hasStrict_exp_comp_abeda0874ee6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution (L M : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => logA 𝔸 (exp (L p) * exp (M p))) (L + M) (0 : 𝔸 × 𝔸) := by
  have hprod := (hasStrict_exp_comp L).mul' (hasStrict_exp_comp M)
  simp only [map_zero, exp_zero, one_smul, MulOpposite.op_one] at hprod
  have hlog : HasStrictFDerivAt (logA 𝔸) (ContinuousLinearMap.id ℝ 𝔸)
      (((fun p : 𝔸 × 𝔸 => exp (L p)) * fun p : 𝔸 × 𝔸 => exp (M p)) 0) := by
    simp only [Pi.mul_apply, map_zero, exp_zero, mul_one]
    exact hasStrict_logA
  have h := hlog.comp (0 : 𝔸 × 𝔸) hprod
  rw [ContinuousLinearMap.id_comp, add_comm] at h
  exact h
end Formalism.BasicNotions.Examples₂.CD
