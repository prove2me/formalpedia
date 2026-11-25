-- Prove2me | solution 1 for PI.AlgValsFin.W.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:39:05.239476+00:00
-- url     : https://prove2.me/submissions/6311c56c-f75f-43ef-b2d5-70914ee282ed

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ValuedAtFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Theorems.Thm_PI_AlgValsFin_W_evF_diag
import Theorems.Thm_PI_AlgValsFin_W_evI_diag
import Theorems.Thm_PI_AlgValsFin_W_evI_localIdele
import Theorems.Thm_PI_AlgValsFin_W_evF_localIdele_ne
import Theorems.Thm_PI_AlgValsFin_W_evF_localIdele_self
import Theorems.Thm_PI_AlgValsFin_W_evI_infDiag
import Theorems.Thm_PI_AlgValsFin_W_evF_infDiag
import Theorems.Thm_PI_AlgValsFin_W_valued_atFin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution : Decomp L := by
  classical
  intro k T hT
  set D := infDiag k * (∏ v ∈ T, localIdele L v (atFin v k)) with hD
  refine ⟨D⁻¹ * diagUnits L k, ⟨?_, fun v => ?_⟩, by rw [mul_inv_cancel_left]⟩
  · funext w
    show ((evI w (D⁻¹ * diagUnits L k) : (w.Completion)ˣ) : w.Completion) = (1 : InfiniteAdeleRing L) w
    have hP : evI w (∏ v ∈ T, localIdele L v (atFin v k)) = 1 := by
      rw [map_prod]
      exact Finset.prod_eq_one fun v _ => evI_localIdele w v _
    rw [map_mul, map_inv, hD, map_mul, hP, evI_infDiag, evI_diag, mul_one, inv_mul_cancel]
    rfl
  · show Valued.v ((evF v (D⁻¹ * diagUnits L k) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
    have hP : evF v (∏ u ∈ T, localIdele L u (atFin u k)) = if v ∈ T then atFin v k else 1 := by
      rw [map_prod]
      split_ifs with hv
      · rw [Finset.prod_eq_single v (fun u _ hu => evF_localIdele_ne v u (Ne.symm hu) _)
          (fun h => absurd hv h), evF_localIdele_self]
      · exact Finset.prod_eq_one fun u hu => evF_localIdele_ne v u (by rintro rfl; exact hv hu) _
    rw [map_mul, map_inv, hD, map_mul, hP, evF_infDiag, evF_diag, one_mul]
    split_ifs with hv
    · rw [inv_mul_cancel]
      simp
    · rw [inv_one, one_mul, valued_atFin, hT v hv]
      simp
end PI.AlgValsFin.W
