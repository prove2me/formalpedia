-- Prove2me | solution 1 for PI.Dv.GLP.cG_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:52:49.112527+00:00
-- url     : https://prove2.me/submissions/afad9c02-30f8-49f9-a31a-e37e58ffc092

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_IsIntegralTraceOfPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_MajAtZeroRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_StarMapTraceOfPowEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_CGIntegral
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_GLP_card_ne_zero
import Theorems.Thm_PI_Dv_GLP_isIntegral_trace_of_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open NumberField
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLP
theorem _root_.solution [CharZero K] (T : GoodSet K G) (x : G) :
    IsIntegral ℤ (((Fintype.card G : ℕ) : K) * cG T x) := by
  have h : ((Fintype.card G : ℕ) : K) * cG T x =
      ∑ s, ((Module.finrank K (T.W s) : ℕ) : K) * LinearMap.trace K _ (T.tau s x⁻¹) := by
    rw [cG, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have := card_ne_zero (K := K) (G := G)
    rw [cS]
    field_simp
  rw [h]
  refine IsIntegral.sum _ fun s _ => ?_
  refine IsIntegral.mul ?_ ?_
  · have := (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K ((Module.finrank K (T.W s) : ℕ) : ℤ)))
    simpa using this
  · exact isIntegral_trace_of_pow _ (Fintype.card G) Fintype.card_pos
      (by rw [← map_pow, pow_card_eq_one, map_one])
end PI.Dv.GLP
