-- Prove2me | solution 1 for PI.Dv.GLP.star_cG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:05.459587+00:00
-- url     : https://prove2.me/submissions/9778b5cc-e71e-4c5c-b43f-20531725f7a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_IsIntegralTraceOfPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_MajAtZeroRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_StarMapTraceOfPowEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_CGIntegral
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_GLPTr_star_map_trace_rep
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
theorem _root_.solution (σ : K →+* ℂ) (T : GoodSet K G) (g : G) :
    star (σ (cG T g)) = σ (cG T g⁻¹) := by
  simp only [cG, cS, map_sum, map_mul, map_div₀, map_natCast, star_sum, star_mul', star_div₀,
    star_natCast, PI.Dv.GLPTr.star_map_trace_rep, inv_inv]
end PI.Dv.GLP
