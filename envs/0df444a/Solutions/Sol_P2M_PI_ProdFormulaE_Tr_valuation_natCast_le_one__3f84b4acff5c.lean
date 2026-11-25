-- Prove2me | solution 1 for P2M_PI_ProdFormulaE_Tr_valuation_natCast_le_one__3f84b4acff5c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:47:20.774797+00:00
-- url     : https://prove2.me/submissions/c1ef33d1-abce-4dce-9d54-ee696114ed30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ExistsEqEllMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_InjectiveOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}
namespace PI.ProdFormulaE.Tr
theorem _root_.solution {K : Type*} [Field K] [ValuativeRel K] (n : ℕ) :
    valuation K (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact Valuation.map_add_le _ ih (by simp)
end PI.ProdFormulaE.Tr
