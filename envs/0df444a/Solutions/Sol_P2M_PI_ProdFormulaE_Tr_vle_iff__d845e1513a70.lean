-- Prove2me | solution 1 for P2M_PI_ProdFormulaE_Tr_vle_iff__d845e1513a70
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:27.737442+00:00
-- url     : https://prove2.me/submissions/54858b34-07fe-4bfc-a866-0ab3e42fb115

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
theorem _root_.solution {K : Type*} [Field K] [ValuativeRel K] (x y : K) :
    x ≤ᵥ y ↔ valuation K x ≤ valuation K y := by
  exact (Valuation.Compatible.vle_iff_le (v := valuation K) x y)
end PI.ProdFormulaE.Tr
