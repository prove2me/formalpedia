-- Prove2me | solution 1 for P2M_PI_ProdFormulaE_Tr_LocFam_valuation__F_le_one_d2c007035a50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:47:53.626939+00:00
-- url     : https://prove2.me/submissions/9a7c31d9-f357-44e3-bc52-e61fd73decdd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ExistsEqEllMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_InjectiveOfLinearIndependent
import Theorems.Thm_P2M_PI_ProdFormulaE_Tr_vle_iff__d845e1513a70

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
namespace LocFam
theorem _root_.solution (D : LocFam F ℓ ι) (i : ι) (x : 𝓞 F) :
    valuation (D.K i) (D.ιF i (x : F)) ≤ 1 := by
  have h := (D.val i (x : F) 1).2 (by simpa using (D.P i).valuation_le_one x)
  simpa [vle_iff'] using h
end LocFam
end PI.ProdFormulaE.Tr
