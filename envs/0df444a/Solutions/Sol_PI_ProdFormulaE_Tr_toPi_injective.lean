-- Prove2me | solution 1 for PI.ProdFormulaE.Tr.toPi_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:04.101824+00:00
-- url     : https://prove2.me/submissions/5bc42616-6540-4c82-a40c-e32a8ebe1dfb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ExistsEqEllMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_InjectiveOfLinearIndependent
import Theorems.Thm_PI_ProdFormulaE_Tr_LocFam_linearIndependent
import Theorems.Thm_PI_ProdFormulaE_Tr_LocFam_injective_of_linearIndependent
import Theorems.Thm_PI_ProdFormulaE_Tr_exists_eq_ell_mul
import Theorems.Thm_PI_ProdFormulaE_Tr_exists_int_approx


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
theorem _root_.solution : TrInj := by
  intro F _ _ ℓ _ ι _ D hD
  exact LocFam.injective_of_linearIndependent D
    (LocFam.linearIndependent D hD (exists_eq_ell_mul ℓ) (exists_int_approx ℓ))
end PI.ProdFormulaE.Tr
