-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.omc_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:30:56.939952+00:00
-- url     : https://prove2.me/submissions/47fcef1c-1f2c-4ba6-9960-7c0396be9e22

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_omc_glue_j
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
omit [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.CtrX
theorem _root_.solution {m : ℕ} (j : Fin m) (F : Fin m → Fin n → ℂ) (b : Fin n) (R : {p // p ≠ j} → Fin n) :
    ∏ p, F p (omcGlue j b R p) = F j b * ∏ p : {p // p ≠ j}, F p.1 (R p) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  simp only [omc_glue_j]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  simp [omcGlue, p.2]
end PositivityTheory.Rg.Cz.CtrX
