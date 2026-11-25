-- Prove2me | solution 1 for PI.WGB.GoodB_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:24.177718+00:00
-- url     : https://prove2.me/submissions/952049fc-9d08-46cb-881d-fb235c181262

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Theorems.Thm_PI_WGB_GoodB_mul
import Theorems.Thm_PI_WGB_GoodB_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
variable {σ : Type*} (R : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (ψ : σ → ℕ)
namespace PI.WGB
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ) (d : ι → ℕ)
    (h : ∀ i ∈ s, GoodB R ψ (f i) (d i)) : GoodB R ψ (∏ i ∈ s, f i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GoodB_one R ψ
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact GoodB_mul R ψ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end PI.WGB
