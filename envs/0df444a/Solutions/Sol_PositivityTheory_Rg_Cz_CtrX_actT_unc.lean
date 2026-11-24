-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.actT_unc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:25.453803+00:00
-- url     : https://prove2.me/submissions/14414aa8-a54b-4625-b3f3-43976dddf0c4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA
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
namespace PositivityTheory.Rg.Cz.CtrX
theorem _root_.solution {ι Γ A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (la : A → ι) (lb : B → ι)
    (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ) (f : TV n (TV n M A) B) :
    actT (Sum.elim la lb) κ ρ γ (unc f) = unc (actT lb κ (actT la κ ρ) γ f) := by
  funext I
  simp only [actT, unc, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, Function.comp_apply, Finset.sum_apply, Pi.smul_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.sumArrowEquivProdArrow A B (Fin n)).trans (Equiv.prodComm _ _)) _ _ (fun d => ?_)
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [mul_comm]
  rfl
end PositivityTheory.Rg.Cz.CtrX
