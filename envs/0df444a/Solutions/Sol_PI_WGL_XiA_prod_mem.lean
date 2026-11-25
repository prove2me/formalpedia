-- Prove2me | solution 1 for PI.WGL.XiA.prod_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:15:41.4288+00:00
-- url     : https://prove2.me/submissions/076a0363-2e68-4271-a45c-d29a9e88c7a6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
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


section
noncomputable section
namespace PI.WGL.XiA
open Formalism.BasicNotions MvPolynomial
private theorem mul_mem_dualWeyl_complex {N : ℕ} (ν μ : Fin N → ℕ) (f g : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν) (hg : g ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N μ) :
    f * g ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (ν + μ) := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf hg ⊢
  rw [Submodule.mem_inf] at hf hg ⊢
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hf1 hg1 ⊢
    exact hf1.mul hg1
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero] at hf2 hg2 ⊢
    intro l j hlj
    rw [map_mul, map_mul, hf2 l j hlj, hg2 l j hlj]
private theorem one_mem_dualWeyl_complex {N : ℕ} :
    (1 : MvPolynomial (Fin N × Fin N) ℂ) ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N 0 := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact MvPolynomial.isWeightedHomogeneous_one _ _
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero]
    intro l j hlj
    rw [map_one, map_one]
end PI.WGL.XiA
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiA
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiA
theorem _root_.solution {N : ℕ} {ι : Type*} (s : Finset ι) (ν : ι → Fin N → ℕ) (f : ι → MvPolynomial (Fin N × Fin N) ℂ)
    (hf : ∀ i ∈ s, f i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (ν i)) :
    ∏ i ∈ s, f i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (∑ i ∈ s, ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_dualWeyl_complex (N := N)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_dualWeyl_complex _ _ _ _ (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
end PI.WGL.XiA
