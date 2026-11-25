-- Prove2me | solution 1 for PI.WGL.LTE.prod_memZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:11:09.467297+00:00
-- url     : https://prove2.me/submissions/d2df0113-e5ed-471c-8ee1-bb1979d883c4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
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
namespace PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD
private theorem mul_mem_dualWeyl_int {N : ℕ} {ν ν' : Fin N → ℕ} {f g : MvPolynomial (Fin N × Fin N) ℤ}
    (hf : f ∈ dualWeyl ℤ N N ν) (hg : g ∈ dualWeyl ℤ N N ν') : f * g ∈ dualWeyl ℤ N N (ν + ν') := by
  unfold dualWeyl at hf hg ⊢
  rw [Submodule.mem_inf] at hf hg ⊢
  refine ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule] at hf hg ⊢
    exact hf.1.mul hg.1
  · have h1 := hf.2
    have h2 := hg.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero] at h1 h2 ⊢
    intro l j hlj
    rw [map_mul, map_mul, h1 l j hlj, h2 l j hlj]
private theorem one_mem_dualWeyl_int {N : ℕ} : (1 : MvPolynomial (Fin N × Fin N) ℤ) ∈ dualWeyl ℤ N N 0 := by
  unfold dualWeyl
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_one ℤ _
  · simp [Submodule.mem_iInf, LinearMap.mem_ker]
end PI.WGL.LTE
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD
namespace PI.WGL.LTE
theorem _root_.solution {N : ℕ} {ι : Type*} (s : Finset ι) (ν : ι → Fin N → ℕ) (f : ι → MvPolynomial (Fin N × Fin N) ℤ)
    (hf : ∀ i ∈ s, f i ∈ dualWeyl ℤ N N (ν i)) :
    ∏ i ∈ s, f i ∈ dualWeyl ℤ N N (∑ i ∈ s, ν i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using (one_mem_dualWeyl_int (N := N))
  · intro a s ha ih hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_dualWeyl_int (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
end PI.WGL.LTE
