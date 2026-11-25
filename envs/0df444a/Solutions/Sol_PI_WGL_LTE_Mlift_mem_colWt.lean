-- Prove2me | solution 1 for PI.WGL.LTE.Mlift_mem_colWt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:34.434577+00:00
-- url     : https://prove2.me/submissions/e505fe9a-7d49-4579-979a-4ddbe21441a7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
import Theorems.Thm_PI_WGL_LTE_prod_memZ
import Theorems.Thm_PI_WGL_LTE_ite_pow_memZ
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
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
private theorem initMinor_mem_dualWeyl_int_initW {N s : ℕ} (I : Fin s → Fin N) (hs : s ≤ N) :
    initMinor ℤ I hs ∈ dualWeyl ℤ N N (initW N s) := by
  have h := bidetMem ℤ N N 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have e1 : bideterminant ℤ (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor ℤ (n := N) I hs := by
    unfold bideterminant
    simp
  have e2 : shapeDeg (n := N) (fun _ : Fin 1 => s) = initW N s := by
    funext t
    unfold shapeDeg initW
    split_ifs with ht <;> simp [ht]
  rw [e1, e2] at h
  exact h
end PI.WGL.LTE
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD
namespace PI.WGL.LTE
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ}
    (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n) :
    Mlift h lam sg sz hsz L I ∈ dualWeyl ℤ N N (colWt h lam sg sz L) := by
  have hlp : ∀ (s : ℕ) (hr : s ≤ N) (hc : s ≤ N), lpMinor ℤ s hr hc ∈ dualWeyl ℤ N N (initW N s) :=
    fun s hr hc => initMinor_mem_dualWeyl_int_initW (Fin.castLE hr) hc
  unfold Mlift colWt
  apply mul_mem_dualWeyl_int
  · unfold C0
    refine prod_memZ Finset.univ _ _ fun i _ => ?_
    exact mul_mem_dualWeyl_int (ite_pow_memZ _ _ (hlp _ _ _) _) (ite_pow_memZ _ _ (initMinor_mem_dualWeyl_int_initW _ _) _)
  · refine prod_memZ Finset.univ _ _ fun k _ => ?_
    split_ifs
    · unfold lif
      exact initMinor_mem_dualWeyl_int_initW _ _
    · unfold unl
      exact initMinor_mem_dualWeyl_int_initW _ _
end PI.WGL.LTE
