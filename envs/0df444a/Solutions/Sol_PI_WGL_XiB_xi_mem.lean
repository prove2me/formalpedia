-- Prove2me | solution 1 for PI.WGL.XiB.xi_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:41.626866+00:00
-- url     : https://prove2.me/submissions/d80bbea2-e975-49b0-b4a2-8b3a876594c9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Theorems.Thm_PI_WGL_XiB_nu_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_XiA_initMinor_mem
import Theorems.Thm_PI_WGL_XiA_lpMinor_eq
import Theorems.Thm_PI_WGL_XiA_pow_mem
import Theorems.Thm_PI_WGL_XiA_prod_mem
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
namespace PI.WGL.XiB
open Formalism.BasicNotions MvPolynomial
private theorem mul_mem_dualWeyl_complex_add {N : ℕ} (ν μ : Fin N → ℕ) (f g : MvPolynomial (Fin N × Fin N) ℂ)
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
end PI.WGL.XiB
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg) :
    xi ℂ h lam sg ∈ nablaSq ℂ N lam := by
  unfold nablaSq
  have key : lam.natW = ∑ i : Fin n, ((aa h lam sg i).toNat • (fun t : Fin N => if t.1 < i.1 + 1 then 1 else 0) +
      (bb h lam sg i).toNat • (fun t : Fin N => if t.1 < i.1 + 1 then 1 else 0)) := by
    funext t
    rw [← nu_eq h lam sg hI t]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  unfold xi
  rw [key]
  refine XiA.prod_mem Finset.univ _ _ (fun i _ => ?_)
  apply mul_mem_dualWeyl_complex_add
  · apply XiA.pow_mem
    rw [XiA.lpMinor_eq]
    exact XiA.initMinor_mem _ _
  · apply XiA.pow_mem
    exact XiA.initMinor_mem _ _
end PI.WGL.XiB
