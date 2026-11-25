-- Prove2me | solution 1 for PI.ZuckTensorWork.isWtOn_sigC_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:42.91713+00:00
-- url     : https://prove2.me/submissions/4f25582e-ef11-42eb-8b2e-af6e6313e6be

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_revM_diagonal
import Theorems.Thm_PI_ZuckTensorWork_revM_mem_Kset_iff
import Theorems.Thm_PI_ZuckTensorWork_revM_mem_Kset
import Theorems.Thm_PI_ZuckTensorWork_Cj_mk_smul
import Theorems.Thm_PI_ZuckTensorWork_sigC_mk
import Theorems.Thm_PI_ZuckTensorWork_Cj_mk_un
import Theorems.Thm_PI_ZuckTensorWork_Cj_un_mk
import Theorems.Thm_PI_ZuckTensorWork_Cj_un_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.ZuckTensorWork.Cj.mk_un
attribute [local simp] PI.ZuckTensorWork.Cj.un_mk


section
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
section Mat
variable {n : ℕ}
end Mat
section Conj
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {n : ℕ}
end Conj
section Wt
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ} {ε : Fin n → Bool}
private theorem conjRep_conj_expI (r : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((r : ℂ) * Complex.I)) = Complex.exp (((-r : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring_nf
private theorem conjRep_sum_revP (μ θ : Fin n → ℝ) :
    ∑ a, revP μ a * θ a = -(∑ a, μ a * θ (Fin.rev a)) := by
  rw [← Finset.sum_neg_distrib,
    ← Equiv.sum_comp (Fin.revPerm : Fin n ≃ Fin n) (fun a => -(μ a * θ (Fin.rev a)))]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [revP, Fin.revPerm_apply]
end Wt
end PI.ZuckTensorWork
end
end

set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ} {ε : Fin n → Bool}
namespace PI.ZuckTensorWork
theorem _root_.solution (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (μ : Fin n → ℝ) (v : H) :
    IsWtOn (Kset ε) σ μ v ↔ IsWtOn (Kset (revE ε)) (sigC σ) (revP μ) (Cj.mk v) := by
  constructor
  · intro h θ hθ
    have hD : revM (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) =
        diagonal fun a => Complex.exp (((θ ∘ Fin.rev) a : ℂ) * Complex.I) := by
      rw [revM_diagonal]; rfl
    have hK := revM_mem_Kset hθ
    rw [hD] at hK
    have h1 := h (θ ∘ Fin.rev) hK
    rw [sigC_mk, hD, h1, Cj.mk_smul, conjRep_conj_expI, conjRep_sum_revP]
    rfl
  · intro h θ hθ
    have hD : revM (diagonal fun a => Complex.exp (((θ ∘ Fin.rev) a : ℂ) * Complex.I)) =
        diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := by
      rw [revM_diagonal]; congr 1; funext a; simp [Fin.rev_rev]
    have hK : (diagonal fun a => Complex.exp (((θ ∘ Fin.rev) a : ℂ) * Complex.I)) ∈ Kset (revE ε) := by
      rw [← revM_mem_Kset_iff, hD]; exact hθ
    have h1 := h (θ ∘ Fin.rev) hK
    rw [sigC_mk, hD] at h1
    have h2 := congrArg Cj.un h1
    rw [Cj.un_smul, Cj.un_mk, Cj.un_mk] at h2
    rw [h2, conjRep_conj_expI, conjRep_sum_revP]
    have e : -(-(∑ a, μ a * (θ ∘ Fin.rev) (Fin.rev a))) = ∑ a, μ a * θ a := by simp [Fin.rev_rev]
    rw [e]
end PI.ZuckTensorWork
