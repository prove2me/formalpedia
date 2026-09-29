-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_fuchsianGroup_smul_eq_of_smul_eq_qmPeriodLattice_of_forall_mem_imp_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2eb00449-2e3d-59ba-b22c-4cce484cb123

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_forall_mem_imp_mem_iff_exists_levelModule_qmPeriodLattice_eq
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_levelModule_unique
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_smul_qmPeriodLattice_pair_eq_iff_exists_fuchsianGroup_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_fuchsianGroup_smul_eq_of_smul_eq_qmPeriodLattice_of_forall_mem_imp_mem
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

namespace PeriodUniqP7

theorem relIndex_smul {L M : Submodule ℤ (Fin 2 → ℂ)} {c : ℂ} (hc : c ≠ 0) :
    (c • L).toAddSubgroup.relIndex (c • M).toAddSubgroup = L.toAddSubgroup.relIndex M.toAddSubgroup := by
  rw [Submodule.pointwise_smul_toAddSubgroup, Submodule.pointwise_smul_toAddSubgroup, AddSubgroup.pointwise_smul_def,
    AddSubgroup.pointwise_smul_def]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (smul_right_injective (Fin 2 → ℂ) hc)

end PeriodUniqP7

open PeriodUniqP7 in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (L M : Submodule ℤ (Fin 2 → ℂ))
    (hLM : L ≤ M) (hMN : ∀ v ∈ M, ((N : ℤ) • v) ∈ L)
    (hMstab : ∀ x ∈ Λ, ∀ v ∈ M, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ M)
    (hidx : L.toAddSubgroup.relIndex M.toAddSubgroup = N ^ 2)
    (τ₁ τ₂ : UpperHalfPlane) (c₁ c₂ : ℂ) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hL₁ : c₁ • L = qmPeriodLattice ι Λ τ₁) (hL₂ : c₂ • L = qmPeriodLattice ι Λ τ₂)
    (hlev₁ : (∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
        ((N : ℂ)⁻¹) • qmPeriodMap ι τ₁ lam ∈ c₁ • M → ((N : ℂ)⁻¹) • qmPeriodMap ι τ₁ (lam * r) ∈ c₁ • M))
    (hlev₂ : (∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
        ((N : ℂ)⁻¹) • qmPeriodMap ι τ₂ lam ∈ c₂ • M → ((N : ℂ)⁻¹) • qmPeriodMap ι τ₂ (lam * r) ∈ c₂ • M)) :
    ∃ γ ∈ fuchsianGroup R ι, γ • τ₁ = τ₂ := by
  classical

  have hdata : ∀ (τ : UpperHalfPlane) (c : ℂ), c ≠ 0 → c • L = qmPeriodLattice ι Λ τ →
      qmPeriodLattice ι Λ τ ≤ c • M ∧ (∀ v ∈ c • M, ((N : ℤ) • v) ∈ qmPeriodLattice ι Λ τ) ∧
      (∀ x ∈ Λ, ∀ v ∈ c • M, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ c • M) ∧
      (qmPeriodLattice ι Λ τ).toAddSubgroup.relIndex (c • M).toAddSubgroup = N ^ 2 := by
    intro τ c hc hL
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hL]
      intro v hv
      rw [Submodule.mem_smul_pointwise_iff_exists] at hv ⊢
      obtain ⟨l, hl, rfl⟩ := hv
      exact ⟨l, hLM hl, rfl⟩
    · intro v hv
      rw [Submodule.mem_smul_pointwise_iff_exists] at hv
      obtain ⟨mm, hmm, rfl⟩ := hv
      rw [← hL, smul_comm, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨_, hMN mm hmm, rfl⟩
    · intro x hx v hv
      rw [Submodule.mem_smul_pointwise_iff_exists] at hv ⊢
      obtain ⟨mm, hmm, rfl⟩ := hv
      exact ⟨_, hMstab x hx mm hmm, (Matrix.mulVec_smul _ _ _).symm⟩
    · rw [← hL, relIndex_smul hc, hidx]
  obtain ⟨hLM₁, hMN₁, hMstab₁, hidx₁⟩ := hdata τ₁ c₁ hc₁ hL₁
  obtain ⟨hLM₂, hMN₂, hMstab₂, hidx₂⟩ := hdata τ₂ c₂ hc₂ hL₂
  obtain ⟨J₁, hJ₁, hM₁⟩ := (QuaternionAlgebra.IsEichlerOrder.forall_mem_imp_mem_iff_exists_levelModule_qmPeriodLattice_eq hqN hq'N hqq'
    hB Λ hΛ hN R hR hRΛ ι hι τ₁ (c₁ • M) hLM₁ hMN₁ hMstab₁ hidx₁).1 hlev₁
  obtain ⟨J₂, hJ₂, hM₂⟩ := (QuaternionAlgebra.IsEichlerOrder.forall_mem_imp_mem_iff_exists_levelModule_qmPeriodLattice_eq hqN hq'N hqq'
    hB Λ hΛ hN R hR hRΛ ι hι τ₂ (c₂ • M) hLM₂ hMN₂ hMstab₂ hidx₂).1 hlev₂
  have hJ : J₁ = J₂ := QuaternionAlgebra.IsEichlerOrder.levelModule_unique hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ ι hι J₁ J₂ hJ₁ hJ₂
  subst hJ
  refine (QuaternionAlgebra.IsEichlerOrder.exists_smul_qmPeriodLattice_pair_eq_iff_exists_fuchsianGroup_smul_eq hqN hq'N hqq' hB Λ hΛ
    hN R hR hRΛ ι hι J₁ hJ₁ τ₁ τ₂).1 ⟨c₂ * c₁⁻¹, mul_ne_zero hc₂ (inv_ne_zero hc₁), ?_, ?_⟩
  · rw [← hL₁, smul_smul, mul_assoc, inv_mul_cancel₀ hc₁, mul_one, hL₂]
  · rw [← hM₁, smul_smul, mul_assoc, inv_mul_cancel₀ hc₁, mul_one, hM₂]

end S_QuaternionAlgebra_IsEichlerOrder_exists_fuchsianGroup_smul_eq_of_smul_eq_qmPeriodLattice_of_forall_mem_imp_mem
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_fuchsianGroup_smul_eq_of_smul_eq_qmPeriodLattice_of_forall_mem_imp_mem (solution)
