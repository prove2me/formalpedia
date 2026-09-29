-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_units_atkinLehner_qmPeriodLattice_levelModule_iff_exists_mem_levelHeckeUSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5395835c-02a0-5fc3-88fa-1b0e2923bab1

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_units_mem_nrd_eq_level_forall_mem_iff_conj_mem
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_exists_mem_levelHeckeUSet_conj_of_dvd
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_levelIdentity_of_not_dvd
import Theorems.Thm_QuaternionAlgebra_forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity
import Theorems.Thm_CerednikDrinfeld_exists_gl_conj_fuchsianGroup_iff_of_forall_mem_iff_conj_mem
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_primeHeckeSet_coe_eq_tmul_one_of_nrd_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_units_atkinLehner_qmPeriodLattice_levelModule_iff_exists_mem_levelHeckeUSet
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J')) :
    ∃ (wN : (ℍ[ℚ, a, b])ˣ) (g : GL (Fin 2) ℝ),

      (g : Matrix (Fin 2) (Fin 2) ℝ) = ι (wN : ℍ[ℚ, a, b]) ∧ 0 < g.det.val ∧

      (∀ x : ℍ[ℚ, a, b], x ∈ R ↔ (wN : ℍ[ℚ, a, b]) * x * ((wN⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R) ∧
      (∀ x : ℍ[ℚ, a, b], nrd ((wN : ℍ[ℚ, a, b]) * x * ((wN⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = nrd x) ∧

      (∀ γ : GL (Fin 2) ℝ, γ ∈ fuchsianGroup R ι ↔ g * γ * g⁻¹ ∈ fuchsianGroup R ι) ∧

      (∀ u : ℍ[ℚ, a, b], IsUnitOf R u → nrd u = 1 →
        ∃ γ : GL (Fin 2) ℝ, γ ∈ fuchsianGroup R ι ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = ι u) ∧

      (∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ q → ℓ ≠ q' → ∀ (τ : UpperHalfPlane) (t : ℍ[ℚ, a, b]), t ∈ R → nrd t = (ℓ : ℚ) →
        ((∀ v : Fin 2 → ℂ, (∃ w ∈ qmPeriodLattice ι J' τ, ∃ y ∈ Λ, (ℓ : ℂ) • w + qmPeriodMap ι τ (y * t) = v) ↔
            ∃ y ∈ J', qmPeriodMap ι τ (y * t) = v) ↔
          ∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
              ((wN : ℍ[ℚ, a, b]) * t * ((wN⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
  classical
  obtain ⟨w, hwR, hwn, hwnorm⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_units_mem_nrd_eq_level_forall_mem_iff_conj_mem hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ
  have hwpos : 0 < nrd (w : ℍ[ℚ, a, b]) := by
    rw [hwn]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨g, hgι, hgdet, hN2, hN3, hnrd⟩ :=
    CerednikDrinfeld.exists_gl_conj_fuchsianGroup_iff_of_forall_mem_iff_conj_mem hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ ι hι w hwpos hwnorm
  refine ⟨w, g, hgι, hgdet, hwnorm, hnrd, hN2, hN3, ?_⟩
  intro ℓ hℓ hℓq hℓq' τ t ht hnt
  rw [QuaternionAlgebra.forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity hB ι hι Λ J' t ℓ τ]
  by_cases hℓN : ℓ ∣ N
  · simp only [if_pos hℓN]
    exact QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_exists_mem_levelHeckeUSet_conj_of_dvd
      hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ J' hJ' w hwR hwn hwnorm ℓ hℓ hℓN t ht hnt
  · simp only [if_neg hℓN]
    constructor
    · intro _
      have hx : (w : ℍ[ℚ, a, b]) * t * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R := (hwnorm t).1 ht
      have hnx : nrd ((w : ℍ[ℚ, a, b]) * t * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = (ℓ : ℚ) := by rw [hnrd, hnt]
      exact QuaternionAlgebra.IsEichlerOrder.exists_mem_primeHeckeSet_coe_eq_tmul_one_of_nrd_eq hB Λ hΛ R hR hRΛ ℓ hℓ _ hx hnx
    · intro _
      exact QuaternionAlgebra.IsEichlerOrder.levelIdentity_of_not_dvd hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ J' hJ' ℓ hℓ hℓN t ht hnt

end S_QuaternionAlgebra_IsEichlerOrder_exists_units_atkinLehner_qmPeriodLattice_levelModule_iff_exists_mem_levelHeckeUSet
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_units_atkinLehner_qmPeriodLattice_levelModule_iff_exists_mem_levelHeckeUSet (solution)
