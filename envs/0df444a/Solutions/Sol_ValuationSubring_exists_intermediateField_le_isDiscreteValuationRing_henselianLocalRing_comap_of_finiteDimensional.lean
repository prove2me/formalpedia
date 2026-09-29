-- Prove2me | solution 1 for ValuationSubring.exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4c614e8d-0016-5aa1-8271-07c54590cb8d

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_henselianLocalRing_comap_of_forall_comap_eq_imp_eq
import Theorems.Thm_ValuationSubring_eq_of_comap_eq_of_forall_mem_decompositionSubgroup
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_forall_isSeparable_of_forall_smul_eq
import Theorems.Thm_ValuationSubring_mem_decompositionSubgroup_of_forall_mem_fixedField_inf_separableClosure_imp_eq
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional

set_option autoImplicit false

open scoped Pointwise

universe u

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {Ω : Type u} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) (hAtop : A ≠ ⊤)
    (K' : IntermediateField K Ω) [FiniteDimensional K ↥K'] :
    ∃ Kh : IntermediateField K Ω, K' ≤ Kh ∧
      (∀ σ : Ω ≃ₐ[K] Ω, σ ∈ A.decompositionSubgroup K → (∀ x : Ω, x ∈ K' → σ x = x) →
        ∀ x : Ω, x ∈ Kh → σ x = x) ∧
      IsDiscreteValuationRing ↥(A.comap (algebraMap ↥Kh Ω)) ∧
      HenselianLocalRing ↥(A.comap (algebraMap ↥Kh Ω)) := by
  classical
  let H : Subgroup (Ω ≃ₐ[K] Ω) := A.decompositionSubgroup K ⊓ K'.fixingSubgroup
  let Kh : IntermediateField K Ω := IntermediateField.fixedField H ⊓ (separableClosure ↥K' Ω).restrictScalars K
  have hKh_mem : ∀ x : Ω, x ∈ Kh ↔ (∀ σ ∈ H, σ x = x) ∧ IsSeparable ↥K' x := by
    intro x
    show x ∈ IntermediateField.fixedField H ⊓ (separableClosure ↥K' Ω).restrictScalars K ↔ _
    rw [IntermediateField.mem_inf, IntermediateField.mem_fixedField_iff, IntermediateField.mem_restrictScalars,
      mem_separableClosure_iff]
  have hK'Kh : K' ≤ Kh := by
    intro x hx
    rw [hKh_mem]
    refine ⟨fun σ hσ => (IntermediateField.mem_fixingSubgroup_iff K' σ).mp hσ.2 x hx, ?_⟩
    exact isSeparable_algebraMap (⟨x, hx⟩ : ↥K')

  haveI hAlgK' : IsAlgClosure ↥K' Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed K, isAlgebraic := Algebra.IsAlgebraic.tower_top (K := K) ↥K' }
  haveI hAlgKh : IsAlgClosure ↥Kh Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed K, isAlgebraic := Algebra.IsAlgebraic.tower_top (K := K) ↥Kh }

  have hres : ∀ (L : IntermediateField K Ω) (σ : Ω ≃ₐ[↥L] Ω),
      σ ∈ A.decompositionSubgroup ↥L ↔ σ.restrictScalars K ∈ A.decompositionSubgroup K := by
    intro L σ
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    have : σ.restrictScalars K • A = σ • A := by
      ext x
      rw [ValuationSubring.mem_smul_pointwise_iff_exists, ValuationSubring.mem_smul_pointwise_iff_exists]
      rfl
    rw [this]
  refine ⟨Kh, hK'Kh, ?_, ?_, ?_⟩

  · intro σ hσD hσK' x hx
    exact ((hKh_mem x).mp hx).1 σ ⟨hσD, (IntermediateField.mem_fixingSubgroup_iff K' σ).mpr hσK'⟩

  ·
    letI : Algebra R ↥K' := ((algebraMap K ↥K').comp (algebraMap R K)).toAlgebra
    haveI : IsScalarTower R K ↥K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hAK' : ∀ r : R, algebraMap R ↥K' r ∈ A.comap (algebraMap ↥K' Ω) := by
      intro r
      rw [ValuationSubring.mem_comap]
      show algebraMap ↥K' Ω (algebraMap K ↥K' (algebraMap R K r)) ∈ A
      rw [← IsScalarTower.algebraMap_apply]
      exact hA r
    have htop' : A.comap (algebraMap ↥K' Ω) ≠ ⊤ := by
      intro htop
      apply hAtop
      have hK'A : ∀ y : ↥K', algebraMap ↥K' Ω y ∈ A := fun y => by
        have : y ∈ A.comap (algebraMap ↥K' Ω) := by rw [htop]; exact ValuationSubring.mem_top y
        exact ValuationSubring.mem_comap.mp this
      ext x
      refine ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
      have hint : IsIntegral ↥K' x := (Algebra.IsAlgebraic.isAlgebraic (R := ↥K') x).isIntegral
      let φ : ↥K' →+* ↥A := (algebraMap ↥K' Ω).codRestrict A.toSubring hK'A
      have hint' : IsIntegral ↥A x := hint.map_of_comp_eq φ (RingHom.id Ω) (by ext y; rfl)
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := Ω)).mp hint'
      rw [← hy]; exact y.2
    have hdvr' : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥K' Ω)) :=
      ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite (A := R) (K := K) (L := ↥K')
        (A.comap (algebraMap ↥K' Ω)) hAK' htop'

    have hsep : ∀ x : Ω, x ∈ IntermediateField.extendScalars hK'Kh → IsSeparable ↥K' x := fun x hx =>
      ((hKh_mem x).mp ((IntermediateField.mem_extendScalars _).mp hx)).2
    have hfix : ∀ σ : Ω ≃ₐ[↥K'] Ω, σ ∈ A.decompositionSubgroup ↥K' →
        ∀ x : Ω, x ∈ IntermediateField.extendScalars hK'Kh → σ x = x := by
      intro σ hσ x hx
      have hσ' : σ.restrictScalars K ∈ H := by
        refine ⟨(hres K' σ).mp hσ, (IntermediateField.mem_fixingSubgroup_iff K' _).mpr (fun y hy => ?_)⟩
        show σ y = y
        exact σ.commutes (⟨y, hy⟩ : ↥K')
      have := ((hKh_mem x).mp ((IntermediateField.mem_extendScalars _).mp hx)).1 _ hσ'
      exact this
    exact ValuationSubring.isDiscreteValuationRing_comap_of_forall_isSeparable_of_forall_smul_eq (L := ↥K') A hdvr'
      (IntermediateField.extendScalars hK'Kh) hsep hfix

  · refine ValuationSubring.henselianLocalRing_comap_of_forall_comap_eq_imp_eq (K := ↥Kh) A hAtop (fun B hB => ?_)
    refine ValuationSubring.eq_of_comap_eq_of_forall_mem_decompositionSubgroup (L := ↥Kh) A (fun σ => ?_) B hB
    rw [hres Kh σ]
    refine ValuationSubring.mem_decompositionSubgroup_of_forall_mem_fixedField_inf_separableClosure_imp_eq A K'
      (σ.restrictScalars K) (fun x hx => ?_)
    show σ x = x
    exact σ.commutes (⟨x, hx⟩ : ↥Kh)

end S_ValuationSubring_exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional
end P2MW
export P2MW.S_ValuationSubring_exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional (solution)
