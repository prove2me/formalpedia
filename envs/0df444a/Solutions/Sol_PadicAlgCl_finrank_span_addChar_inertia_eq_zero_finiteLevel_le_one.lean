-- Prove2me | solution 1 for PadicAlgCl.finrank_span_addChar_inertia_eq_zero_finiteLevel_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8e3b4548-a268-5c14-b388-eb0e8a8fb742

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_finrank_span_addChar_inertia_eq_zero_finiteLevel_le_one
p2m_attr_erase "instance" "instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

namespace S17UnramLine

def kerSubgroup {G : Type} [Group G] {k : Type} [AddGroup k] (ψ : G → k)
    (hadd : ∀ σ τ : G, ψ (σ * τ) = ψ σ + ψ τ) : Subgroup G where
  carrier := {g | ψ g = 0}
  one_mem' := by
    have h := hadd 1 1
    rw [one_mul] at h
    simpa using h
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [hadd, ha, hb, add_zero]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : ψ 1 = 0 := by
      have h := hadd 1 1
      rw [one_mul] at h
      simpa using h
    have h := hadd a⁻¹ a
    rw [inv_mul_cancel, h1, ha, add_zero] at h
    exact h.symm

end S17UnramLine

open S17UnramLine in

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] :
    FiniteDimensional k (Submodule.span k
        {φ : primeLocalGaloisGroup (pPrime p) → k |
          (∀ σ τ : primeLocalGaloisGroup (pPrime p), φ (σ * τ) = φ σ + φ τ) ∧
          (∀ σ : primeLocalGaloisGroup (pPrime p),
            ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → φ σ = 0) ∧
          ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
            ∀ (g s : primeLocalGaloisGroup (pPrime p)),
              primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → φ (g * s) = φ g}) ∧
      Module.finrank k (Submodule.span k
        {φ : primeLocalGaloisGroup (pPrime p) → k |
          (∀ σ τ : primeLocalGaloisGroup (pPrime p), φ (σ * τ) = φ σ + φ τ) ∧
          (∀ σ : primeLocalGaloisGroup (pPrime p),
            ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → φ σ = 0) ∧
          ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
            ∀ (g s : primeLocalGaloisGroup (pPrime p)),
              primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → φ (g * s) = φ g}) ≤ 1 := by
  classical

  set S0 := {φ : primeLocalGaloisGroup (pPrime p) → k |
          (∀ σ τ : primeLocalGaloisGroup (pPrime p), φ (σ * τ) = φ σ + φ τ) ∧
          (∀ σ : primeLocalGaloisGroup (pPrime p),
            ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → φ σ = 0) ∧
          ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
            ∀ (g s : primeLocalGaloisGroup (pPrime p)),
              primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → φ (g * s) = φ g} with hS0
  let G := primeLocalGaloisGroup (pPrime p)
  let r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := primeLocalToGlobal (pPrime p)
  let Iglob : Subgroup G := ((primeLocalPlace (pPrime p)).inertiaSubgroupIn ℚ).comap r

  obtain ⟨σ₀, hσ₀⟩ := ExtCitation.exists_isFrobeniusAt_apply_primeLocalToGlobal (pPrime p)

  let T : Submodule k (G → k) :=
    { carrier := {ψ | (∀ σ τ : G, ψ (σ * τ) = ψ σ + ψ τ) ∧ (∀ g ∈ Iglob, ψ g = 0) ∧
        ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : G, r s ∈ F.fixingSubgroup → ψ s = 0}
      add_mem' := by
        rintro ψ₁ ψ₂ ⟨ha₁, hI₁, F₁, hF₁, hl₁⟩ ⟨ha₂, hI₂, F₂, hF₂, hl₂⟩
        haveI := hF₁; haveI := hF₂
        refine ⟨fun σ τ => ?_, fun g hg => ?_, F₁ ⊔ F₂, inferInstance, fun s hs => ?_⟩
        · simp only [Pi.add_apply, ha₁, ha₂]; abel
        · simp only [Pi.add_apply, hI₁ g hg, hI₂ g hg, add_zero]
        · simp only [Pi.add_apply]
          rw [hl₁ s (IntermediateField.fixingSubgroup_le le_sup_left hs),
            hl₂ s (IntermediateField.fixingSubgroup_le le_sup_right hs), add_zero]
      zero_mem' := by
        refine ⟨fun σ τ => by simp, fun g _ => rfl, ⊥, inferInstance, fun s _ => rfl⟩
      smul_mem' := by
        rintro a ψ ⟨ha, hI, F, hF, hl⟩
        refine ⟨fun σ τ => ?_, fun g hg => ?_, F, hF, fun s hs => ?_⟩
        · simp only [Pi.smul_apply, ha, smul_add]
        · simp only [Pi.smul_apply, hI g hg, smul_zero]
        · simp only [Pi.smul_apply, hl s hs, smul_zero] }

  have hS0T : S0 ⊆ (T : Set (G → k)) := by
    rintro φ ⟨hadd, hI, F, hF, hlev⟩
    have h1 : φ 1 = 0 := by
      have h := hadd 1 1
      rw [one_mul] at h
      simpa using h
    refine ⟨hadd, ?_, F, hF, ?_⟩
    · intro g hg
      obtain ⟨τ, hτ, hτg⟩ :=
        ValuationSubring.exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq p (r g) hg
      let τ' : G := τ
      have hfix : r (τ'⁻¹ * g) ∈ F.fixingSubgroup := by
        have : r (τ'⁻¹ * g) = 1 := by
          rw [map_mul, map_inv]
          have hτg' : r τ' = r g := hτg
          rw [hτg', inv_mul_cancel]
        rw [this]; exact one_mem _
      have h2 := hlev τ' (τ'⁻¹ * g) hfix
      rw [mul_inv_cancel_left] at h2
      rw [h2]
      exact hI τ' hτ
    · intro s hs
      have h2 := hlev 1 s hs
      rw [one_mul] at h2
      rw [h2, h1]
  have hST : Submodule.span k S0 ≤ T := Submodule.span_le.mpr hS0T

  have hkey : ∀ ψ ∈ T, ψ σ₀ = 0 → ψ = 0 := by
    rintro ψ ⟨hadd, hI, F, hF, hlev⟩ h0
    haveI := hF
    have h1 : ψ 1 = 0 := by
      have h := hadd 1 1
      rw [one_mul] at h
      simpa using h
    have hpow : ∀ m : ℕ, ψ (σ₀ ^ m) = 0 := by
      intro m
      induction m with
      | zero => simpa using h1
      | succ m ih => rw [pow_succ, hadd, ih, h0, add_zero]
    have hsup : Iglob ⊔ (F.fixingSubgroup).comap r ≤ kerSubgroup ψ hadd :=
      sup_le (fun g hg => hI g hg) (fun g hg => hlev g hg)
    funext g
    obtain ⟨n, hn⟩ :=
      ExtCitation.exists_frobenius_pow_inv_mul_mem_inertia_sup_level (pPrime p) σ₀ hσ₀ F g
    have h2 : ψ ((σ₀ ^ n)⁻¹ * g) = 0 := hsup hn
    have h3 : ψ g = ψ (σ₀ ^ n) + ψ ((σ₀ ^ n)⁻¹ * g) := by rw [← hadd, mul_inv_cancel_left]
    rw [h3, hpow, h2, add_zero]
    rfl

  let ev : Submodule.span k S0 →ₗ[k] k := (LinearMap.proj σ₀).comp (Submodule.span k S0).subtype
  have hinj : Function.Injective ev := by
    intro x y hxy
    have hx : (x : G → k) - (y : G → k) ∈ T := T.sub_mem (hST x.2) (hST y.2)
    have h0 : ((x : G → k) - (y : G → k)) σ₀ = 0 := by
      simp only [Pi.sub_apply]
      exact sub_eq_zero.mpr hxy
    have := hkey _ hx h0
    exact Subtype.ext (sub_eq_zero.mp this)
  refine ⟨Module.Finite.of_injective ev hinj, ?_⟩
  calc Module.finrank k (Submodule.span k S0)
      ≤ Module.finrank k k := LinearMap.finrank_le_finrank_of_injective hinj
    _ = 1 := Module.finrank_self k

#print axioms solution

end S_PadicAlgCl_finrank_span_addChar_inertia_eq_zero_finiteLevel_le_one
end P2MW
export P2MW.S_PadicAlgCl_finrank_span_addChar_inertia_eq_zero_finiteLevel_le_one (solution)
