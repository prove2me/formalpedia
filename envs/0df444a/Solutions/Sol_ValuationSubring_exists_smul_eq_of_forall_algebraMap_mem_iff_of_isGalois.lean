-- Prove2me | solution 1 for ValuationSubring.exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/7f72249b-3c71-59c5-a342-f11d5deb044e

import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Ideal.Pointwise
import Theorems.Thm_ValuationSubring_exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure
import Theorems.Thm_ValuationSubring_mem_iff_exists_integralClosure_valuation_eq_one_mul_eq_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois

set_option autoImplicit false

noncomputable section

attribute [local instance] Ideal.Quotient.field

namespace ValConjT

open IsLocalRing ValuationSubring Pointwise

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

section galois
variable [FiniteDimensional E F] [IsGalois E F] (O : ValuationSubring E)

noncomputable scoped instance msaGalB : MulSemiringAction Gal(F/E) ↥(integralClosure (↥O) F) :=
  IsIntegralClosure.MulSemiringAction ↥O E F ↥(integralClosure (↥O) F)

omit [FiniteDimensional E F] in
theorem smul_coe (σ : Gal(F/E)) (b : integralClosure (↥O) F) :
    ((σ • b : integralClosure (↥O) F) : F) = σ (b : F) :=
  algebraMap_galRestrict_apply ↥O σ b

scoped instance sccGalOB : SMulCommClass Gal(F/E) ↥O ↥(integralClosure (↥O) F) where
  smul_comm g a b := by
    have key : ∀ c : integralClosure (↥O) F, ((a • c : integralClosure (↥O) F) : F)
        = algebraMap E F (a : E) * (c : F) := fun c => by
      rw [Subalgebra.coe_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply ↥O E F]; rfl
    exact Subtype.ext <| by rw [smul_coe, key, key, smul_coe, map_mul, g.commutes]

scoped instance ifrBF : IsFractionRing ↥(integralClosure (↥O) F) F :=
  integralClosure.isFractionRing_of_finite_extension E F

scoped instance invOBGal : Algebra.IsInvariant ↥O ↥(integralClosure (↥O) F) Gal(F/E) :=
  Algebra.isInvariant_of_isGalois ↥O E F ↥(integralClosure (↥O) F)

end galois

section center
variable (O : ValuationSubring E) (O' : ValuationSubring F)
  (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)

include hO in
theorem val_le_one (b : integralClosure (↥O) F) : O'.valuation (b : F) ≤ 1 := by
  obtain ⟨_, _, h⟩ :=
    (ValuationSubring.exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure
      (F := F) O).1 O' hO
  exact (h b).1

def inclBtoO' : integralClosure (↥O) F →+* ↥O' where
  toFun b := ⟨b.1, (O'.valuation_le_one_iff _).mp (val_le_one O O' hO b)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem inclBtoO'_coe (b : integralClosure (↥O) F) :
    ((inclBtoO' O O' hO b : ↥O') : F) = (b : F) := rfl

def centerQ : Ideal ↥(integralClosure (↥O) F) :=
  (IsLocalRing.maximalIdeal ↥O').comap (inclBtoO' O O' hO)

theorem mem_centerQ_iff (b : integralClosure (↥O) F) :
    b ∈ centerQ O O' hO ↔ O'.valuation (b : F) < 1 :=
  ValuationSubring.valuation_lt_one_iff O' _

scoped instance centerQ_isMaximal : (centerQ O O' hO).IsMaximal := by
  obtain ⟨M, hMmax, hM⟩ :=
    (ValuationSubring.exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure
      (F := F) O).1 O' hO
  have hQM : centerQ O O' hO = M := by
    ext b; rw [mem_centerQ_iff]; exact (hM b).2
  exact hQM ▸ hMmax

include hO in
theorem valO'_lt_one_iff (a : E) :
    O'.valuation (algebraMap E F a) < 1 ↔ O.valuation a < 1 := by
  simp only [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
    ← map_inv₀, hO, FaithfulSMul.algebraMap_eq_zero_iff]

scoped instance centerQ_liesOver :
    (centerQ O O' hO).LiesOver (IsLocalRing.maximalIdeal ↥O) := by
  constructor
  ext a
  rw [Ideal.mem_under, mem_centerQ_iff]
  have hcoe : ((algebraMap ↥O (integralClosure (↥O) F) a : integralClosure (↥O) F) : F)
      = algebraMap E F (a : E) :=
    (IsScalarTower.algebraMap_apply ↥O E F a :)
  rw [hcoe, valO'_lt_one_iff O O' hO]
  exact ValuationSubring.valuation_lt_one_iff O a

section galois
variable [FiniteDimensional E F] [IsGalois E F]

include hO in
omit [FiniteDimensional E F] [IsGalois E F] in
theorem smul_O'_over (σ : Gal(F/E)) : ∀ x : E, algebraMap E F x ∈ σ • O' ↔ x ∈ O := by
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    show (σ⁻¹ : Gal(F/E)) • algebraMap E F x = algebraMap E F x from (σ⁻¹).commutes x]
  exact hO x

omit [FiniteDimensional E F] in
theorem val_smul_lt_one_iff (σ : Gal(F/E)) (b : integralClosure (↥O) F) :
    (σ • O').valuation (b : F) < 1 ↔ σ⁻¹ • b ∈ centerQ O O' hO := by
  rw [mem_centerQ_iff, smul_coe, ← ValuationSubring.mem_nonunits_iff,
    ← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_nonunits_iff_or]
  refine or_congr ?_ (not_congr ?_)
  · exact ⟨fun h => by rw [h, map_zero], fun h => σ⁻¹.injective (by rwa [map_zero])⟩
  · rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      show (σ⁻¹ : Gal(F/E)) • ((↑b : F)⁻¹) = (σ⁻¹ : Gal(F/E)) ((↑b : F)⁻¹) from rfl,
      map_inv₀]

end galois

end center

end ValConjT
p2m_reactivate "P2MW.S_ValuationSubring_exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois.ValConjT"

end
p2m_reactivate "P2MW.S_ValuationSubring_exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois.ValConjT"

open ValConjT IsLocalRing Pointwise in
theorem solution
    {E F : Type*} [Field E] [Field F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F]
    (O₁ O₂ : ValuationSubring F)
    (h : ∀ x : E, algebraMap E F x ∈ O₁ ↔ algebraMap E F x ∈ O₂) :
    ∃ σ : F ≃ₐ[E] F, σ • O₁ = O₂ := by
  classical

  let O : ValuationSubring E := O₁.comap (algebraMap E F)
  have hO₁ : ∀ x : E, algebraMap E F x ∈ O₁ ↔ x ∈ O := fun x => Iff.rfl
  have hO₂ : ∀ x : E, algebraMap E F x ∈ O₂ ↔ x ∈ O := fun x => (h x).symm

  haveI : (centerQ O O₁ hO₁).IsPrime := (centerQ_isMaximal O O₁ hO₁).isPrime
  haveI : (centerQ O O₂ hO₂).IsPrime := (centerQ_isMaximal O O₂ hO₂).isPrime
  have hunder : Ideal.under ↥O (centerQ O O₁ hO₁) = Ideal.under ↥O (centerQ O O₂ hO₂) := by
    rw [← Ideal.LiesOver.over (P := centerQ O O₁ hO₁) (p := IsLocalRing.maximalIdeal ↥O),
      ← Ideal.LiesOver.over (P := centerQ O O₂ hO₂) (p := IsLocalRing.maximalIdeal ↥O)]
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ↥O ↥(integralClosure (↥O) F) Gal(F/E)
    (centerQ O O₁ hO₁) (centerQ O O₂ hO₂) hunder

  refine ⟨σ, ?_⟩
  refine (ValuationSubring.mem_iff_exists_integralClosure_valuation_eq_one_mul_eq_of_isAlgebraic O O₂ hO₂).2
    (σ • O₁) (smul_O'_over O O₁ hO₁ σ) ?_
  intro b
  rw [← mem_centerQ_iff O O₂ hO₂, val_smul_lt_one_iff O O₁ hO₁ σ b, hσ]
  exact Ideal.mem_pointwise_smul_iff_inv_smul_mem (a := σ) (S := centerQ O O₁ hO₁) (x := b)

#print axioms solution

end S_ValuationSubring_exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois
end P2MW
export P2MW.S_ValuationSubring_exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois (solution)
