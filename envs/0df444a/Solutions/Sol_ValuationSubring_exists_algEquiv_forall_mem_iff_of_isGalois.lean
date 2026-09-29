-- Prove2me | solution 1 for ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/dc827301-d4f6-5b3d-9f7e-0ec854895649

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Ideal.Pointwise
import Theorems.Thm_ValuationSubring_exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure
import Theorems.Thm_ValuationSubring_mem_iff_exists_integralClosure_valuation_eq_one_mul_eq_of_isAlgebraic
import Definitions.Def_P2M_Util
import Mathlib.RingTheory.Invariant.Galois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois

set_option autoImplicit false

noncomputable section

namespace EsbCapG3

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

def centerQ : Ideal ↥(integralClosure (↥O) F) :=
  (IsLocalRing.maximalIdeal ↥O').comap (inclBtoO' O O' hO)

theorem mem_centerQ_iff (b : integralClosure (↥O) F) :
    b ∈ centerQ O O' hO ↔ O'.valuation (b : F) < 1 :=
  ValuationSubring.valuation_lt_one_iff O' _

scoped instance centerQ_isPrime : (centerQ O O' hO).IsPrime :=
  Ideal.IsPrime.comap (inclBtoO' O O' hO)

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

omit [FiniteDimensional E F] in
theorem smul_eq_of_center_eq (O'' : ValuationSubring F)
    (hO'' : ∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) (σ : Gal(F/E))
    (hσ : centerQ O O'' hO'' = σ • centerQ O O' hO) : σ • O' = O'' := by
  refine (ValuationSubring.mem_iff_exists_integralClosure_valuation_eq_one_mul_eq_of_isAlgebraic
    O O'' hO'').2 (σ • O') (smul_O'_over O O' hO σ) ?_
  intro b
  rw [← mem_centerQ_iff O O'' hO'', val_smul_lt_one_iff O O' hO σ b, hσ,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem]

end galois

end center

end EsbCapG3
p2m_reactivate "P2MW.S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois.EsbCapG3"

end
p2m_reactivate "P2MW.S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois.EsbCapG3"

open EsbCapG3 IsLocalRing Pointwise in
theorem solution
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    [FiniteDimensional E F]
    [IsGalois E F]
    (O : ValuationSubring E)
    (O' O'' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)
    (hO'' : ∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) :
    ∃ σ : F ≃ₐ[E] F, ∀ x : F, σ x ∈ O'' ↔ x ∈ O' := by
  have hunder : (centerQ O O' hO).under ↥O = (centerQ O O'' hO'').under ↥O := by
    rw [← Ideal.over_def _ (IsLocalRing.maximalIdeal ↥O),
      ← Ideal.over_def _ (IsLocalRing.maximalIdeal ↥O)]
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ↥O ↥(integralClosure (↥O) F)
    Gal(F/E) (centerQ O O' hO) (centerQ O O'' hO'') hunder
  have hOeq : σ • O' = O'' := smul_eq_of_center_eq O O' hO O'' hO'' σ hσ
  exact ⟨σ, fun x => by
    rw [← hOeq, show σ x = σ • x from rfl, ValuationSubring.smul_mem_pointwise_smul_iff]⟩

end S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois
end P2MW
export P2MW.S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois (solution)
