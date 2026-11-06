-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator.exists_directSemilocal_integral_multiple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:44:09.013361+00:00
-- url     : https://prove2.me/submissions/f78ab0a1-6d20-455b-ad6f-c8e1dc3d8056

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalDenominator
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator
open scoped Polynomial RatFunc nonZeroDivisors
open Submodule.IsPrincipal UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator._p2m_local_instance_ebdac87835_36
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator._p2m_local_instance_ebdac87835_41
open DirectIntegralDifferentialResidue
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) (x : F)
    (hx : ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      GlobalPlace.RegularAt
        (AffinePlace.globalPlace k F (directFactorPlace k F p P)) x) :
    ∃ a : R k, a ∉ p.asIdeal ∧ ∃ b : B k F,
      algebraMap (B k F) F b = algebraMap (R k) F a * x := by
  classical
  let q : R k := generator p.asIdeal
  have hq_prime : Prime q := by
    dsimp only [q]
    exact prime_generator_of_isPrime p.asIdeal p.ne_bot
  obtain ⟨y, hy_ne, hy_integral⟩ :=
    exists_integral_multiples (R k) (RatFunc k) ({x} : Finset F)
  have hyx_integral : IsIntegral (R k) (y • x) :=
    hy_integral x (by simp)
  let b₀ : B k F := IsIntegralClosure.mk' (B k F) (y • x) hyx_integral
  have hb₀ : algebraMap (B k F) F b₀ = y • x :=
    IsIntegralClosure.algebraMap_mk' (B k F) (y • x) hyx_integral
  obtain ⟨a, hya, hq_not_dvd_a⟩ :=
    (FiniteMultiplicity.of_prime_left hq_prime hy_ne).exists_eq_pow_mul_and_not_dvd
  have ha_not_mem : a ∉ p.asIdeal := by
    apply (mem_iff_generator_dvd p.asIdeal).not.mpr
    simpa only [q] using hq_not_dvd_a
  have hpmap : Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot p.ne_bot
  have hax_range : algebraMap (R k) F a * x ∈
      Set.range (algebraMap (B k F) F) := by
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro Q
    by_cases hqQ : algebraMap (R k) (B k F) q ∈ Q.asIdeal
    · have hmap_le :
          Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≤ Q.asIdeal := by
        rw [← Ideal.span_singleton_generator p.asIdeal, Ideal.map_span,
          Set.image_singleton]
        exact Ideal.span_le.2 (Set.singleton_subset_iff.mpr hqQ)
      have hQ_normalized : Q.asIdeal ∈ normalizedFactors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) :=
        (Ideal.mem_normalizedFactors_iff hpmap).2 ⟨Q.isPrime, hmap_le⟩
      have hQ_factor : Q.asIdeal ∈ factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) := by
        simpa only [factors_eq_normalizedFactors] using hQ_normalized
      let P : (factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset :=
        ⟨Q.asIdeal, Multiset.mem_toFinset.mpr hQ_factor⟩
      have hQ_over : Q.asIdeal ∈ p.asIdeal.primesOver (B k F) :=
        (Ideal.mem_primesOver_iff_mem_normalizedFactors
          (B k F) p.ne_bot).2 hQ_normalized
      letI : Q.asIdeal.LiesOver p.asIdeal := hQ_over.2
      have haQ : algebraMap (R k) (B k F) a ∉ Q.asIdeal := by
        intro haQ
        apply ha_not_mem
        exact (Ideal.mem_of_liesOver (P := Q.asIdeal) (p := p.asIdeal) a).mpr haQ
      have ha_val : Q.valuation F (algebraMap (R k) F a) = 1 := by
        have := (Q.valuation_eq_one_iff_notMem
          (K := F) (r := algebraMap (R k) (B k F) a)).2 haQ
        simpa only [IsScalarTower.algebraMap_apply (R k) (B k F) F] using this
      have hP_eq : directFactorPlace k F p P = Q := by
        apply IsDedekindDomain.HeightOneSpectrum.ext
        rfl
      have hxQ : Q.valuation F x ≤ 1 := by
        have hxP := hx P
        change (directFactorPlace k F p P).valuation F x ≤ 1 at hxP
        simpa only [hP_eq] using hxP
      calc
        Q.valuation F (algebraMap (R k) F a * x) =
            Q.valuation F (algebraMap (R k) F a) * Q.valuation F x := by
          rw [(Q.valuation F).map_mul]
        _ = Q.valuation F x := by rw [ha_val, one_mul]
        _ ≤ 1 := hxQ
    · have hq_val : Q.valuation F (algebraMap (R k) F q) = 1 := by
        have := (Q.valuation_eq_one_iff_notMem
          (K := F) (r := algebraMap (R k) (B k F) q)).2 hqQ
        simpa only [IsScalarTower.algebraMap_apply (R k) (B k F) F] using this
      have hyx_val : Q.valuation F (algebraMap (R k) F y * x) ≤ 1 := by
        have hb₀_val : Q.valuation F (algebraMap (B k F) F b₀) ≤ 1 := by
          rw [Q.valuation_of_algebraMap]
          exact Q.intValuation_le_one b₀
        rw [hb₀] at hb₀_val
        simpa only [Algebra.smul_def] using hb₀_val
      have hya_field : algebraMap (R k) F y =
          (algebraMap (R k) F q) ^ multiplicity q y *
            algebraMap (R k) F a := by
        simpa only [map_mul, map_pow] using
          congrArg (algebraMap (R k) F) hya
      calc
        Q.valuation F (algebraMap (R k) F a * x) =
            Q.valuation F
              ((algebraMap (R k) F q) ^ multiplicity q y *
                (algebraMap (R k) F a * x)) := by
          symm
          rw [(Q.valuation F).map_mul, (Q.valuation F).map_pow, hq_val,
            one_pow, one_mul]
        _ = Q.valuation F (algebraMap (R k) F y * x) := by
          apply congrArg (Q.valuation F)
          rw [hya_field]
          ring
        _ ≤ 1 := hyx_val
  rcases hax_range with ⟨b, hb⟩
  exact ⟨a, ha_not_mem, b, hb⟩
end QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator
