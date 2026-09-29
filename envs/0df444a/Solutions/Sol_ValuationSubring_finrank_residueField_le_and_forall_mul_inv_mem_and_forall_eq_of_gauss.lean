-- Prove2me | solution 1 for ValuationSubring.finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8dfdd6cd-f587-5543-a25c-befdc565e4c6

import Mathlib
import Theorems.Thm_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one
import Theorems.Thm_IsDiscreteValuationRing_primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open Polynomial

universe u

namespace DeuringVal

section frame
variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K₀ : Type u} [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    {F : Type u} [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    {j : F} {ϖ : R}

scoped instance isScalarTower_adjoin : IsScalarTower R ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F :=
  IsScalarTower.of_algebraMap_eq (fun r => by
    show algebraMap R F r = ((algebraMap R ↥(IntermediateField.adjoin K₀ ({j} : Set F)) r : ↥(IntermediateField.adjoin K₀ ({j} : Set F))) : F)
    rw [IsScalarTower.algebraMap_apply R K₀ F, IsScalarTower.algebraMap_apply R K₀ ↥(IntermediateField.adjoin K₀ ({j} : Set F))]
    rfl)

theorem isPrime_span_C (hϖ : Prime ϖ) : (Ideal.span {C ϖ} : Ideal R[X]).IsPrime := by
  rw [Ideal.span_singleton_prime (by simpa using hϖ.ne_zero)]
  exact Polynomial.prime_C_iff.2 hϖ

variable (𝔤 : Ideal R[X]) [𝔤.IsPrime]

theorem aeval_ne_zero_of_mem_primeCompl (htj : Transcendental R j) (q : R[X]) (hq : q ∈ 𝔤.primeCompl) :
    aeval j q ≠ 0 := by
  intro h
  have hq0 : q ≠ 0 := fun h0 => hq (h0 ▸ 𝔤.zero_mem)
  exact hq0 (transcendental_iff_injective.1 htj (by rw [h, map_zero]))

omit [𝔤.IsPrime] in
theorem mem_of_C_dvd (h𝔤 : 𝔤 = Ideal.span {C ϖ}) {q : R[X]} (h : C ϖ ∣ q) : q ∈ 𝔤 := by
  rw [h𝔤]; exact Ideal.mem_span_singleton.2 h

omit [𝔤.IsPrime] in
theorem C_dvd_of_mem (h𝔤 : 𝔤 = Ideal.span {C ϖ}) {q : R[X]} (h : q ∈ 𝔤) : C ϖ ∣ q := by
  rw [h𝔤] at h; exact Ideal.mem_span_singleton.1 h

theorem exists_ringHom_adjoin (htj : Transcendental R j) :
    ∃ f : Localization.AtPrime 𝔤 →+* ↥(IntermediateField.adjoin K₀ ({j} : Set F)), ∀ p : R[X], ((f (algebraMap R[X] (Localization.AtPrime 𝔤) p) : ↥(IntermediateField.adjoin K₀ ({j} : Set F))) : F) = aeval j p := by
  let jE : ↥(IntermediateField.adjoin K₀ ({j} : Set F)) := ⟨j, IntermediateField.mem_adjoin_simple_self K₀ j⟩
  let g : R[X] →+* ↥(IntermediateField.adjoin K₀ ({j} : Set F)) := (aeval jE).toRingHom
  have hg : ∀ p : R[X], ((g p : ↥(IntermediateField.adjoin K₀ ({j} : Set F))) : F) = aeval j p := fun p =>
    (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F) jE p).symm
  have hunit : ∀ y : 𝔤.primeCompl, IsUnit (g y) := by
    intro y
    apply Ne.isUnit
    intro h0
    apply aeval_ne_zero_of_mem_primeCompl 𝔤 htj y.1 y.2
    rw [← hg, h0]
    rfl
  refine ⟨IsLocalization.lift (M := 𝔤.primeCompl) hunit, fun p => ?_⟩
  rw [IsLocalization.lift_eq]
  exact hg p

variable [Algebra (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F))] [Algebra (Localization.AtPrime 𝔤) F] [IsScalarTower (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F]

theorem isDiscreteValuationRing (hϖ : Prime ϖ) (h𝔤 : 𝔤 = Ideal.span {C ϖ}) : IsDiscreteValuationRing (Localization.AtPrime 𝔤) := by
  have hC0 : (C ϖ : R[X]) ≠ 0 := fun h => hϖ.ne_zero (C_eq_zero.1 h)
  have hCu : ¬ IsUnit (C ϖ : R[X]) := fun h => hϖ.not_unit (isUnit_C.1 h)
  have hht : 𝔤.height = 1 := by
    rw [h𝔤]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hC0) hCu
  exact Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one 𝔤 hht

theorem algebraMap_R_B (r : R) : algebraMap R (Localization.AtPrime 𝔤) r = algebraMap R[X] (Localization.AtPrime 𝔤) (C r) := by
  rw [IsScalarTower.algebraMap_apply R R[X] (Localization.AtPrime 𝔤), Polynomial.algebraMap_eq]

theorem maximalIdeal_eq (hϖ : Prime ϖ) (h𝔤 : 𝔤 = Ideal.span {C ϖ}) :
    IsLocalRing.maximalIdeal (Localization.AtPrime 𝔤) = Ideal.span {algebraMap R (Localization.AtPrime 𝔤) ϖ} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal,
    congrArg (Ideal.map (algebraMap R[X] (Localization.AtPrime 𝔤))) h𝔤, Ideal.map_span, Set.image_singleton, ← algebraMap_R_B 𝔤]

theorem irreducible_algebraMap (hϖ : Prime ϖ) (h𝔤 : 𝔤 = Ideal.span {C ϖ}) : Irreducible (algebraMap R (Localization.AtPrime 𝔤) ϖ) := by
  haveI := isDiscreteValuationRing 𝔤 hϖ h𝔤
  refine IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ ?_ (maximalIdeal_eq 𝔤 hϖ h𝔤)
  rw [algebraMap_R_B, map_ne_zero_iff _ (IsLocalization.injective (Localization.AtPrime 𝔤) 𝔤.primeCompl_le_nonZeroDivisors)]
  exact fun h => hϖ.ne_zero (C_eq_zero.1 h)

theorem algebraMap_R_B_F (hcompat : ∀ p : R[X], algebraMap (Localization.AtPrime 𝔤) F (algebraMap R[X] (Localization.AtPrime 𝔤) p) = aeval j p) (r : R) :
    algebraMap (Localization.AtPrime 𝔤) F (algebraMap R (Localization.AtPrime 𝔤) r) = algebraMap R F r := by
  rw [algebraMap_R_B, hcompat, aeval_C]

theorem exists_eq_aeval_div (hcompat : ∀ p : R[X], algebraMap (Localization.AtPrime 𝔤) F (algebraMap R[X] (Localization.AtPrime 𝔤) p) = aeval j p)
    (htj : Transcendental R j) (b : Localization.AtPrime 𝔤) :
    ∃ P : R[X], ∃ Q ∈ 𝔤.primeCompl, algebraMap (Localization.AtPrime 𝔤) F b = aeval j P / aeval j Q ∧ aeval j Q ≠ 0 := by
  obtain ⟨⟨P, Q⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔤.primeCompl b
  refine ⟨P, Q, Q.2, ?_, aeval_ne_zero_of_mem_primeCompl 𝔤 htj Q Q.2⟩
  rw [eq_div_iff (aeval_ne_zero_of_mem_primeCompl 𝔤 htj Q Q.2), ← hcompat, ← hcompat, ← map_mul, IsLocalization.mk'_spec]

theorem algebraMap_mem_of_gaussType (hcompat : ∀ p : R[X], algebraMap (Localization.AtPrime 𝔤) F (algebraMap R[X] (Localization.AtPrime 𝔤) p) = aeval j p)
    (htj : Transcendental R j) (hϖ : Prime ϖ) (h𝔤 : 𝔤 = Ideal.span {C ϖ})
    (V' : ValuationSubring F) (hRV' : ∀ r : R, algebraMap R F r ∈ V')
    (hjV' : ∀ P : R[X], ¬ (C ϖ ∣ P) → aeval j P ∈ V' ∧ (aeval j P)⁻¹ ∈ V') (b : Localization.AtPrime 𝔤) :
    algebraMap (Localization.AtPrime 𝔤) F b ∈ V' := by

  have hX : ¬ C ϖ ∣ (X : R[X]) := by
    intro hd
    rw [C_dvd_iff_dvd_coeff] at hd
    have := hd 1
    rw [coeff_X_one] at this
    exact hϖ.not_unit (isUnit_of_dvd_one this)
  have hjm : j ∈ V' := by simpa using (hjV' X hX).1
  have hPV : ∀ P : R[X], aeval j P ∈ V' := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a =>
        rw [aeval_monomial]
        exact mul_mem (hRV' a) (pow_mem hjm n)
  obtain ⟨P, Q, hQ, hb, hQ0⟩ := exists_eq_aeval_div 𝔤 hcompat htj b
  have hQ' : ¬ C ϖ ∣ Q := fun hd => hQ (mem_of_C_dvd 𝔤 h𝔤 hd)
  rw [hb, div_eq_mul_inv]
  exact mul_mem (hPV P) (hjV' Q hQ').2

theorem algebraMap_mem_nonunits_of_mem_maximalIdeal
    (hcompat : ∀ p : R[X], algebraMap (Localization.AtPrime 𝔤) F (algebraMap R[X] (Localization.AtPrime 𝔤) p) = aeval j p)
    (htj : Transcendental R j) (hϖ : Prime ϖ) (h𝔤 : 𝔤 = Ideal.span {C ϖ})
    (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V) (hϖV : algebraMap R F ϖ ∈ V.nonunits)
    (hjV : ∀ P : R[X], ¬ (C ϖ ∣ P) → aeval j P ∈ V ∧ (aeval j P)⁻¹ ∈ V)
    (b : Localization.AtPrime 𝔤) (hb : b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔤)) : algebraMap (Localization.AtPrime 𝔤) F b ∈ V.nonunits := by
  rw [maximalIdeal_eq 𝔤 hϖ h𝔤, Ideal.mem_span_singleton'] at hb
  obtain ⟨c, rfl⟩ := hb
  rw [map_mul, algebraMap_R_B_F 𝔤 hcompat]
  have hc : algebraMap (Localization.AtPrime 𝔤) F c ∈ V := algebraMap_mem_of_gaussType 𝔤 hcompat htj hϖ h𝔤 V hRV hjV c
  have hclt := (V.valuation_le_one_iff _).2 hc
  rw [ValuationSubring.mem_nonunits_iff] at hϖV ⊢
  rw [map_mul]
  exact lt_of_le_of_lt (by simpa only [one_mul] using mul_le_mul_left hclt (V.valuation (algebraMap R F ϖ))) hϖV

theorem isFractionRing (hcompat : ∀ p : R[X], algebraMap (Localization.AtPrime 𝔤) F (algebraMap R[X] (Localization.AtPrime 𝔤) p) = aeval j p)
    (htj : Transcendental R j) : IsFractionRing (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) := by
  classical

  letI algXE : Algebra R[X] ↥(IntermediateField.adjoin K₀ ({j} : Set F)) := ((algebraMap (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F))).comp (algebraMap R[X] (Localization.AtPrime 𝔤))).toAlgebra
  haveI : IsScalarTower R[X] (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hval : ∀ p : R[X], ((algebraMap R[X] ↥(IntermediateField.adjoin K₀ ({j} : Set F)) p : ↥(IntermediateField.adjoin K₀ ({j} : Set F))) : F) = aeval j p := by
    intro p
    change ((algebraMap (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) (algebraMap R[X] (Localization.AtPrime 𝔤) p) : ↥(IntermediateField.adjoin K₀ ({j} : Set F))) : F) = aeval j p
    rw [← hcompat p, IsScalarTower.algebraMap_apply (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F]
    rfl
  have hinj : Function.Injective (algebraMap R[X] ↥(IntermediateField.adjoin K₀ ({j} : Set F))) := by
    intro p q h
    apply transcendental_iff_injective.1 htj
    rw [← hval, ← hval, h]
  have hRinj : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)

  have haevNorm : ∀ p : K₀[X], ∃ b ∈ nonZeroDivisors R,
      aeval j (IsLocalization.integerNormalization (nonZeroDivisors R) p) = algebraMap R F b * aeval j p := by
    intro p
    obtain ⟨b, hb, hbp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
    refine ⟨b, hb, ?_⟩
    rw [← Polynomial.aeval_map_algebraMap K₀ j (IsLocalization.integerNormalization (nonZeroDivisors R) p), hbp,
      Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply R K₀ K₀[X] b, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply R K₀ F]

  haveI hXE : IsFractionRing R[X] ↥(IntermediateField.adjoin K₀ ({j} : Set F)) := by
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨a, ha⟩
      exact isUnit_iff_ne_zero.mpr fun h0 => (mem_nonZeroDivisors_iff_ne_zero.mp ha) (hinj (h0.trans (map_zero _).symm))
    · intro k
      obtain ⟨r, t, hrt⟩ := (IntermediateField.mem_adjoin_simple_iff K₀ (α := j) (k : F)).mp k.2
      obtain ⟨br, hbr, hbrr⟩ := haevNorm r
      obtain ⟨bt, hbt, hbtt⟩ := haevNorm t
      set r' := IsLocalization.integerNormalization (nonZeroDivisors R) r
      set t' := IsLocalization.integerNormalization (nonZeroDivisors R) t
      by_cases ht0 : aeval j t = 0
      · refine ⟨⟨0, 1⟩, ?_⟩
        have hk0 : k = 0 := Subtype.ext (by rw [hrt, ht0, div_zero]; rfl)
        simp [hk0]
      · have ht'nz : C bt * r' ≠ 0 ∨ True := Or.inr trivial
        have hden : (C br * t' : R[X]) ∈ nonZeroDivisors R[X] := by
          refine mem_nonZeroDivisors_iff_ne_zero.2 (mul_ne_zero ?_ ?_)
          · exact fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hbr) (C_eq_zero.1 h)
          · intro h
            have : aeval j t' = 0 := by rw [h, map_zero]
            rw [hbtt, mul_eq_zero] at this
            rcases this with hc | hc
            · exact (mem_nonZeroDivisors_iff_ne_zero.mp hbt) (hRinj (hc.trans (map_zero _).symm))
            · exact ht0 hc
        refine ⟨⟨C bt * r', ⟨C br * t', hden⟩⟩, ?_⟩
        apply Subtype.ext
        change (k : F) * ((algebraMap R[X] ↥(IntermediateField.adjoin K₀ ({j} : Set F)) (C br * t') : ↥(IntermediateField.adjoin K₀ ({j} : Set F))) : F) = ((algebraMap R[X] ↥(IntermediateField.adjoin K₀ ({j} : Set F)) (C bt * r') : ↥(IntermediateField.adjoin K₀ ({j} : Set F))) : F)
        rw [hval, hval, map_mul, map_mul, aeval_C, aeval_C, hbrr, hbtt, hrt]
        rw [div_mul_eq_mul_div, div_eq_iff ht0]
        ring
    · intro a b hab
      exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; exact hinj hab⟩

  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔤.primeCompl (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F))

section residue

variable (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V)
  (𝔽 : Type u) [Field 𝔽] [Algebra R 𝔽] [Algebra 𝔽 (IsLocalRing.ResidueField ↥V)]
  (hcomp : ∀ r : R, algebraMap 𝔽 (IsLocalRing.ResidueField ↥V) (algebraMap R 𝔽 r) = IsLocalRing.residue ↥V ⟨algebraMap R F r, hRV r⟩)
  (jV : ↥V) (hjV' : (jV : F) = j)

include hRV hjV' in

theorem aeval_mem (P : R[X]) : aeval j P ∈ V := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
      rw [aeval_monomial, ← hjV']
      exact mul_mem (hRV a) (pow_mem jV.2 n)

include hRV hcomp hjV' in

theorem residue_aeval (P : R[X]) (hP : aeval j P ∈ V) :
    IsLocalRing.residue ↥V ⟨aeval j P, hP⟩ = aeval (IsLocalRing.residue ↥V jV) (P.map (algebraMap R 𝔽)) := by
  have key : ∀ P : R[X], IsLocalRing.residue ↥V ⟨aeval j P, aeval_mem V hRV jV hjV' P⟩ =
      aeval (IsLocalRing.residue ↥V jV) (P.map (algebraMap R 𝔽)) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
        have : (⟨aeval j (p + q), aeval_mem V hRV jV hjV' (p + q)⟩ : ↥V) =
            ⟨aeval j p, aeval_mem V hRV jV hjV' p⟩ + ⟨aeval j q, aeval_mem V hRV jV hjV' q⟩ :=
          Subtype.ext (map_add _ _ _)
        rw [this, map_add, hp, hq, Polynomial.map_add, map_add]
    | monomial n a =>
        have : (⟨aeval j (monomial n a), aeval_mem V hRV jV hjV' _⟩ : ↥V) = ⟨algebraMap R F a, hRV a⟩ * jV ^ n := by
          apply Subtype.ext
          simp [aeval_monomial, hjV']
        rw [this, map_mul, map_pow, ← hcomp, Polynomial.map_monomial, aeval_monomial]
  exact key P

variable (hϖV : algebraMap R F ϖ ∈ V.nonunits)
  (hjV : ∀ P : R[X], ¬ (C ϖ ∣ P) → aeval j P ∈ V ∧ (aeval j P)⁻¹ ∈ V)
  (hcompat : ∀ p : R[X], algebraMap (Localization.AtPrime 𝔤) F (algebraMap R[X] (Localization.AtPrime 𝔤) p) = aeval j p)
  (htj : Transcendental R j) (hϖ : Prime ϖ) (h𝔤 : 𝔤 = Ideal.span {C ϖ})
  (hBV : ∀ b : Localization.AtPrime 𝔤, algebraMap (Localization.AtPrime 𝔤) F b ∈ V)

include hRV hcomp hϖV in

theorem algebraMap_ϖ_eq_zero : algebraMap R 𝔽 ϖ = 0 := by
  apply (algebraMap 𝔽 (IsLocalRing.ResidueField ↥V)).injective
  rw [hcomp, map_zero, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  exact hϖV

include hRV hcomp hϖV in

theorem not_C_dvd_of_map_ne_zero (Q : R[X]) (hQ : Q.map (algebraMap R 𝔽) ≠ 0) : ¬ C ϖ ∣ Q := by
  rintro ⟨Q', rfl⟩
  apply hQ
  rw [Polynomial.map_mul, Polynomial.map_C, algebraMap_ϖ_eq_zero V hRV 𝔽 hcomp hϖV, C_0, zero_mul]

include hRV hcomp hjV' hjV htj in

theorem aeval_residue_ne_zero (P : R[X]) (hP : ¬ C ϖ ∣ P) :
    aeval (IsLocalRing.residue ↥V jV) (P.map (algebraMap R 𝔽)) ≠ 0 := by
  rw [← residue_aeval V hRV 𝔽 hcomp jV hjV' P (hjV P hP).1, Ne, IsLocalRing.residue_eq_zero_iff]
  intro hm
  have h0 : aeval j P ≠ 0 := by
    intro h0
    apply hP
    rw [transcendental_iff_injective.1 htj (h0.trans (map_zero _).symm)]
    exact dvd_zero _
  have hu : IsUnit (⟨aeval j P, (hjV P hP).1⟩ : ↥V) :=
    isUnit_iff_exists_inv.2 ⟨⟨(aeval j P)⁻¹, (hjV P hP).2⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  exact (IsLocalRing.mem_maximalIdeal _).1 hm hu

theorem aeval_mem_adjoin (p : 𝔽[X]) :
    aeval (IsLocalRing.residue ↥V jV) p ∈ IntermediateField.adjoin 𝔽 ({IsLocalRing.residue ↥V jV} : Set (IsLocalRing.ResidueField ↥V)) := by
  have h := Polynomial.aeval_algHom_apply
    (IntermediateField.val (IntermediateField.adjoin 𝔽 ({IsLocalRing.residue ↥V jV} : Set (IsLocalRing.ResidueField ↥V))))
    (⟨IsLocalRing.residue ↥V jV, IntermediateField.mem_adjoin_simple_self 𝔽 _⟩ :
      ↥(IntermediateField.adjoin 𝔽 ({IsLocalRing.residue ↥V jV} : Set (IsLocalRing.ResidueField ↥V)))) p
  rw [IntermediateField.val_mk] at h
  rw [h]
  exact Subtype.mem _

include hRV hcomp hjV' hjV hcompat htj h𝔤 in

theorem residue_mk' (P : R[X]) (Q : 𝔤.primeCompl) :
    IsLocalRing.residue ↥V ⟨algebraMap (Localization.AtPrime 𝔤) F (IsLocalization.mk' (Localization.AtPrime 𝔤) P Q), hBV _⟩ =
      aeval (IsLocalRing.residue ↥V jV) (P.map (algebraMap R 𝔽)) *
        (aeval (IsLocalRing.residue ↥V jV) (Q.1.map (algebraMap R 𝔽)))⁻¹ ∧
    aeval (IsLocalRing.residue ↥V jV) (Q.1.map (algebraMap R 𝔽)) ≠ 0 := by
  have hQ : ¬ C ϖ ∣ Q.1 := fun hd => Q.2 (mem_of_C_dvd 𝔤 h𝔤 hd)
  have hQ0 := aeval_ne_zero_of_mem_primeCompl 𝔤 htj Q.1 Q.2
  refine ⟨?_, aeval_residue_ne_zero V hRV 𝔽 hcomp jV hjV' hjV htj Q.1 hQ⟩

  have hval : algebraMap (Localization.AtPrime 𝔤) F (IsLocalization.mk' (Localization.AtPrime 𝔤) P Q) = aeval j P * (aeval j Q.1)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hQ0, ← hcompat, ← hcompat, ← map_mul, IsLocalization.mk'_spec]
  have hfac : (⟨algebraMap (Localization.AtPrime 𝔤) F (IsLocalization.mk' (Localization.AtPrime 𝔤) P Q), hBV _⟩ : ↥V) =
      ⟨aeval j P, (aeval_mem V hRV jV hjV' P)⟩ * ⟨(aeval j Q.1)⁻¹, (hjV Q.1 hQ).2⟩ :=
    Subtype.ext hval
  have hinv : IsLocalRing.residue ↥V ⟨(aeval j Q.1)⁻¹, (hjV Q.1 hQ).2⟩ =
      (IsLocalRing.residue ↥V ⟨aeval j Q.1, (hjV Q.1 hQ).1⟩)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    have : (⟨(aeval j Q.1)⁻¹, (hjV Q.1 hQ).2⟩ : ↥V) * ⟨aeval j Q.1, (hjV Q.1 hQ).1⟩ = 1 :=
      Subtype.ext (inv_mul_cancel₀ hQ0)
    rw [this, map_one]
  rw [hfac, map_mul, hinv, residue_aeval V hRV 𝔽 hcomp jV hjV', residue_aeval V hRV 𝔽 hcomp jV hjV']

include hRV hcomp hjV' hjV hcompat htj h𝔤 in

theorem residue_mem_adjoin (b : Localization.AtPrime 𝔤) :
    IsLocalRing.residue ↥V ⟨algebraMap (Localization.AtPrime 𝔤) F b, hBV b⟩ ∈
      IntermediateField.adjoin 𝔽 ({IsLocalRing.residue ↥V jV} : Set (IsLocalRing.ResidueField ↥V)) := by
  obtain ⟨⟨P, Q⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔤.primeCompl b
  rw [(residue_mk' 𝔤 V hRV 𝔽 hcomp jV hjV' hjV hcompat htj h𝔤 hBV P Q).1]
  exact mul_mem (aeval_mem_adjoin V 𝔽 jV _) (inv_mem (aeval_mem_adjoin V 𝔽 jV _))

include hRV hcomp hjV' hjV hcompat htj h𝔤 hϖV in

theorem exists_residue_eq (h𝔽 : Function.Surjective (algebraMap R 𝔽))
    (z : IsLocalRing.ResidueField ↥V) (hz : z ∈ IntermediateField.adjoin 𝔽 ({IsLocalRing.residue ↥V jV} : Set (IsLocalRing.ResidueField ↥V))) :
    ∃ b : Localization.AtPrime 𝔤, IsLocalRing.residue ↥V ⟨algebraMap (Localization.AtPrime 𝔤) F b, hBV b⟩ = z := by
  obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff 𝔽 (α := IsLocalRing.residue ↥V jV) z).mp hz
  obtain ⟨P, rfl⟩ := Polynomial.map_surjective (algebraMap R 𝔽) h𝔽 p
  obtain ⟨Q, rfl⟩ := Polynomial.map_surjective (algebraMap R 𝔽) h𝔽 q
  by_cases hq : aeval (IsLocalRing.residue ↥V jV) (Q.map (algebraMap R 𝔽)) = 0
  · refine ⟨0, ?_⟩
    have : (⟨algebraMap (Localization.AtPrime 𝔤) F 0, hBV 0⟩ : ↥V) = 0 := Subtype.ext (map_zero _)
    rw [this, map_zero, hpq, hq, div_zero]
  · have hQ : ¬ C ϖ ∣ Q := not_C_dvd_of_map_ne_zero V hRV 𝔽 hcomp hϖV Q (fun h => hq (by rw [h, map_zero]))
    have hQ' : Q ∈ 𝔤.primeCompl := fun hm => hQ (C_dvd_of_mem 𝔤 h𝔤 hm)
    refine ⟨IsLocalization.mk' (Localization.AtPrime 𝔤) P ⟨Q, hQ'⟩, ?_⟩
    rw [(residue_mk' 𝔤 V hRV 𝔽 hcomp jV hjV' hjV hcompat htj h𝔤 hBV P ⟨Q, hQ'⟩).1, hpq, div_eq_mul_inv]

include hRV hcomp hjV' hjV hcompat htj h𝔤 in

theorem mem_maximalIdeal_of_residue_eq_zero (b : Localization.AtPrime 𝔤)
    (hb : IsLocalRing.residue ↥V ⟨algebraMap (Localization.AtPrime 𝔤) F b, hBV b⟩ = 0) : b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔤) := by
  obtain ⟨⟨P, Q⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔤.primeCompl b
  obtain ⟨h1, h2⟩ := residue_mk' 𝔤 V hRV 𝔽 hcomp jV hjV' hjV hcompat htj h𝔤 hBV P Q
  rw [h1, mul_eq_zero, inv_eq_zero, or_iff_left h2] at hb
  have hP : C ϖ ∣ P := by
    by_contra hP
    exact aeval_residue_ne_zero V hRV 𝔽 hcomp jV hjV' hjV htj P hP hb
  rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime 𝔤) 𝔤]
  exact mem_of_C_dvd 𝔤 h𝔤 hP

end residue

section closure

variable (V : ValuationSubring F) (hBV : ∀ b : Localization.AtPrime 𝔤, algebraMap (Localization.AtPrime 𝔤) F b ∈ V)

include hBV in
theorem integralClosure_mem (x : ↥(integralClosure (Localization.AtPrime 𝔤) F)) : (x : F) ∈ V := by
  obtain ⟨p, hpm, hpx⟩ := x.2
  let ψ : Localization.AtPrime 𝔤 →+* ↥V := (algebraMap (Localization.AtPrime 𝔤) F).codRestrict V.toSubring hBV
  have hint : IsIntegral ↥V (x : F) := by
    refine ⟨p.map ψ, hpm.map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpx
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  rw [← hv]
  exact v.2

noncomputable def toV : ↥(integralClosure (Localization.AtPrime 𝔤) F) →+* ↥V :=
  (Subalgebra.val _).toRingHom.codRestrict V.toSubring (integralClosure_mem 𝔤 V hBV)

theorem coe_toV (x : ↥(integralClosure (Localization.AtPrime 𝔤) F)) : ((toV 𝔤 V hBV x : ↥V) : F) = algebraMap ↥(integralClosure (Localization.AtPrime 𝔤) F) F x := rfl

noncomputable def P₁ : Ideal ↥(integralClosure (Localization.AtPrime 𝔤) F) := (IsLocalRing.maximalIdeal ↥V).comap (toV 𝔤 V hBV)

theorem mem_P₁_iff (x : ↥(integralClosure (Localization.AtPrime 𝔤) F)) : x ∈ P₁ 𝔤 V hBV ↔ (x : F) ∈ V.nonunits := by
  rw [P₁, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

scoped instance P₁_isPrime : (P₁ 𝔤 V hBV).IsPrime := Ideal.comap_isPrime _ _

theorem P₁_liesOver (h𝔪 : ∀ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔤), algebraMap (Localization.AtPrime 𝔤) F b ∈ V.nonunits) :
    (P₁ 𝔤 V hBV).LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔤)) := by
  refine ⟨((IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime 𝔤)).eq_of_le ?_ ?_)⟩
  · intro htop
    rw [Ideal.eq_top_iff_one, Ideal.under_def, Ideal.mem_comap, map_one, mem_P₁_iff] at htop
    rw [ValuationSubring.mem_nonunits_iff] at htop
    simp at htop
  · intro b hb
    rw [Ideal.under_def, Ideal.mem_comap, mem_P₁_iff]
    exact h𝔪 b hb

theorem P₁_ne_bot (h𝔪 : ∀ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔤), algebraMap (Localization.AtPrime 𝔤) F b ∈ V.nonunits)
    (hinj : Function.Injective (algebraMap (Localization.AtPrime 𝔤) F))
    {x : Localization.AtPrime 𝔤} (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔤)) (hx0 : x ≠ 0) : P₁ 𝔤 V hBV ≠ ⊥ := by
  intro h0
  have hmem : algebraMap (Localization.AtPrime 𝔤) ↥(integralClosure (Localization.AtPrime 𝔤) F) x ∈ P₁ 𝔤 V hBV := by
    rw [mem_P₁_iff]
    exact h𝔪 x hx
  have hinj' : Function.Injective (algebraMap (Localization.AtPrime 𝔤) ↥(integralClosure (Localization.AtPrime 𝔤) F)) := fun a b h =>
    hinj (by simpa using congrArg (fun y : ↥(integralClosure (Localization.AtPrime 𝔤) F) => (y : F)) h)
  rw [h0, Ideal.mem_bot, map_eq_zero_iff _ hinj'] at hmem
  exact hx0 hmem

private theorem _root_.DeuringVal.algebraMap_injective [Algebra (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F))] [IsScalarTower (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F] [IsFractionRing (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F))] :
    Function.Injective (algebraMap (Localization.AtPrime 𝔤) F) := by
  rw [IsScalarTower.algebraMap_eq (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F]
  exact (algebraMap ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F).injective.comp (IsFractionRing.injective (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F)))

p2m_export "DeuringVal" "algebraMap_injective"

theorem isDedekindDomain_integralClosure [Algebra (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F))] [IsScalarTower (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F]
    [IsFractionRing (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F))] [FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F] [Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F]
    (hdvr : IsDiscreteValuationRing (Localization.AtPrime 𝔤)) : IsDedekindDomain ↥(integralClosure (Localization.AtPrime 𝔤) F) :=
  integralClosure.isDedekindDomain (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F

theorem finite_integralClosure [Algebra (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F))] [IsScalarTower (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F]
    [IsFractionRing (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F))] [FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F] [Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F]
    (hdvr : IsDiscreteValuationRing (Localization.AtPrime 𝔤)) :
    Module.Finite (Localization.AtPrime 𝔤) ↥(integralClosure (Localization.AtPrime 𝔤) F) := by
  convert IsIntegralClosure.finite (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F
    ↥(integralClosure (Localization.AtPrime 𝔤) F) using 2
  all_goals try rfl

theorem isFractionRing_integralClosure [Algebra (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F))] [IsScalarTower (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F]
    [IsFractionRing (Localization.AtPrime 𝔤) ↥(IntermediateField.adjoin K₀ ({j} : Set F))] [FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F] [Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F] :
    IsFractionRing ↥(integralClosure (Localization.AtPrime 𝔤) F) F :=
  integralClosure.isFractionRing_of_finite_extension ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F

end closure

end frame
end DeuringVal
p2m_reactivate "P2MW.S_ValuationSubring_finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss.DeuringVal"

open IsLocalRing IsDedekindDomain

namespace DeuringGlue

theorem unique_prime_and_unramified_of_finrank_le_inertiaDeg
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (E : Type*) [Field E] [Algebra B E] [IsFractionRing B E]
    (F : Type*) [Field F] [Algebra E F] [Algebra B F] [IsScalarTower B E F]
    [FiniteDimensional E F] [Algebra.IsSeparable E F]

    [IsDedekindDomain ↥(integralClosure B F)] [IsFractionRing ↥(integralClosure B F) F]
    (P₁ : Ideal ↥(integralClosure B F)) [P₁.IsPrime] [P₁.LiesOver (IsLocalRing.maximalIdeal B)]
    (hf : Module.finrank E F ≤ Ideal.inertiaDeg' (IsLocalRing.maximalIdeal B) P₁) :
    ∃ h0 : P₁ ≠ ⊥,
      (∀ P : Ideal ↥(integralClosure B F), P.IsPrime → P.LiesOver (IsLocalRing.maximalIdeal B) → P = P₁) ∧
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal B) P₁ = 1 ∧
      Ideal.inertiaDeg' (IsLocalRing.maximalIdeal B) P₁ = Module.finrank E F ∧
      (∀ V' : ValuationSubring F, V' ≠ ⊤ → (∀ x : B, algebraMap B F x ∈ V') →
        (∀ x ∈ IsLocalRing.maximalIdeal B, algebraMap B F x ∈ V'.nonunits) →
        V' = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F ⟨P₁, inferInstance, h0⟩) ∧
      (∀ ϖ : B, Irreducible ϖ → ∀ x ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F ⟨P₁, inferInstance, h0⟩,
        x ∈ (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F ⟨P₁, inferInstance, h0⟩).nonunits →
        ∃ y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F ⟨P₁, inferInstance, h0⟩, x = algebraMap B F ϖ * y) := by
  classical

  haveI : Module.IsTorsionFree B F := .trans_faithfulSMul B E F
  haveI : FaithfulSMul B F := inferInstance
  haveI : Module.Finite B ↥(integralClosure B F) := IsIntegralClosure.finite B E F (integralClosure B F)
  have h𝔪0 : IsLocalRing.maximalIdeal B ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have h0 : P₁ ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔪0 P₁

  obtain ⟨hrange, he, hfd, -, hval, hunif⟩ :=
    IsDiscreteValuationRing.primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg (O := B) (F := F) E
      (ι := Unit) (fun _ => P₁) (hprime := fun _ => inferInstance) (fun _ => h0) (hover := fun _ => inferInstance)
      (fun _ _ _ => Subsingleton.elim _ _) (fun _ => Module.finrank E F) (fun _ => hf) (by simp)
  refine ⟨h0, ?_, he (), hfd (), ?_, ?_⟩
  · intro P hP hPl
    have : P ∈ (IsLocalRing.maximalIdeal B).primesOver ↥(integralClosure B F) := ⟨hP, hPl⟩
    rw [hrange] at this
    obtain ⟨_, rfl⟩ := this
    rfl
  · intro V' hV' hBV' hmV'
    obtain ⟨_, hi⟩ := hval V' hV' hBV' hmV'
    exact hi
  · intro ϖ hϖ x hx hxn
    exact hunif () ϖ hϖ x hx hxn

end DeuringGlue
p2m_reactivate "P2MW.S_ValuationSubring_finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss.DeuringVal"

namespace DeuringValF

variable {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  {E : Type u} [Field E] [Algebra B E] [IsFractionRing B E]
  {F : Type u} [Field F] [Algebra E F] [Algebra B F] [IsScalarTower B E F]
  [FiniteDimensional E F] [Algebra.IsSeparable E F]
  [IsDedekindDomain ↥(integralClosure B F)] [IsFractionRing ↥(integralClosure B F) F]
  [Module.Finite B ↥(integralClosure B F)]
  (V : ValuationSubring F)
  (hBV : ∀ b : B, algebraMap B F b ∈ V)
  (h𝔪 : ∀ b ∈ maximalIdeal B, algebraMap B F b ∈ V.nonunits)
  (toV : ↥(integralClosure B F) →+* ↥V) (coe_toV : ∀ x, ((toV x : ↥V) : F) = algebraMap _ F x)
  (P₁ : Ideal ↥(integralClosure B F)) (hP₁ : P₁ = Ideal.comap toV (maximalIdeal ↥V))
  [P₁.IsPrime] [P₁.LiesOver (maximalIdeal B)] (hP₁0 : P₁ ≠ ⊥)

include E hBV h𝔪 coe_toV hP₁ hP₁0

theorem eq_valuationSubringAtPrime :
    V = HeightOneSpectrum.valuationSubringAtPrime F ⟨P₁, inferInstance, hP₁0⟩ := by
  classical
  haveI : Module.IsTorsionFree B F := .trans_faithfulSMul B E F
  haveI : FaithfulSMul B F := inferInstance

  have hle : HeightOneSpectrum.valuationSubringAtPrime F ⟨P₁, inferInstance, hP₁0⟩ ≤ V := by
    rintro x ⟨a, s, hs, rfl⟩
    have ha : algebraMap ↥(integralClosure B F) F a ∈ V := by rw [← coe_toV]; exact (toV a).2
    have hsu : IsUnit (toV s) := by
      by_contra h
      have h1 : toV s ∈ maximalIdeal ↥V := (IsLocalRing.mem_maximalIdeal _).mpr h
      have h2 : s ∈ P₁ := by rw [hP₁]; exact h1
      exact hs h2
    obtain ⟨u, hu⟩ := hsu
    have hmul : ((u : ↥V) : F) * (((u⁻¹ : (↥V)ˣ) : ↥V) : F) = 1 := by
      rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
    have hinv : (algebraMap ↥(integralClosure B F) F s)⁻¹ = (((u⁻¹ : (↥V)ˣ) : ↥V) : F) := by
      rw [← coe_toV, ← hu]
      exact inv_eq_of_mul_eq_one_right hmul
    have hs' : (algebraMap ↥(integralClosure B F) F s)⁻¹ ∈ V := by rw [hinv]; exact SetLike.coe_mem _
    exact V.mul_mem _ _ ha hs'

  have hne : V ≠ ⊤ := by
    obtain ⟨b, hb𝔪, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (IsDiscreteValuationRing.not_a_field B)
    intro hTop
    have hbn : (⟨algebraMap B F b, hBV b⟩ : ↥V) ∈ maximalIdeal ↥V :=
      (ValuationSubring.coe_mem_nonunits_iff).mp (h𝔪 b hb𝔪)
    have hy : (algebraMap B F b)⁻¹ ∈ V := by rw [hTop]; exact ValuationSubring.mem_top _
    have hunit : IsUnit (⟨algebraMap B F b, hBV b⟩ : ↥V) := by
      refine IsUnit.of_mul_eq_one (b := ⟨(algebraMap B F b)⁻¹, hy⟩) (Subtype.ext ?_)
      change algebraMap B F b * (algebraMap B F b)⁻¹ = 1
      exact mul_inv_cancel₀ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B F)).mpr hb0)
    exact (IsLocalRing.mem_maximalIdeal _).mp hbn hunit
  exact (ValuationSubring.eq_of_le_of_ne_top _ hle hne).symm

theorem finite_and_finrank_eq_inertiaDeg_and_le
    (𝔽 : Type u) [Field 𝔽] [Algebra 𝔽 (ResidueField ↥V)] (jV : ↥V)
    (hres : ∀ b : B, residue ↥V ⟨algebraMap B F b, hBV b⟩ ∈
      IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V)))
    (hres_surj : ∀ z ∈ IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V)),
      ∃ b : B, residue ↥V ⟨algebraMap B F b, hBV b⟩ = z)
    (hres_ker : ∀ b : B, residue ↥V ⟨algebraMap B F b, hBV b⟩ = 0 → b ∈ maximalIdeal B) :
    FiniteDimensional ↥(IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V))) (ResidueField ↥V) ∧
    Module.finrank ↥(IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V))) (ResidueField ↥V) =
      Ideal.inertiaDeg' (maximalIdeal B) P₁ ∧
    Ideal.inertiaDeg' (maximalIdeal B) P₁ ≤ Module.finrank E F := by
  classical
  haveI : Module.IsTorsionFree B F := .trans_faithfulSMul B E F
  haveI : FaithfulSMul B F := inferInstance
  have hmax : P₁.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP₁0

  let gBV : B →+* ↥V := (algebraMap B F).codRestrict V hBV
  let g : B →+* ResidueField ↥V := (residue ↥V).comp gBV
  have hg : ∀ b : B, g b = residue ↥V ⟨algebraMap B F b, hBV b⟩ := fun b => rfl
  have hgker : ∀ b : B, g b = 0 ↔ b ∈ maximalIdeal B := fun b => by
    refine ⟨fun h => hres_ker b (by rw [← hg]; exact h), fun h => ?_⟩
    rw [hg, IsLocalRing.residue_eq_zero_iff]
    exact (ValuationSubring.coe_mem_nonunits_iff).mp (h𝔪 b h)
  let gL : B →+* ↥(IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V))) :=
    g.codRestrict (IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V))) fun b => by rw [hg]; exact hres b
  let i₀ : ResidueField B →+* ↥(IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V))) :=
    Ideal.Quotient.lift (maximalIdeal B) gL fun b hb => Subtype.ext (by
      rw [RingHom.codRestrict_apply]; exact (hgker b).mpr hb)
  have hi₀ : Function.Bijective i₀ := by
    refine ⟨i₀.injective, fun z => ?_⟩
    obtain ⟨b, hb⟩ := hres_surj z.1 z.2
    exact ⟨Ideal.Quotient.mk (maximalIdeal B) b, Subtype.ext (by rw [← hb, ← hg]; rfl)⟩
  let i : ResidueField B ≃+* ↥(IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V))) :=
    RingEquiv.ofBijective i₀ hi₀

  let g' : ↥(integralClosure B F) →+* ResidueField ↥V := (residue ↥V).comp toV
  have hg'ker : RingHom.ker g' = P₁ := by
    rw [hP₁, ← RingHom.comap_ker, IsLocalRing.ker_residue]
  have hVW := eq_valuationSubringAtPrime (E := E) V hBV h𝔪 toV coe_toV P₁ hP₁ hP₁0
  have hg'surj : Function.Surjective g' := by
    intro v
    obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective v
    have hw : (w : F) ∈ HeightOneSpectrum.valuationSubringAtPrime F ⟨P₁, inferInstance, hP₁0⟩ := by
      rw [← hVW]; exact w.2
    obtain ⟨a, s, hs, hw'⟩ := hw

    haveI := hmax
    have hs0 : Ideal.Quotient.mk P₁ s ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hs
    obtain ⟨sbar, hsbar⟩ := Ideal.Quotient.exists_inv hs0
    obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective sbar
    have hss' : g' s * g' s' = 1 := by
      have h1 : Ideal.Quotient.mk P₁ (s * s') = 1 := by rw [map_mul, hsbar]
      have h2 : s * s' - 1 ∈ RingHom.ker g' := by
        rw [hg'ker, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
      have h3 := (RingHom.mem_ker).mp h2
      rw [map_sub, map_mul, map_one, sub_eq_zero] at h3
      exact h3
    refine ⟨a * s', ?_⟩

    have hsu : IsUnit (toV s) := by
      by_contra h
      exact hs (show s ∈ P₁ from by rw [hP₁]; exact (IsLocalRing.mem_maximalIdeal _).mpr h)
    obtain ⟨u, hu⟩ := hsu
    have hwu : w = toV a * ((u⁻¹ : (↥V)ˣ) : ↥V) := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, coe_toV, hw']
      congr 1
      have hmul : ((u : ↥V) : F) * (((u⁻¹ : (↥V)ˣ) : ↥V) : F) = 1 := by
        rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
      rw [← coe_toV, ← hu]
      exact inv_eq_of_mul_eq_one_right hmul
    have hgu : g' s * residue ↥V ((u⁻¹ : (↥V)ˣ) : ↥V) = 1 := by
      change residue ↥V (toV s) * _ = 1
      rw [← hu, ← map_mul, Units.mul_inv, map_one]
    have hinv : residue ↥V ((u⁻¹ : (↥V)ˣ) : ↥V) = g' s' :=
      left_inv_eq_right_inv ((mul_comm _ _).trans hgu) hss'
    rw [map_mul, hwu, map_mul, ← hinv]
    rfl
  letI : Algebra (ResidueField B) (↥(integralClosure B F) ⧸ P₁) :=
    inferInstanceAs (Algebra (B ⧸ maximalIdeal B) (↥(integralClosure B F) ⧸ P₁))
  haveI : Module.Finite (ResidueField B) (↥(integralClosure B F) ⧸ P₁) :=
    module_finite_of_liesOver P₁ (maximalIdeal B)
  haveI : NoZeroSMulDivisors B F := ⟨fun {c x} h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun h0 => (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective B F)).mp h0⟩
  haveI : NoZeroSMulDivisors B ↥(integralClosure B F) :=
    Subtype.val_injective.noZeroSMulDivisors (Subtype.val : ↥(integralClosure B F) → F) rfl (fun _ _ => rfl)
  let jj : (↥(integralClosure B F) ⧸ P₁) ≃+* ResidueField ↥V :=
    (Ideal.quotEquivOfEq hg'ker.symm).trans (RingHom.quotientKerEquivOfSurjective hg'surj)

  have hc : (algebraMap ↥(IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V))) (ResidueField ↥V)).comp
      i.toRingHom = jj.toRingHom.comp (algebraMap (ResidueField B) (↥(integralClosure B F) ⧸ P₁)) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    change ((i₀ (Ideal.Quotient.mk (maximalIdeal B) x) : ↥(IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V)))) :
      ResidueField ↥V) = jj (algebraMap (ResidueField B) (↥(integralClosure B F) ⧸ P₁) (Ideal.Quotient.mk _ x))
    have e1 : algebraMap (ResidueField B) (↥(integralClosure B F) ⧸ P₁) (Ideal.Quotient.mk (maximalIdeal B) x) =
        Ideal.Quotient.mk P₁ (algebraMap B ↥(integralClosure B F) x) := rfl
    have e2 : ∀ y, jj (Ideal.Quotient.mk P₁ y) = g' y := fun y => by
      simp only [jj, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
      rfl
    rw [e1, e2]
    change (gL x : ResidueField ↥V) = g' (algebraMap B ↥(integralClosure B F) x)
    rw [RingHom.codRestrict_apply]
    change g x = residue ↥V (toV (algebraMap B ↥(integralClosure B F) x))
    rw [hg]
    congr 1
    apply Subtype.ext
    rw [coe_toV, ← IsScalarTower.algebraMap_apply]

  have hfr : Module.finrank ↥(IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V))) (ResidueField ↥V) =
      Ideal.inertiaDeg' (maximalIdeal B) P₁ := by
    rw [Ideal.inertiaDeg_algebraMap]
    exact (Algebra.finrank_eq_of_equiv_equiv i jj hc).symm
  have hfin : FiniteDimensional ↥(IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V))) (ResidueField ↥V) :=
    Module.Finite.of_equiv_equiv i jj hc
  refine ⟨hfin, hfr, ?_⟩
  exact Ideal.inertiaDeg_le_finrank (integralClosure B F) E F P₁ (IsDiscreteValuationRing.not_a_field B)

theorem unramified_and_unique (hf : Module.finrank E F ≤ Ideal.inertiaDeg' (maximalIdeal B) P₁) :
    (∀ ϖB : B, Irreducible ϖB → ∀ f : F, f ∈ V.nonunits → f * (algebraMap B F ϖB)⁻¹ ∈ V) ∧
    (∀ V' : ValuationSubring F, V' ≠ ⊤ → (∀ b : B, algebraMap B F b ∈ V') →
      (∀ b ∈ maximalIdeal B, algebraMap B F b ∈ V'.nonunits) → V' = V) := by
  classical
  haveI : Module.IsTorsionFree B F := .trans_faithfulSMul B E F
  haveI : FaithfulSMul B F := inferInstance
  obtain ⟨h0, -, -, -, hval, hunifB⟩ :=
    DeuringGlue.unique_prime_and_unramified_of_finrank_le_inertiaDeg B E F P₁ hf
  have hVW := eq_valuationSubringAtPrime (E := E) V hBV h𝔪 toV coe_toV P₁ hP₁ hP₁0
  refine ⟨?_, ?_⟩
  · intro ϖB hϖB f hfn
    have hfV : f ∈ V := V.nonunits_subset hfn
    rw [hVW] at hfV hfn
    obtain ⟨y, hy, hfy⟩ := hunifB ϖB hϖB f hfV hfn
    have hϖ0 : algebraMap B F ϖB ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B F)).mpr hϖB.ne_zero
    rw [hfy, mul_comm (algebraMap B F ϖB) y, mul_assoc, mul_inv_cancel₀ hϖ0, mul_one, hVW]
    exact hy
  · intro V' hV'top hBV' hmV'
    rw [hval V' hV'top hBV' hmV', hVW]

theorem main
    (𝔽 : Type u) [Field 𝔽] [Algebra 𝔽 (ResidueField ↥V)] (jV : ↥V)
    (hres : ∀ b : B, residue ↥V ⟨algebraMap B F b, hBV b⟩ ∈
      IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V)))
    (hres_surj : ∀ z ∈ IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V)),
      ∃ b : B, residue ↥V ⟨algebraMap B F b, hBV b⟩ = z)
    (hres_ker : ∀ b : B, residue ↥V ⟨algebraMap B F b, hBV b⟩ = 0 → b ∈ maximalIdeal B)
    (ϖB : B) (hirr : Irreducible ϖB) :
    (FiniteDimensional ↥(IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V))) (ResidueField ↥V) ∧
      Module.finrank ↥(IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V))) (ResidueField ↥V) ≤
        Module.finrank E F) ∧
    (Module.finrank E F ≤
        Module.finrank ↥(IntermediateField.adjoin 𝔽 ({residue ↥V jV} : Set (ResidueField ↥V))) (ResidueField ↥V) →
      (∀ f : F, f ∈ V.nonunits → f * (algebraMap B F ϖB)⁻¹ ∈ V) ∧
      (∀ V' : ValuationSubring F, V' ≠ ⊤ → (∀ b : B, algebraMap B F b ∈ V') →
        (∀ b ∈ maximalIdeal B, algebraMap B F b ∈ V'.nonunits) → V' = V)) := by
  obtain ⟨hfin, hfr, hle⟩ := finite_and_finrank_eq_inertiaDeg_and_le (E := E) V hBV h𝔪 toV coe_toV P₁ hP₁ hP₁0
    𝔽 jV hres hres_surj hres_ker
  refine ⟨⟨hfin, hfr ▸ hle⟩, fun hdeg => ?_⟩
  obtain ⟨hunif, huniq⟩ := unramified_and_unique (E := E) V hBV h𝔪 toV coe_toV P₁ hP₁ hP₁0 (hfr ▸ hdeg)
  exact ⟨hunif ϖB hirr, huniq⟩

end DeuringValF
p2m_reactivate "P2MW.S_ValuationSubring_finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss.DeuringVal"

open Polynomial in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (V : ValuationSubring F)
    (hRV : ∀ r : R, algebraMap R F r ∈ V) (hϖV : algebraMap R F ϖ ∈ V.nonunits)
    (hjV : ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)

    (𝔽 : Type u) [Field 𝔽] [Algebra R 𝔽] (h𝔽 : Function.Surjective (algebraMap R 𝔽))
    [Algebra 𝔽 (IsLocalRing.ResidueField ↥V)]
    (hcomp : ∀ r : R, algebraMap 𝔽 (IsLocalRing.ResidueField ↥V) (algebraMap R 𝔽 r) =
      IsLocalRing.residue ↥V ⟨algebraMap R F r, hRV r⟩)
    (jV : ↥V) (hjV' : (jV : F) = j) :

    FiniteDimensional
        ↥(IntermediateField.adjoin 𝔽 ({IsLocalRing.residue ↥V jV} : Set (IsLocalRing.ResidueField ↥V)))
        (IsLocalRing.ResidueField ↥V) ∧
    Module.finrank
        ↥(IntermediateField.adjoin 𝔽 ({IsLocalRing.residue ↥V jV} : Set (IsLocalRing.ResidueField ↥V)))
        (IsLocalRing.ResidueField ↥V) ≤
      Module.finrank ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F ∧

    (Module.finrank ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F ≤
        Module.finrank
          ↥(IntermediateField.adjoin 𝔽 ({IsLocalRing.residue ↥V jV} : Set (IsLocalRing.ResidueField ↥V)))
          (IsLocalRing.ResidueField ↥V) →
      (∀ f : F, f ∈ V.nonunits → f * (algebraMap R F ϖ)⁻¹ ∈ V) ∧
      (∀ V' : ValuationSubring F, (∀ r : R, algebraMap R F r ∈ V') → algebraMap R F ϖ ∈ V'.nonunits →
        (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V') → V' = V)) := by
  classical

  haveI hgP : (Ideal.span {C ϖ} : Ideal R[X]).IsPrime := DeuringVal.isPrime_span_C hϖ
  obtain ⟨f, hf⟩ := DeuringVal.exists_ringHom_adjoin (K₀ := K₀) (Ideal.span {C ϖ} : Ideal R[X]) htj
  letI : Algebra (Localization.AtPrime (Ideal.span {C ϖ} : Ideal R[X])) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) :=
    f.toAlgebra
  letI : Algebra (Localization.AtPrime (Ideal.span {C ϖ} : Ideal R[X])) F :=
    ((algebraMap ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F).comp f).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime (Ideal.span {C ϖ} : Ideal R[X])) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcompat : ∀ p : R[X], algebraMap (Localization.AtPrime (Ideal.span {C ϖ} : Ideal R[X])) F
      (algebraMap R[X] (Localization.AtPrime (Ideal.span {C ϖ} : Ideal R[X])) p) = aeval j p := fun p => hf p
  haveI hdvr : IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {C ϖ} : Ideal R[X])) :=
    DeuringVal.isDiscreteValuationRing _ hϖ rfl
  haveI : IsFractionRing (Localization.AtPrime (Ideal.span {C ϖ} : Ideal R[X])) ↥(IntermediateField.adjoin K₀ ({j} : Set F)) :=
    DeuringVal.isFractionRing _ hcompat htj
  haveI := hFD
  haveI := hsep
  haveI := DeuringVal.isDedekindDomain_integralClosure (K₀ := K₀) (F := F) (j := j) (Ideal.span {C ϖ} : Ideal R[X]) hdvr
  haveI := DeuringVal.finite_integralClosure (K₀ := K₀) (F := F) (j := j) (Ideal.span {C ϖ} : Ideal R[X]) hdvr
  haveI := DeuringVal.isFractionRing_integralClosure (K₀ := K₀) (F := F) (j := j) (Ideal.span {C ϖ} : Ideal R[X])
  have hBV := DeuringVal.algebraMap_mem_of_gaussType (Ideal.span {C ϖ} : Ideal R[X]) hcompat htj hϖ rfl V hRV hjV
  have h𝔪 := DeuringVal.algebraMap_mem_nonunits_of_mem_maximalIdeal (Ideal.span {C ϖ} : Ideal R[X]) hcompat htj hϖ rfl
    V hRV hϖV hjV
  have hinj := DeuringVal.algebraMap_injective (K₀ := K₀) (F := F) (j := j) (Ideal.span {C ϖ} : Ideal R[X])
  have hirr := DeuringVal.irreducible_algebraMap (Ideal.span {C ϖ} : Ideal R[X]) hϖ rfl
  have hϖB : algebraMap R (Localization.AtPrime (Ideal.span {C ϖ} : Ideal R[X])) ϖ ∈
      maximalIdeal (Localization.AtPrime (Ideal.span {C ϖ} : Ideal R[X])) :=
    (IsLocalRing.mem_maximalIdeal _).mpr hirr.not_isUnit
  haveI := DeuringVal.P₁_liesOver (Ideal.span {C ϖ} : Ideal R[X]) V hBV h𝔪
  have hP₁0 := DeuringVal.P₁_ne_bot (Ideal.span {C ϖ} : Ideal R[X]) V hBV h𝔪 hinj hϖB hirr.ne_zero

  obtain ⟨ha, hb⟩ := DeuringValF.main (E := ↥(IntermediateField.adjoin K₀ ({j} : Set F))) V hBV h𝔪
    (DeuringVal.toV _ V hBV) (DeuringVal.coe_toV _ V hBV) (DeuringVal.P₁ _ V hBV) rfl hP₁0 𝔽 jV
    (fun b => DeuringVal.residue_mem_adjoin (𝔤 := (Ideal.span {C ϖ} : Ideal R[X])) (V := V) (hRV := hRV) (𝔽 := 𝔽)
      (hcomp := hcomp) (jV := jV) (hjV' := hjV') (hjV := hjV) (hcompat := hcompat) (htj := htj) (h𝔤 := rfl) (hBV := hBV) b)
    (fun z hz => DeuringVal.exists_residue_eq (𝔤 := (Ideal.span {C ϖ} : Ideal R[X])) (V := V) (hRV := hRV) (𝔽 := 𝔽)
      (hcomp := hcomp) (jV := jV) (hjV' := hjV') (hjV := hjV) (hcompat := hcompat) (htj := htj) (h𝔤 := rfl) (hϖV := hϖV)
      (hBV := hBV) (h𝔽 := h𝔽) z hz)
    (fun b hb => DeuringVal.mem_maximalIdeal_of_residue_eq_zero (𝔤 := (Ideal.span {C ϖ} : Ideal R[X])) (V := V) (hRV := hRV)
      (𝔽 := 𝔽) (hcomp := hcomp) (jV := jV) (hjV' := hjV') (hjV := hjV) (hcompat := hcompat) (htj := htj) (h𝔤 := rfl)
      (hBV := hBV) b hb)
    (algebraMap R _ ϖ) hirr
  have hϖF : algebraMap (Localization.AtPrime (Ideal.span {C ϖ} : Ideal R[X])) F
      (algebraMap R (Localization.AtPrime (Ideal.span {C ϖ} : Ideal R[X])) ϖ) = algebraMap R F ϖ :=
    DeuringVal.algebraMap_R_B_F (Ideal.span {C ϖ} : Ideal R[X]) hcompat ϖ
  refine ⟨ha.1, ha.2, fun hdeg => ?_⟩
  obtain ⟨hunif, huniq⟩ := hb hdeg
  refine ⟨fun g hg => hϖF ▸ hunif g hg, fun V' hRV' hϖV' hjV'' => ?_⟩
  refine huniq V' ?_ (DeuringVal.algebraMap_mem_of_gaussType (Ideal.span {C ϖ} : Ideal R[X]) hcompat htj hϖ rfl V' hRV' hjV'')
    (DeuringVal.algebraMap_mem_nonunits_of_mem_maximalIdeal (Ideal.span {C ϖ} : Ideal R[X]) hcompat htj hϖ rfl V' hRV' hϖV' hjV'')

  intro hTop
  have hϖ0 : algebraMap R F ϖ ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R K₀ F]
    exact (map_ne_zero_iff _ (algebraMap K₀ F).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective R K₀)).mpr hϖ.ne_zero)
  have hmem : (⟨algebraMap R F ϖ, hRV' ϖ⟩ : ↥V') ∈ maximalIdeal ↥V' :=
    (ValuationSubring.coe_mem_nonunits_iff).mp hϖV'
  have hy : (algebraMap R F ϖ)⁻¹ ∈ V' := by rw [hTop]; exact ValuationSubring.mem_top _
  refine (IsLocalRing.mem_maximalIdeal _).mp hmem (IsUnit.of_mul_eq_one (b := ⟨_, hy⟩) (Subtype.ext ?_))
  change algebraMap R F ϖ * (algebraMap R F ϖ)⁻¹ = 1
  exact mul_inv_cancel₀ hϖ0

end S_ValuationSubring_finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss
end P2MW
export P2MW.S_ValuationSubring_finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss (solution)
