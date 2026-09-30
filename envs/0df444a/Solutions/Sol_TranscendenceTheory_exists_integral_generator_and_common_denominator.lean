-- Prove2me | solution 1 for TranscendenceTheory.exists_integral_generator_and_common_denominator
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T11:24:06.786902+00:00
-- url     : https://prove2.me/submissions/b1e9dbc8-43a1-48a3-87bf-72ddd837c159

import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Tactic.FieldSimp

open Polynomial
open scoped nonZeroDivisors

noncomputable section

namespace TranscendenceTheory.IntegralGenerator


theorem finite_extension_presentation
    (R K E : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] [Field E]
    [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    [FiniteDimensional K E] {ι : Type*} [Fintype ι] (v : ι → E) :
    ∃ ν : E, IsIntegral R ν ∧ ∃ d : R, d ≠ 0 ∧
      ∀ i, ∃ p : R[X], aeval ν p = algebraMap R E d * v i := by
  classical
  have hinj : Function.Injective (algebraMap R E) := by
    rw [IsScalarTower.algebraMap_eq R K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective R K)
  have : Algebra.IsAlgebraic R K :=
    IsLocalization.isAlgebraic K (nonZeroDivisors R)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K E
  have hαR : IsAlgebraic R α :=
    (Algebra.IsAlgebraic.isAlgebraic (R := K) α).restrictScalars R
  obtain ⟨r, hr, hν⟩ := hαR.exists_integral_multiple
  let ν : E := r • α
  have hgen : Algebra.adjoin K {ν} = ⊤ := by
    have hαgen : Algebra.adjoin K {α} = ⊤ :=
      Algebra.adjoin_eq_top_of_primitive_element
        (Algebra.IsAlgebraic.isAlgebraic (R := K) α) hα
    apply top_unique
    rw [← hαgen]
    apply Algebra.adjoin_le
    intro x hx
    have hxα : x = α := Set.mem_singleton_iff.mp hx
    rw [hxα]
    have hmem := (Algebra.adjoin K {ν}).smul_mem
      (Algebra.self_mem_adjoin_singleton K ν) (algebraMap R K r)⁻¹
    have he : (algebraMap R K r)⁻¹ • ν = α := by
      simp only [ν, Algebra.smul_def, map_inv₀, ← IsScalarTower.algebraMap_apply R K E]
      rw [inv_mul_cancel_left₀ (map_ne_zero_iff _ hinj |>.mpr hr)]
    rwa [he] at hmem
  have hp : ∀ i, ∃ p : K[X], aeval ν p = v i := by
    intro i
    have hi : v i ∈ Algebra.adjoin K {ν} := by rw [hgen]; trivial
    rwa [Algebra.adjoin_singleton_eq_range_aeval] at hi
  choose p hp using hp
  let q (i : ι) : R[X] := IsLocalization.integerNormalization (nonZeroDivisors R) (p i)
  have hb : ∀ i, ∃ b : R, b ∈ nonZeroDivisors R ∧
      (q i).map (algebraMap R K) = b • p i := by
    intro i
    exact IsLocalization.integerNormalization_spec (nonZeroDivisors R) (p i)
  choose b hb0 hb using hb
  refine ⟨ν, hν, ∏ i, b i, Finset.prod_ne_zero_iff.mpr (fun i _ =>
    mem_nonZeroDivisors_iff_ne_zero.mp (hb0 i)), fun i => ?_⟩
  refine ⟨C (∏ j ∈ Finset.univ.erase i, b j) * q i, ?_⟩
  have hqi : aeval ν (q i) = algebraMap R E (b i) * v i := by
    calc
      aeval ν (q i) = aeval ν ((q i).map (algebraMap R K)) :=
        (aeval_map_algebraMap ..).symm
      _ = aeval ν (b i • p i) := congrArg (aeval ν : K[X] →ₐ[K] E) (hb i)
      _ = b i • aeval ν (p i) := map_smul ((aeval ν : K[X] →ₐ[K] E).restrictScalars R) _ _
      _ = algebraMap R E (b i) * v i := by rw [hp, Algebra.smul_def]
  rw [map_mul, aeval_C, hqi, ← mul_assoc, ← map_mul]
  congr 2
  exact Finset.prod_erase_mul (Finset.univ (α := ι)) b (Finset.mem_univ i)


theorem exists_integral_presentation {ι : Type*} [Fintype ι]
    (θ : ℂ) (hθ : Transcendental ℚ θ) (v : ι → ℂ)
    (hv : ∀ i, IsAlgebraic (Algebra.adjoin ℚ {θ}) (v i)) :
    ∃ ν : ℂ,
      (∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (aeval θ).toRingHom ν = 0) ∧
      ∃ d : ℤ[X], aeval θ d ≠ 0 ∧
        ∀ i, ∃ p : ℤ[X][X], p.eval₂ (aeval θ).toRingHom ν = aeval θ d * v i := by
  classical
  let R := ℤ[X]
  let : Algebra R ℂ := (aeval θ).toAlgebra
  have hθZ : Transcendental ℤ θ :=
    hθ.restrictScalars (algebraMap ℤ ℚ).injective_int
  have hinj : Function.Injective (algebraMap R ℂ) :=
    (transcendental_iff_injective.mp hθZ)
  let : FaithfulSMul R ℂ := (faithfulSMul_iff_algebraMap_injective R ℂ).mpr hinj
  let B := Algebra.adjoin ℚ {θ}
  let θB : B := ⟨θ, Algebra.self_mem_adjoin_singleton ℚ θ⟩
  let : Algebra R B := (aeval θB).toAlgebra
  have : IsScalarTower R B ℂ := .of_algebraMap_eq fun p => by
    exact aeval_algHom_apply (B.val.restrictScalars ℤ) θB p
  have halgB : ∀ b : B, IsAlgebraic R (b : ℂ) := by
    intro b
    refine Algebra.adjoin_induction (p := fun x _ => IsAlgebraic R x) ?_ ?_ ?_ ?_ b.property
    · intro x hx
      have hxθ : x = θ := Set.mem_singleton_iff.mp hx
      rw [hxθ]
      have h := isAlgebraic_algebraMap (R := R) (A := ℂ) (X : ℤ[X])
      change IsAlgebraic R (aeval θ X) at h
      simpa only [aeval_X] using h
    · intro q
      have hq : IsAlgebraic R ((q.num : ℂ) / (q.den : ℂ)) :=
        (isAlgebraic_intCast (R := R) q.num).mul
          (isAlgebraic_natCast (R := R) q.den).inv
      change IsAlgebraic R (q : ℂ)
      simpa only [div_eq_mul_inv, Rat.cast_def] using hq
    · intro x y _ _ hx hy
      exact hx.add hy
    · intro x y _ _ hx hy
      exact hx.mul hy
  have : Algebra.IsAlgebraic R B := ⟨fun b =>
    (isAlgebraic_algebraMap_iff (R := R) (S := B) (A := ℂ) Subtype.val_injective).mp
      (halgB b)⟩
  have hvR : ∀ i, IsAlgebraic R (v i) := fun i => (hv i).restrictScalars R
  let K := FractionRing R
  let : Algebra K ℂ := FractionRing.liftAlgebra R ℂ
  have : IsScalarTower R K ℂ := FractionRing.isScalarTower_liftAlgebra R ℂ
  have hvK : ∀ i, IsIntegral K (v i) := fun i =>
    ((hvR i).extendScalars (IsFractionRing.injective R K)).isIntegral
  let E := IntermediateField.adjoin K (Set.range v)
  have : IsScalarTower R E ℂ := .of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin (by
    rintro x ⟨i, rfl⟩
    exact hvK i)
  let w (i : ι) : E := ⟨v i, IntermediateField.subset_adjoin K (Set.range v) ⟨i, rfl⟩⟩
  obtain ⟨ν, hν, d, hd, hp⟩ := finite_extension_presentation R K E w
  refine ⟨(ν : ℂ), ?_, d, map_ne_zero_iff _ hinj |>.mpr hd, fun i => ?_⟩
  · have hνC := hν.map (IsScalarTower.toAlgHom R E ℂ)
    exact hνC
  · obtain ⟨p, hp⟩ := hp i
    refine ⟨p, ?_⟩
    change aeval (ν : ℂ) p = algebraMap R ℂ d * v i
    calc
      _ = algebraMap E ℂ (aeval ν p) :=
        aeval_algHom_apply (IsScalarTower.toAlgHom R E ℂ) ν p
      _ = _ := by rw [hp, map_mul, IsScalarTower.algebraMap_apply R E ℂ]; rfl

end TranscendenceTheory.IntegralGenerator

open TranscendenceTheory.IntegralGenerator

theorem solution {ι : Type*} [Fintype ι]
    (θ : ℂ) (hθ : Transcendental ℚ θ) (v : ι → ℂ)
    (hv : ∀ i, IsAlgebraic (Algebra.adjoin ℚ {θ}) (v i)) :
    ∃ ν : ℂ,
      (∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (aeval θ).toRingHom ν = 0) ∧
      ∃ d : ℤ[X], aeval θ d ≠ 0 ∧
        ∀ i, ∃ p : ℤ[X][X], p.eval₂ (aeval θ).toRingHom ν = aeval θ d * v i := by
  exact exists_integral_presentation θ hθ v hv
