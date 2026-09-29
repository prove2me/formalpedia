-- Prove2me | solution 1 for ValuationSubring.exists_ringHom_comp_eq_and_subtype_comp_eq_and_isLocalHom_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/77465d3b-f015-5477-8970-78d89af41847

import Mathlib
import Theorems.Thm_ValuationSubring_exists_algHom_forall_apply_mem_iff_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_ringHom_comp_eq_and_subtype_comp_eq_and_isLocalHom_of_isDiscreteValuationRing

set_option autoImplicit false

namespace LocalMapOverDVR

theorem isUnit_iff_inv_mem {K : Type*} [Field K] (W : ValuationSubring K) (y : K) (hy : y ∈ W) :
    IsUnit (⟨y, hy⟩ : W) ↔ y ≠ 0 ∧ y⁻¹ ∈ W := by
  constructor
  · rintro ⟨u, hu⟩
    have hmul : y * (((u⁻¹ : Wˣ) : W) : K) = 1 := by
      have h := congrArg (fun z : W => (z : K)) (u.mul_inv)
      rw [hu] at h
      simpa using h
    have hy0 : y ≠ 0 := left_ne_zero_of_mul_eq_one hmul
    refine ⟨hy0, ?_⟩
    rw [inv_eq_of_mul_eq_one_right hmul]
    exact ((u⁻¹ : Wˣ) : W).2
  · rintro ⟨hy0, hinv⟩
    exact isUnit_iff_exists_inv.mpr ⟨⟨y⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hy0)⟩

theorem isAlgebraic_algebraicClosure_rat (K : Type*) [Field K] [Algebra K (AlgebraicClosure ℚ)] :
    Algebra.IsAlgebraic K (AlgebraicClosure ℚ) := by
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap K (AlgebraicClosure ℚ)).injective).mpr inferInstance
  refine ⟨fun x => ?_⟩
  obtain ⟨p, hp0, hpx⟩ := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x
  refine ⟨p.map (algebraMap ℚ K), (Polynomial.map_ne_zero_iff (algebraMap ℚ K).injective).mpr hp0, ?_⟩
  rw [Polynomial.aeval_def] at hpx
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  convert hpx using 2
  all_goals first | rfl | skip
  exact RingHom.ext fun q => by rw [RingHom.comp_apply, eq_ratCast, eq_ratCast, map_ratCast]

end LocalMapOverDVR

open LocalMapOverDVR in

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    (ιA' : O' →+* ↥A) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA')
    (R : Type) [CommRing R] [IsLocalRing R] (σ : O' →+* R) (hσ : IsLocalHom σ)
    (L : Type) [Field L] (r : R →+* L)
    (e₀ : L →+* AlgebraicClosure ℚ) (he₀ : e₀.comp (r.comp σ) = A.subtype.comp ιA') :
    ∃ (τ : L →+* AlgebraicClosure ℚ) (χ : R →+* ↥A),
      τ.comp (r.comp σ) = A.subtype.comp ιA' ∧ A.subtype.comp χ = τ.comp r ∧ IsLocalHom χ := by
  classical

  set j : O' →+* L := r.comp σ with hj_def
  have hj : Function.Injective j := by
    have h := congrArg (fun f : O' →+* AlgebraicClosure ℚ => (f : O' → AlgebraicClosure ℚ)) he₀
    have hinj : Function.Injective (e₀.comp (r.comp σ)) := by
      rw [he₀]
      exact Subtype.val_injective.comp hιA'inj
    exact Function.Injective.of_comp (f := e₀) (by simpa [hj_def, RingHom.coe_comp] using hinj)
  have hι : Function.Injective (A.subtype.comp ιA') := Subtype.val_injective.comp hιA'inj
  let K := FractionRing O'
  letI algKL : Algebra K L := (IsFractionRing.lift (K := K) hj).toAlgebra
  letI algKQ : Algebra K (AlgebraicClosure ℚ) := (IsFractionRing.lift (K := K) hι).toAlgebra
  have hKL : ∀ x : O', algebraMap K L (algebraMap O' K x) = j x := fun x =>
    IsFractionRing.lift_algebraMap (K := K) hj x
  have hKQ : ∀ x : O', algebraMap K (AlgebraicClosure ℚ) (algebraMap O' K x) = (ιA' x : AlgebraicClosure ℚ) := fun x =>
    IsFractionRing.lift_algebraMap (K := K) hι x

  have he₀K : ∀ k : K, e₀ (algebraMap K L k) = algebraMap K (AlgebraicClosure ℚ) k := by
    intro k
    have h1 : (e₀.comp (algebraMap K L)).comp (algebraMap O' K) = (algebraMap K (AlgebraicClosure ℚ)).comp (algebraMap O' K) := by
      ext x
      simp only [RingHom.comp_apply, hKL, hKQ, hj_def]
      exact congrArg (fun f : O' →+* AlgebraicClosure ℚ => f x) he₀
    have h2 : e₀.comp (algebraMap K L) = algebraMap K (AlgebraicClosure ℚ) :=
      IsLocalization.ringHom_ext (nonZeroDivisors O') h1
    exact congrArg (fun f : K →+* AlgebraicClosure ℚ => f k) h2
  let e₀' : L →ₐ[K] AlgebraicClosure ℚ := { e₀ with commutes' := he₀K }
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure ℚ) := isAlgebraic_algebraicClosure_rat K
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_injective e₀' e₀'.toRingHom.injective

  obtain ⟨V, hrV, hrloc⟩ := IsLocalRing.exists_factor_valuationRing r

  have hVO : ∀ x : O', j x ∈ V := fun x => hrV (σ x)
  have hunitV : ∀ x : O', IsUnit (⟨j x, hVO x⟩ : V) → IsUnit x := by
    intro x hx
    haveI := hrloc
    haveI := hσ
    have h1 : IsUnit (σ x) := (isUnit_map_iff (r.codRestrict V.toSubring hrV) (σ x)).mp hx
    exact (isUnit_map_iff σ x).mp h1
  have hunitA : ∀ x : O', IsUnit (ιA' x) → IsUnit x := by
    intro x hx
    haveI := hιA'loc
    exact (isUnit_map_iff ιA' x).mp hx
  have hV : ∀ x : K, algebraMap K L x ∈ V ↔ algebraMap K (AlgebraicClosure ℚ) x ∈ A := by
    intro x

    have key : ∀ (P : K → Prop), (∀ y : O', P (algebraMap O' K y)) →
        (∀ y : O', ¬ IsUnit y → ∀ z : K, z * algebraMap O' K y = 1 → ¬ P z) →
        (P x ↔ ∃ y : O', algebraMap O' K y = x) := by
      intro P hP hN
      constructor
      · intro hx
        by_contra hnot
        rcases ValuationRing.isInteger_or_isInteger O' x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact hnot ⟨y, hy⟩
        ·
          have hx0 : x ≠ 0 := by
            rintro rfl
            exact hnot ⟨0, by simp⟩
          have hyu : ¬ IsUnit y := by
            intro hyu
            obtain ⟨u, rfl⟩ := hyu
            apply hnot
            refine ⟨(u⁻¹ : O'ˣ), ?_⟩
            have : algebraMap O' K (u : O') * algebraMap O' K ((u⁻¹ : O'ˣ) : O') = 1 := by
              rw [← map_mul, Units.mul_inv, map_one]
            rw [hy] at this
            calc algebraMap O' K ((u⁻¹ : O'ˣ) : O') = x * (x⁻¹ * algebraMap O' K ((u⁻¹ : O'ˣ) : O')) := by
                  rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
              _ = x := by rw [this, mul_one]
          exact hN y hyu x (by rw [hy, mul_inv_cancel₀ hx0]) hx
      · rintro ⟨y, rfl⟩
        exact hP y
    have hPV : ∀ y : O', (fun z => algebraMap K L z ∈ V) (algebraMap O' K y) := fun y => by
      show algebraMap K L (algebraMap O' K y) ∈ V
      rw [hKL]; exact hVO y
    have hNV : ∀ y : O', ¬ IsUnit y → ∀ z : K, z * algebraMap O' K y = 1 → ¬ (fun z => algebraMap K L z ∈ V) z := by
      intro y hyu z hz hzV
      refine hyu (hunitV y (isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K L z, hzV⟩, Subtype.ext ?_⟩))
      show j y * algebraMap K L z = 1
      rw [← hKL, ← map_mul, mul_comm, hz, map_one]
    have hPA : ∀ y : O', (fun z => algebraMap K (AlgebraicClosure ℚ) z ∈ A) (algebraMap O' K y) := fun y => by
      show algebraMap K (AlgebraicClosure ℚ) (algebraMap O' K y) ∈ A
      rw [hKQ]; exact (ιA' y).2
    have hNA : ∀ y : O', ¬ IsUnit y → ∀ z : K, z * algebraMap O' K y = 1 →
        ¬ (fun z => algebraMap K (AlgebraicClosure ℚ) z ∈ A) z := by
      intro y hyu z hz hzA
      refine hyu (hunitA y (isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K (AlgebraicClosure ℚ) z, hzA⟩, Subtype.ext ?_⟩))
      show (ιA' y : AlgebraicClosure ℚ) * algebraMap K (AlgebraicClosure ℚ) z = 1
      rw [← hKQ, ← map_mul, mul_comm, hz, map_one]
    exact (key _ hPV hNV).trans (key _ hPA hNA).symm

  obtain ⟨τ, hτ⟩ := ValuationSubring.exists_algHom_forall_apply_mem_iff_of_isAlgebraic K A L V hV

  have hχmem : ∀ z : R, (τ.toRingHom.comp r) z ∈ A.toSubring := fun z => (hτ (r z)).mpr (hrV z)
  refine ⟨τ.toRingHom, (τ.toRingHom.comp r).codRestrict A.toSubring hχmem, ?_, ?_, ?_⟩
  · ext x
    show τ (j x) = (ιA' x : AlgebraicClosure ℚ)
    rw [← hKL, AlgHom.commutes, hKQ]
  · rfl
  · constructor
    intro z hz
    haveI := hrloc
    apply (isUnit_map_iff (r.codRestrict V.toSubring hrV) z).mp

    change IsUnit (⟨τ (r z), hχmem z⟩ : A) at hz
    rw [isUnit_iff_inv_mem A (τ (r z)) (hχmem z)] at hz
    obtain ⟨h0, hinv⟩ := hz
    have hr0 : r z ≠ 0 := fun h => h0 (by rw [h, map_zero])
    rw [← map_inv₀, hτ] at hinv
    show IsUnit (⟨r z, hrV z⟩ : V)
    exact (isUnit_iff_inv_mem V (r z) (hrV z)).mpr ⟨hr0, hinv⟩

end S_ValuationSubring_exists_ringHom_comp_eq_and_subtype_comp_eq_and_isLocalHom_of_isDiscreteValuationRing
end P2MW
export P2MW.S_ValuationSubring_exists_ringHom_comp_eq_and_subtype_comp_eq_and_isLocalHom_of_isDiscreteValuationRing (solution)
