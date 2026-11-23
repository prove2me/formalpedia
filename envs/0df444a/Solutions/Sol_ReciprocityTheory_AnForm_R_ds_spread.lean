-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ds_spread
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:18.963316+00:00
-- url     : https://prove2.me/submissions/131a63bd-abfd-41a9-a348-bacd757e40d9

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {R S : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S]
    (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime S P] (I : Ideal R) (a : R) (ha : a ∈ I)
    (hmap : I.map (algebraMap R S) = Ideal.span {algebraMap R S a})
    (hnzd : algebraMap R S a ∈ nonZeroDivisors S) :
    ∃ σ : R, σ ∉ P ∧ ∀ (T : Type*) [CommRing T] [Algebra R T] [IsLocalization.Away σ T],
      I.map (algebraMap R T) = Ideal.span {algebraMap R T a} ∧
        algebraMap R T a ∈ nonZeroDivisors T := by
  obtain ⟨sI, hsI⟩ := IsNoetherian.noetherian I
  obtain ⟨sJ, hsJ⟩ := IsNoetherian.noetherian (LinearMap.ker (LinearMap.mulRight R a))

  have key : ∀ i ∈ I, ∃ c ∈ P.primeCompl, c * i ∈ Ideal.span {a} := by
    intro i hi
    have hi' : algebraMap R S i ∈ Ideal.span {algebraMap R S a} := by
      rw [← hmap]; exact Ideal.mem_map_of_mem _ hi
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hi'
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    have e : algebraMap R S (r * a) = algebraMap R S (↑s * i) := by
      rw [map_mul, map_mul, ← hy, ← IsLocalization.mk'_spec S r s]; ring
    obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) e
    exact ⟨↑d * ↑s, P.primeCompl.mul_mem d.2 s.2,
      Ideal.mem_span_singleton'.mpr ⟨↑d * r, by linear_combination hd⟩⟩

  have key2 : ∀ j ∈ LinearMap.ker (LinearMap.mulRight R a), ∃ d ∈ P.primeCompl, d * j = 0 := by
    intro j hj
    rw [LinearMap.mem_ker, LinearMap.mulRight_apply] at hj
    have h1 : algebraMap R S j * algebraMap R S a = 0 := by rw [← map_mul, hj, map_zero]
    have h2 : algebraMap R S j = algebraMap R S 0 := by
      rw [map_zero]
      first
      | exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hnzd).mp h1
      | exact (mul_cancel_right_mem_nonZeroDivisors hnzd).mp (by rw [zero_mul]; exact h1)
      | exact (mem_nonZeroDivisors_iff.mp hnzd).1 _ h1
      | exact mem_nonZeroDivisors_iff.mp hnzd _ h1
      | exact hnzd.1 _ h1
      | exact hnzd _ h1
    obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) h2
    exact ⟨d, d.2, by rw [hd, mul_zero]⟩
  choose! cI hcP hcA using key
  choose! dJ hdP hdA using key2
  have memI : ∀ i ∈ sI, i ∈ I := fun i hi => by
    rw [← hsI]; exact Submodule.subset_span (Finset.mem_coe.mpr hi)
  have memJ : ∀ j ∈ sJ, j ∈ LinearMap.ker (LinearMap.mulRight R a) := fun j hj => by
    rw [← hsJ]; exact Submodule.subset_span (Finset.mem_coe.mpr hj)
  obtain ⟨C, hC⟩ : ∃ C : R, C = ∏ i ∈ sI, cI i := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : R, D = ∏ j ∈ sJ, dJ j := ⟨_, rfl⟩
  have hCP : C ∈ P.primeCompl := by
    rw [hC]; exact prod_mem fun i hi => hcP i (memI i hi)
  have hDP : D ∈ P.primeCompl := by
    rw [hD]; exact prod_mem fun j hj => hdP j (memJ j hj)
  have hDk : ∀ x ∈ LinearMap.ker (LinearMap.mulRight R a), D * x = 0 := by
    have hle : LinearMap.ker (LinearMap.mulRight R a) ≤ LinearMap.ker (LinearMap.mulLeft R D) := by
      rw [← hsJ, Submodule.span_le]
      intro j hj
      have hj' : j ∈ sJ := Finset.mem_coe.mp hj
      have hj0 : dJ j * j = 0 := hdA j (memJ j hj')
      obtain ⟨e, he⟩ : dJ j ∣ D := by rw [hD]; exact Finset.dvd_prod_of_mem dJ hj'
      show j ∈ LinearMap.ker (LinearMap.mulLeft R D)
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, he]
      linear_combination e * hj0
    intro x hx
    have hx' := hle hx
    rwa [LinearMap.mem_ker, LinearMap.mulLeft_apply] at hx'
  refine ⟨C * D, P.primeCompl.mul_mem hCP hDP, ?_⟩
  intro T _ _ _
  have hunit : IsUnit (algebraMap R T (C * D)) :=
    IsLocalization.map_units T (⟨C * D, Submonoid.mem_powers _⟩ : Submonoid.powers (C * D))
  constructor
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, ← hsI, Submodule.span_le]
      intro i hi
      have hi' : i ∈ sI := Finset.mem_coe.mp hi
      have hcu : IsUnit (algebraMap R T (cI i)) := by
        refine isUnit_of_dvd_unit (map_dvd _ ?_) hunit
        rw [hC]; exact (Finset.dvd_prod_of_mem cI hi').trans (dvd_mul_right _ _)
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hcA i (memI i hi'))
      have e1 : algebraMap R T (cI i) * algebraMap R T i =
          algebraMap R T r * algebraMap R T a := by
        rw [← map_mul, ← map_mul, hr]
      show algebraMap R T i ∈ Ideal.span {algebraMap R T a}
      refine Ideal.mem_span_singleton'.mpr ⟨↑hcu.unit⁻¹ * algebraMap R T r, ?_⟩
      apply hcu.mul_left_cancel
      linear_combination (algebraMap R T r * algebraMap R T a) * hcu.mul_val_inv - e1
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_map_of_mem _ ha))
  · have H : ∀ z : T, z * algebraMap R T a = 0 → z = 0 := by
      intro z hz
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (C * D)) z
      have e1 : algebraMap R T (r * a) = algebraMap R T 0 := by
        rw [map_zero, map_mul, ← IsLocalization.mk'_spec T r s]
        linear_combination (algebraMap R T ↑s) * hz
      obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
        IsLocalization.exists_of_eq (M := Submonoid.powers (C * D)) e1
      have hk' : (C * D) ^ k * (r * a) = 0 := hk.trans (mul_zero _)
      have hmem : (C * D) ^ k * r ∈ LinearMap.ker (LinearMap.mulRight R a) := by
        rw [LinearMap.mem_ker, LinearMap.mulRight_apply, mul_assoc]; exact hk'
      have h0 := hDk _ hmem
      rw [IsLocalization.mk'_eq_zero_iff]
      refine ⟨⟨(C * D) ^ (k + 1), k + 1, rfl⟩, ?_⟩
      show (C * D) ^ (k + 1) * r = 0
      linear_combination C * h0
    first
    | exact mem_nonZeroDivisors_iff.mpr H
    | exact mem_nonZeroDivisors_iff_right.mpr H
    | exact mem_nonZeroDivisors_iff.mpr ⟨H, fun z hz => H z (by rw [mul_comm]; exact hz)⟩
    | exact ⟨H, fun z hz => H z (by rw [mul_comm]; exact hz)⟩
    | exact H
end ReciprocityTheory.AnForm.R
