-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P86.basedRingHom_preserves_bar
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T11:09:09.217005+00:00
-- url     : https://prove2.me/submissions/48674169-04ff-47aa-84c6-271d9ebbcd2d

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P86

set_option autoImplicit false



noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P86

/-- The identity coefficient of a basis element times its bar is one. -/
theorem basis_mul_bar_one_coefficient
    {A I : Type*} [Ring A] (H : IntegralHypergroup A I) (i : I) :
    H.basis.repr (H.basis i * H.bar (H.basis i)) H.oneIndex = 1 := by
  classical
  obtain ⟨j, hj⟩ := H.bar_basis i
  rw [hj, H.reciprocity, H.basis_one, one_mul, ← hj, H.bar_involutive]
  simp

/-- Positive identity coefficient identifies the unique bar partner. -/
theorem bar_basis_eq_of_one_coefficient_pos
    {A I : Type*} [Ring A] (H : IntegralHypergroup A I) (i j : I)
    (hpos : 0 < H.basis.repr (H.basis i * H.basis j) H.oneIndex) :
    H.bar (H.basis i) = H.basis j := by
  classical
  obtain ⟨l, hl⟩ := H.bar_basis j
  have hli : l = i := by
    by_contra hne
    have hz : H.basis.repr (H.basis i * H.basis j) H.oneIndex = 0 := by
      rw [H.reciprocity, H.basis_one, one_mul, hl]
      simp [hne]
    omega
  have hbar : H.bar (H.basis j) = H.basis i := by simpa [hli] using hl
  rw [← hbar, H.bar_involutive]

end QAlgorithms.Papers.Independent.Intake100.P86


open scoped BigOperators
open QAlgorithms.Papers.Independent.Intake100.P86

namespace S06P006

variable {A I A2 I2 : Type*} [Ring A] [Ring A2]
variable (H : IntegralHypergroup A I) (H2 : IntegralHypergroup A2 I2)
variable (f : BasedRingHom H H2)

lemma image_basis_coeff_nonneg (i : I) (j : I2) :
    0 ≤ H2.basis.repr (f.hom (H.basis i)) j := by
  classical
  rcases f.basis_image i with h | ⟨k, h⟩
  · simp [h]
  · rw [h, H2.basis.repr_self_apply]
    split_ifs <;> norm_num

lemma image_coeff_expansion (a : A) (j : I2) :
    H2.basis.repr (f.hom a) j =
      ∑ i ∈ (H.basis.repr a).support,
        H.basis.repr a i * H2.basis.repr (f.hom (H.basis i)) j := by
  classical
  have h := congrArg (fun x => H2.basis.repr (f.hom x) j)
    (H.basis.linearCombination_repr a)
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    Finsupp.finsetSum_apply, map_zsmul, Finsupp.smul_apply] at h
  simpa only [zsmul_eq_mul, Int.cast_id] using h.symm

lemma image_coeff_nonneg (a : A) (ha : ∀ i, 0 ≤ H.basis.repr a i) (j : I2) :
    0 ≤ H2.basis.repr (f.hom a) j := by
  classical
  rw [image_coeff_expansion H H2 f a j]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (ha i) (image_basis_coeff_nonneg H H2 f i j)

lemma coeff_one_le_image (a : A) (ha : ∀ i, 0 ≤ H.basis.repr a i) :
    H.basis.repr a H.oneIndex ≤ H2.basis.repr (f.hom a) H2.oneIndex := by
  classical
  rw [image_coeff_expansion H H2 f a H2.oneIndex]
  by_cases hm : H.oneIndex ∈ (H.basis.repr a).support
  · have h := Finset.single_le_sum
      (fun i (_ : i ∈ (H.basis.repr a).support) =>
        mul_nonneg (ha i) (image_basis_coeff_nonneg H H2 f i H2.oneIndex)) hm
    simpa only [H.basis_one, map_one, ← H2.basis_one,
      H2.basis.repr_self_apply, if_pos rfl, ite_true, mul_one] using h
  · have hz : H.basis.repr a H.oneIndex = 0 := Finsupp.notMem_support_iff.mp hm
    rw [hz]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (ha i) (image_basis_coeff_nonneg H H2 f i H2.oneIndex)

end S06P006

open QAlgorithms.Papers.Independent.Intake100.P86

namespace S06P006

lemma image_basis_mul_bar_positive
    {A I A2 I2 : Type*} [Ring A] [Ring A2]
    (H : IntegralHypergroup A I) (H2 : IntegralHypergroup A2 I2)
    (f : BasedRingHom H H2) (i : I) :
    0 < H2.basis.repr (f.hom (H.basis i * H.bar (H.basis i))) H2.oneIndex := by
  have hn : ∀ k, 0 ≤ H.basis.repr (H.basis i * H.bar (H.basis i)) k := by
    obtain ⟨j, hj⟩ := H.bar_basis i
    simpa only [hj] using H.nonnegative i j
  have hle := coeff_one_le_image H H2 f (H.basis i * H.bar (H.basis i)) hn
  rw [basis_mul_bar_one_coefficient] at hle
  omega

lemma basis_image_ne_zero
    {A I A2 I2 : Type*} [Ring A] [Ring A2]
    (H : IntegralHypergroup A I) (H2 : IntegralHypergroup A2 I2)
    (f : BasedRingHom H H2) (i : I) : f.hom (H.basis i) ≠ 0 := by
  intro hz
  have hp := image_basis_mul_bar_positive H H2 f i
  simp [map_mul, hz] at hp

lemma preserves_bar_basis
    {A I A2 I2 : Type*} [Ring A] [Ring A2]
    (H : IntegralHypergroup A I) (H2 : IntegralHypergroup A2 I2)
    (f : BasedRingHom H H2) (i : I) :
    f.hom (H.bar (H.basis i)) = H2.bar (f.hom (H.basis i)) := by
  obtain ⟨j, hj⟩ := H.bar_basis i
  obtain ⟨u, hu⟩ := (f.basis_image i).resolve_left (basis_image_ne_zero H H2 f i)
  obtain ⟨v, hv⟩ := (f.basis_image j).resolve_left (basis_image_ne_zero H H2 f j)
  have hp := image_basis_mul_bar_positive H H2 f i
  rw [hj, map_mul, hu, hv] at hp
  rw [hj, hu, hv]
  exact (bar_basis_eq_of_one_coefficient_pos H2 u v hp).symm

lemma extend_from_basis
    {A I A2 I2 : Type*} [Ring A] [Ring A2]
    (H : IntegralHypergroup A I) (H2 : IntegralHypergroup A2 I2)
    (f : BasedRingHom H H2)
    (h : ∀ i, f.hom (H.bar (H.basis i)) = H2.bar (f.hom (H.basis i))) :
    ∀ a : A, f.hom (H.bar a) = H2.bar (f.hom a) := by
  let fl : A →ₗ[ℤ] A2 := f.hom.toAddMonoidHom.toIntLinearMap
  have heq : fl.comp H.bar = H2.bar.comp fl := H.basis.ext h
  intro a
  exact LinearMap.congr_fun heq a

end S06P006

theorem solution
    {A I A2 I2 : Type*} [Ring A] [Ring A2]
    (H : IntegralHypergroup A I) (H2 : IntegralHypergroup A2 I2)
    (f : BasedRingHom H H2) :
    ∀ a : A, f.hom (H.bar a) = H2.bar (f.hom a) :=
  S06P006.extend_from_basis H H2 f (S06P006.preserves_bar_basis H H2 f)

#print axioms S06P006.basis_image_ne_zero
#print axioms solution
