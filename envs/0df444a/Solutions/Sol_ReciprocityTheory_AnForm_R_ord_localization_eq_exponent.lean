-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ord_localization_eq_exponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:37.152799+00:00
-- url     : https://prove2.me/submissions/a5a42c3d-9572-4825-ae2f-22b7c5b6c30e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Theorems.Thm_ReciprocityTheory_AnForm_R_prime_of_regular_params
import Theorems.Thm_ReciprocityTheory_AnForm_R_isDomain_of_isRegularLocalRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_regular_params_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open IsLocalRing
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) (u : Rˣ) (m : Fin n → ℕ) (i : Fin n) (hi : i ∈ J)
    [(Ideal.span {f i}).IsPrime] :
    Ring.ord (Localization.AtPrime (Ideal.span {f i}))
        (algebraMap R (Localization.AtPrime (Ideal.span {f i})) (u * ∏ j ∈ J, f j ^ m j)) =
      (m i : ℕ∞) := by
  have : IsDomain R := isDomain_of_isRegularLocalRing
  set P := Ideal.span {f i} with hP
  set S := Localization.AtPrime P
  have hpr : ∀ j, Prime (f j) := prime_of_regular_params f hspan hdim

  have hout : ∀ j, j ≠ i → f j ∉ P := by
    intro j hji hj
    rw [hP, Ideal.mem_span_singleton] at hj
    obtain ⟨c, hc⟩ := hj
    have hdc : f j ∣ f i * c := ⟨1, by rw [mul_one, hc]⟩
    rcases (hpr j).dvd_or_dvd hdc with h | h
    · exact (regular_params_spec f hspan hdim).2 j i hji
        (associated_of_dvd_dvd h ⟨c, hc⟩)
    · obtain ⟨d, rfl⟩ := h
      have : f j * 1 = f j * (f i * d) := by linear_combination hc
      have h1 := mul_left_cancel₀ (hpr j).ne_zero this
      exact (hpr i).not_isUnit (isUnit_of_dvd_one ⟨d, h1⟩)
  have hunit : ∀ j, j ≠ i → IsUnit (algebraMap R S (f j)) := fun j hj =>
    IsLocalization.map_units S (⟨f j, hout j hj⟩ : P.primeCompl)
  set π := algebraMap R S (f i)
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors P)
  have hπ0 : π ≠ 0 := fun h => (hpr i).ne_zero (hinj (by rw [map_zero]; exact h))
  have hπnzd : π ∈ nonZeroDivisors S := mem_nonZeroDivisors_of_ne_zero hπ0
  have hmax : Ideal.span {π} = maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    show Ideal.span {π} = Ideal.map (algebraMap R S) (Ideal.span {f i})
    rw [Ideal.map_span, Set.image_singleton]
  have hord1 : Ring.ord S π = 1 := by
    unfold Ring.ord
    rw [hmax, Module.length_eq_one_iff]
    exact isSimpleModule_iff_isCoatom.mpr
      (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal S))
  rw [← Finset.mul_prod_erase J _ hi, map_mul, map_mul, map_pow,
    Ring.ord_mul_of_isUnit_left ((Units.isUnit u).map _)]
  have hrest : IsUnit (algebraMap R S (∏ j ∈ J.erase i, f j ^ m j)) := by
    rw [map_prod]
    exact IsUnit.prod_iff.mpr fun j hj => by
      rw [map_pow]; exact (hunit j (Finset.ne_of_mem_erase hj)).pow _
  rw [Ring.ord_mul_of_isUnit_right hrest, Ring.ord_pow hπnzd, hord1, nsmul_eq_mul, mul_one]
end ReciprocityTheory.AnForm.R
