-- Prove2me | solution 1 for SumProduct.boxAdd_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:53:38.76898+00:00
-- url     : https://prove2.me/submissions/bc556f3e-f819-4656-94e3-2bc9ac3a6574

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
import Theorems.Thm_SumProduct_abs_realEmbed
import Theorems.Thm_SumProduct_exists_coord_dist_ge_one
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult



set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open MeasureTheory NumberField NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) (X : ℝ) (hX : 0 ≤ X) :
    ((boxAdd K X).card : ℝ) ≤ (2 * X + 1) ^ d := by
  classical
  have hcard : Fintype.card (InfinitePlace K) = d := by
    have h0 : nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (K := K)
    have hc := card_eq_nrRealPlaces_add_nrComplexPlaces K
    have hr := card_add_two_mul_card_eq_rank K
    rw [hd] at hr; omega
  set C : 𝓞 K → Set (InfinitePlace K → ℝ) :=
    fun α => Set.univ.pi fun w => Set.Ioo (realEmbed K α w - 1 / 2) (realEmbed K α w + 1 / 2)
    with hC
  have hmeas : ∀ α, MeasurableSet (C α) :=
    fun α => MeasurableSet.pi Set.countable_univ fun w _ => measurableSet_Ioo
  have hvolC : ∀ α, volume (C α) = 1 := fun α => by
    rw [hC]; simp only; rw [volume_pi_pi]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [Real.volume_Ioo, show realEmbed K α w + 1 / 2 - (realEmbed K α w - 1 / 2) = (1 : ℝ) by ring,
      ENNReal.ofReal_one]
  have hdisj : (↑(boxAdd K X) : Set (𝓞 K)).PairwiseDisjoint C := by
    intro α _ β _ hab
    obtain ⟨w, hw⟩ := exists_coord_dist_ge_one hab
    simp only [Function.onFun, hC]
    rw [Set.disjoint_univ_pi]
    refine ⟨w, Set.disjoint_left.mpr fun x hx hx' => ?_⟩
    rw [Set.mem_Ioo] at hx hx'
    have : |realEmbed K α w - realEmbed K β w| < 1 := by
      rw [abs_lt]; constructor <;> linarith [hx.1, hx.2, hx'.1, hx'.2]
    linarith
  have hsub : (⋃ α ∈ boxAdd K X, C α) ⊆
      Set.univ.pi fun _ : InfinitePlace K => Set.Ioo (-X - 1 / 2) (X + 1 / 2) := by
    intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨α, hα, hxα⟩ := hx
    rw [hC] at hxα; simp only at hxα
    rw [Set.mem_univ_pi] at hxα ⊢
    intro w
    have hax := hxα w
    rw [Set.mem_Ioo] at hax ⊢
    have habs : |realEmbed K α w| ≤ X := by rw [abs_realEmbed]; exact (mem_boxAdd.mp hα) w
    rw [abs_le] at habs
    constructor <;> linarith [hax.1, hax.2, habs.1, habs.2]
  have hboxvol : volume (Set.univ.pi fun _ : InfinitePlace K => Set.Ioo (-X - 1 / 2) (X + 1 / 2))
      = ENNReal.ofReal ((2 * X + 1) ^ d) := by
    rw [volume_pi_pi]
    have hone : ∀ w ∈ (Finset.univ : Finset (InfinitePlace K)),
        volume (Set.Ioo (-X - 1 / 2) (X + 1 / 2)) = ENNReal.ofReal (2 * X + 1) := by
      intro w _; rw [Real.volume_Ioo]; congr 1; ring
    rw [Finset.prod_congr rfl hone, Finset.prod_const, Finset.card_univ, hcard,
      ← ENNReal.ofReal_pow (by linarith)]
  have hsum : (↑(boxAdd K X).card : ENNReal) ≤ ENNReal.ofReal ((2 * X + 1) ^ d) := by
    rw [← hboxvol]
    calc (↑(boxAdd K X).card : ENNReal)
        = ∑ α ∈ boxAdd K X, volume (C α) := by
          rw [Finset.sum_congr rfl fun α _ => hvolC α, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = volume (⋃ α ∈ boxAdd K X, C α) :=
          (measure_biUnion_finset hdisj fun α _ => hmeas α).symm
      _ ≤ _ := measure_mono hsub
  have hconv := (ENNReal.toReal_le_toReal (by simp) (by simp)).mpr hsum
  rwa [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at hconv
end SumProduct
