-- Prove2me | solution 1 for PI.LocDualGen.EpC.dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:57:00.110904+00:00
-- url     : https://prove2.me/submissions/20206cd4-12a0-4fad-9699-dc578c470727

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualCase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Module
namespace PI.LocDualGen.EpC
variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]
private theorem nontrivial_of_finrank_eq_two (hr : finrank K L = 2) : Nontrivial L := by
  rcases subsingleton_or_nontrivial L with h | h
  · rw [Module.finrank_zero_of_subsingleton] at hr
    exact absurd hr (by norm_num)
  · exact h
private theorem exists_not_mem_range_algebraMap_of_finrank_eq_two (hr : finrank K L = 2) :
    ∃ x : L, x ∉ Set.range (algebraMap K L) := by
  by_contra h
  push Not at h
  have hsurj : LinearMap.range (Algebra.linearMap K L) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨a, ha⟩ := h y
    exact ⟨a, ha⟩
  have h1 := LinearMap.finrank_range_le (Algebra.linearMap K L)
  rw [hsurj, finrank_top, Module.finrank_self, hr] at h1
  omega
private theorem exists_eq_add_mul_of_finrank_eq_two' (hr : finrank K L = 2) {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) (y : L) :
    ∃ a c : K, algebraMap K L a + algebraMap K L c * x = y := by
  have := nontrivial_of_finrank_eq_two hr
  have hli : LinearIndependent K ![(1 : L), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      refine ⟨?_, rfl⟩
      have h0 : algebraMap K L s = 0 := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact hst
      exact (algebraMap K L).injective (by rw [h0, map_zero])
    · exfalso
      apply hx
      refine ⟨-(s / t), ?_⟩
      have h2 : t • x = -(s • (1 : L)) := by
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
        exact hst
      have h3 : x = t⁻¹ • (t • x) := by
        rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [Algebra.algebraMap_eq_smul_one, h3, h2, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hcard : Fintype.card (Fin 2) = finrank K L := by
    rw [hr, Fintype.card_fin]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = x := by simp [b]
  have hy := b.sum_repr y
  rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one] at hy
  exact ⟨b.repr y 0, b.repr y 1, hy⟩
end PI.LocDualGen.EpC
end
end

set_option autoImplicit false
noncomputable section
open Module
open PI PI.LocDualGen PI.LocDualGen.EpC
variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]
namespace PI.LocDualGen.EpC
theorem _root_.solution (hr : finrank K L = 2) (hred : IsReduced L) :
    IsField L ∨ ∃ e : L, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  have := nontrivial_of_finrank_eq_two hr
  obtain ⟨x, hx⟩ := exists_not_mem_range_algebraMap_of_finrank_eq_two hr
  have hrep := exists_eq_add_mul_of_finrank_eq_two' hr hx
  obtain ⟨p, q, hpq0⟩ := hrep (x ^ 2)
  have hpq : x ^ 2 = algebraMap K L p + algebraMap K L q * x := hpq0.symm
  by_cases hroot : ∃ r : K, r ^ 2 = p + q * r
  · obtain ⟨r, hr2⟩ := hroot
    have hfac : (x - algebraMap K L r) * (x - algebraMap K L (q - r)) = 0 := by
      have h' : algebraMap K L (r ^ 2) = algebraMap K L (p + q * r) := by rw [hr2]
      simp only [map_add, map_mul, map_pow, map_sub] at h' ⊢
      linear_combination hpq - h'
    by_cases hrs : r = q - r
    · exfalso
      have hsq : (x - algebraMap K L r) ^ 2 = 0 := by
        have h' := hfac
        rw [← hrs] at h'
        rw [sq]
        exact h'
      have hz : x - algebraMap K L r = 0 := hred.eq_zero _ ⟨2, hsq⟩
      exact hx ⟨r, (sub_eq_zero.mp hz).symm⟩
    · right
      have hd : q - r - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
      have hsq : (x - algebraMap K L r) * (x - algebraMap K L r) =
          algebraMap K L (q - r - r) * (x - algebraMap K L r) := by
        have h' := hfac
        simp only [map_sub] at h' ⊢
        linear_combination h'
      have hu : algebraMap K L (q - r - r)⁻¹ * algebraMap K L (q - r - r) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hd, map_one]
      have hback : x - algebraMap K L r = algebraMap K L (q - r - r) *
          (algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r)) := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd, map_one, one_mul]
      refine ⟨algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r), ?_, ?_, ?_⟩
      · show _ * _ = _
        linear_combination (algebraMap K L (q - r - r)⁻¹) ^ 2 * hsq +
          algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r) * hu
      · intro he
        rw [he, mul_zero, sub_eq_zero] at hback
        exact hx ⟨r, hback.symm⟩
      · intro he
        rw [he, mul_one] at hback
        apply hx
        refine ⟨q - r, ?_⟩
        simp only [map_sub] at hback ⊢
        linear_combination -hback
  · push Not at hroot
    left
    refine ⟨⟨0, 1, zero_ne_one⟩, fun a b => mul_comm a b, ?_⟩
    intro y hy
    obtain ⟨a, c, rfl⟩ := hrep y
    have hN : a * a + a * c * q - c ^ 2 * p ≠ 0 := by
      intro h0
      by_cases hc : c = 0
      · subst hc
        apply hy
        have ha : a = 0 := by simpa using h0
        simp [ha]
      · apply hroot (-a / c)
        have hci : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
        linear_combination (c⁻¹) ^ 2 * h0 + (p * (1 + c * c⁻¹) - q * a * c⁻¹) * hci
    have hprod : (algebraMap K L a + algebraMap K L c * x) *
        (algebraMap K L (a + c * q) - algebraMap K L c * x) =
        algebraMap K L (a * a + a * c * q - c ^ 2 * p) := by
      simp only [map_add, map_mul, map_sub, map_pow]
      linear_combination (-(algebraMap K L c) ^ 2) * hpq
    refine ⟨algebraMap K L (a * a + a * c * q - c ^ 2 * p)⁻¹ *
      (algebraMap K L (a + c * q) - algebraMap K L c * x), ?_⟩
    rw [mul_left_comm, hprod, ← map_mul, inv_mul_cancel₀ hN, map_one]
end PI.LocDualGen.EpC
