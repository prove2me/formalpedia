-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_nonneg_of_poly_bf85d1564919
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:21:07.466455+00:00
-- url     : https://prove2.me/submissions/03a2142e-1349-41e0-823c-57867b07a052

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {e : ℕ} (c : Finset (Fin e) → ℤ)
    (h : ∀ q : ℕ, 1 ≤ q → 0 ≤ ∑ S : Finset (Fin e), (q : ℤ) ^ Sᶜ.card * c S) : 0 ≤ c ∅ := by
  by_contra hneg
  push Not at hneg
  set C : ℤ := ∑ S ∈ Finset.univ.erase ∅, |c S| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = C + 1 := ⟨(C + 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hq1 : 1 ≤ q := by omega
  have hsum := h q hq1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ∅)] at hsum
  have hcard : (∅ : Finset (Fin e))ᶜ.card = e := by simp
  rw [hcard] at hsum
  have hrest : ∑ S ∈ Finset.univ.erase ∅, (q : ℤ) ^ Sᶜ.card * c S ≤ (q : ℤ) ^ (e - 1) * C := by
    rw [hC, Finset.mul_sum]
    refine Finset.sum_le_sum fun S hS => ?_
    have hSne : S ≠ ∅ := Finset.ne_of_mem_erase hS
    have hcardS : Sᶜ.card ≤ e - 1 := by
      rw [Finset.card_compl, Fintype.card_fin]
      have := (Finset.nonempty_iff_ne_empty.mpr hSne).card_pos
      have := Finset.card_le_univ S
      rw [Fintype.card_fin] at this
      omega
    calc (q : ℤ) ^ Sᶜ.card * c S ≤ (q : ℤ) ^ Sᶜ.card * |c S| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ ≤ (q : ℤ) ^ (e - 1) * |c S| :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast hq1) hcardS) (abs_nonneg _)
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    have hC' : C = 0 := Finset.sum_eq_zero fun S hS =>
      absurd (Finset.eq_empty_of_isEmpty S) (Finset.ne_of_mem_erase hS)
    rw [hC'] at hrest
    simp only [pow_zero, one_mul, mul_zero] at hsum hrest
    linarith
  · have hpow : (q : ℤ) ^ e = q * (q : ℤ) ^ (e - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hpos : 0 < (q : ℤ) ^ (e - 1) := by positivity
    rw [hpow] at hsum
    set P : ℤ := (q : ℤ) ^ (e - 1) with hP
    have h1 : (q : ℤ) * P * c ∅ ≤ -((q : ℤ) * P) := by
      have : 0 < (q : ℤ) * P := by positivity
      nlinarith
    have h2 : (q : ℤ) * P = C * P + P := by rw [hq]; ring
    linarith
end GroundTheory.Heights₂.Heights.Kleiman
