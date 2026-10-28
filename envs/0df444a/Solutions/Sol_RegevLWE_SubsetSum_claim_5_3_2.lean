-- Prove2me | solution 2 for RegevLWE.SubsetSum.claim_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:47:52.103262+00:00
-- url     : https://prove2.me/submissions/0e7306f7-53fd-495f-82ba-385223c7db68

import Mathlib
import Definitions.Def_RegevLWE_SubsetSum_Basic
import Theorems.Thm_RegevLWE_SubsetSum_cauchy_schwarz_l2
import Theorems.Thm_RegevLWE_SubsetSum_expected_l2_norm

-- carved verbatim out of submission 453d4604-60d7-4a22-9c4a-6333bf02513f, lines 187-280

section
set_option autoImplicit false
open Finset hiding subsetSum
open RegevLWE.SubsetSum

theorem solution {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (l : ℕ) :
    expectG (fun g : Fin l → G => statDistUniform g) ≤
        Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l) ∧
      ((univ.filter fun g : Fin l → G =>
            Real.sqrt (Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l)) < statDistUniform g).card : ℝ) /
          (Fintype.card G : ℝ) ^ l ≤
        Real.sqrt (Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l)) := by
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) < (Fintype.card G : ℝ) ^ l := pow_pos hN l
  have h2l : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have hx : ∀ g : Fin l → G, 0 ≤ ∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ) := fun g => by
    rw [← (RegevLWE.SubsetSum.cauchy_schwarz_l2 g).2]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hΔ : ∀ g : Fin l → G, statDistUniform g ≤
      Real.sqrt (Fintype.card G) * Real.sqrt (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ)) :=
    fun g => by
      have := RegevLWE.SubsetSum.cauchy_schwarz_l2 g
      rw [this.2] at this
      exact this.1
  have hΔ0 : ∀ g : Fin l → G, 0 ≤ statDistUniform g := fun g =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hEl := RegevLWE.SubsetSum.expected_l2_norm (G := G) l
  unfold expectG at hEl ⊢
  have hsumS : ∑ g : Fin l → G, ∑ h, P g h ^ 2 ≤
      (Fintype.card G : ℝ) ^ l * (1 / (2 : ℝ) ^ l + 1 / (Fintype.card G : ℝ)) :=
    by rw [mul_comm]; exact (div_le_iff₀ hM).1 hEl
  have hcard : ((Finset.univ : Finset (Fin l → G)).card : ℝ) = (Fintype.card G : ℝ) ^ l := by
    simp
  have hsumx : ∑ g : Fin l → G, (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ)) ≤
      (Fintype.card G : ℝ) ^ l / (2 : ℝ) ^ l := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    have : (Fintype.card G : ℝ) ^ l / (2 : ℝ) ^ l =
        (Fintype.card G : ℝ) ^ l * (1 / (2 : ℝ) ^ l + 1 / (Fintype.card G : ℝ)) -
          (Fintype.card G : ℝ) ^ l * (1 / (Fintype.card G : ℝ)) := by ring
    rw [this]
    linarith
  have hsq : (∑ g : Fin l → G, statDistUniform g) ^ 2 ≤
      (Fintype.card G : ℝ) * (Fintype.card G : ℝ) ^ l * ((Fintype.card G : ℝ) ^ l / (2 : ℝ) ^ l) := by
    calc (∑ g : Fin l → G, statDistUniform g) ^ 2
        ≤ (∑ g : Fin l → G, Real.sqrt (Fintype.card G) *
            Real.sqrt (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun g _ => hΔ0 g)
            (Finset.sum_le_sum fun g _ => hΔ g) 2
      _ = (Fintype.card G : ℝ) *
            (∑ g : Fin l → G, Real.sqrt (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ))) ^ 2 := by
          rw [← Finset.mul_sum, mul_pow, Real.sq_sqrt hN.le]
      _ ≤ (Fintype.card G : ℝ) * ((∑ g : Fin l → G, (1 : ℝ) ^ 2) *
            ∑ g : Fin l → G, Real.sqrt (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ)) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hN.le
          have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin l → G))
            (fun _ => (1 : ℝ)) (fun g => Real.sqrt (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ)))
          simpa using this
      _ ≤ (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) ^ l *
            ((Fintype.card G : ℝ) ^ l / (2 : ℝ) ^ l)) := by
          apply mul_le_mul_of_nonneg_left _ hN.le
          have e1 : ∑ g : Fin l → G, (1 : ℝ) ^ 2 = (Fintype.card G : ℝ) ^ l := by simp
          have e2 : ∑ g : Fin l → G,
              Real.sqrt (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ)) ^ 2 =
              ∑ g : Fin l → G, (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ)) :=
            Finset.sum_congr rfl fun g _ => Real.sq_sqrt (hx g)
          rw [e1, e2]
          exact mul_le_mul_of_nonneg_left hsumx hM.le
      _ = _ := by ring
  have hE : (∑ g : Fin l → G, statDistUniform g) ≤
      (Fintype.card G : ℝ) ^ l * Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l) := by
    have hnn : 0 ≤ (∑ g : Fin l → G, statDistUniform g) :=
      Finset.sum_nonneg fun g _ => hΔ0 g
    have : (∑ g : Fin l → G, statDistUniform g) ≤
        Real.sqrt (((Fintype.card G : ℝ) ^ l) ^ 2 * ((Fintype.card G : ℝ) / 2 ^ l)) := by
      apply le_trans (le_abs_self _) (Real.abs_le_sqrt _)
      calc _ ≤ _ := hsq
        _ = _ := by ring
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq hM.le] at this
  constructor
  · rw [div_le_iff₀ hM, mul_comm]
    exact hE
  · set t := Real.sqrt (Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l)) with ht
    have hq : 0 < (Fintype.card G : ℝ) / 2 ^ l := by positivity
    have htpos : 0 < t := Real.sqrt_pos.2 (Real.sqrt_pos.2 hq)
    have ht2 : t ^ 2 = Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have hcnt : ((univ.filter fun g : Fin l → G => t < statDistUniform g).card : ℝ) * t ≤
        ∑ g : Fin l → G, statDistUniform g := by
      have h1 := Finset.card_nsmul_le_sum (univ.filter fun g : Fin l → G => t < statDistUniform g)
        (fun g => statDistUniform g) t (fun g hg => (Finset.mem_filter.1 hg).2.le)
      rw [nsmul_eq_mul] at h1
      exact h1.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun g _ _ => hΔ0 g))
    rw [div_le_iff₀ hM]
    have : ((univ.filter fun g : Fin l → G => t < statDistUniform g).card : ℝ) * t ≤
        (Fintype.card G : ℝ) ^ l * t ^ 2 := by rw [ht2]; exact hcnt.trans hE
    have h3 : ((univ.filter fun g : Fin l → G => t < statDistUniform g).card : ℝ) * t ≤
        (t * (Fintype.card G : ℝ) ^ l) * t := by nlinarith [this]
    exact le_of_mul_le_mul_right h3 htpos

end
