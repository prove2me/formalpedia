-- Prove2me | solution 1 for SuperBAE.Restriction.specialization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:40:54.155545+00:00
-- url     : https://prove2.me/submissions/1be36822-ae43-4ed8-b0d8-a81e98410950

import Mathlib
import Definitions.Def_SuperBAE_Restriction_Model

namespace Aux_SuperBAE_spec

theorem sign_iff (a b t r : ℂ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    (t = -(a * b) * r ↔ a / b * t = -r) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    constructor <;> intro h <;> norm_num at h ⊢ <;>
    first
    | exact h
    | linear_combination h
    | linear_combination -h
    | (rw [h]; ring)
    | (rw [← h]; ring)

end Aux_SuperBAE_spec

open SuperBAE.Restriction Aux_SuperBAE_spec in
theorem solution (L : ℕ) (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) (k : ℕ)
    (hA1 : odd k ≠ odd (k + 1)) (hA2k : 2 ≤ k) (hA2d : k + 2 ≤ d)
    (hn : numOdd odd d < numEven odd d)
    (hreg : Regular L odd d roots) :
    lam L odd d k = lam L odd d (k + 1) ∧ sgn odd (k + 1) = -sgn odd k ∧
      (∀ u ∈ roots (k - 1), bae L odd d roots (k - 1) u ↔ eq4_2 L odd d roots k u) ∧
      (∀ u ∈ roots k, bae L odd d roots k u ↔ eq4_3 d odd roots k u) ∧
      (∀ u ∈ roots (k + 1), bae L odd d roots (k + 1) u ↔ eq4_4 L odd d roots k u) := by
  have hsgn : ∀ j, sgn odd j = 1 ∨ sgn odd j = -1 := by
    intro j; unfold sgn; split_ifs <;> simp
  have hlam : lam L odd d k = lam L odd d (k + 1) := by
    funext u
    unfold lam
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hs1 : sgn odd (k + 1) = -sgn odd k := by
    unfold sgn
    cases h1 : odd k <;> cases h2 : odd (k + 1) <;> simp_all
  refine ⟨hlam, hs1, ?_, ?_, ?_⟩
  · intro u _
    unfold bae eq4_2
    rw [show k - 1 + 1 = k by omega, show k - 1 - 1 = k - 2 by omega]
    rcases hsgn (k - 1) with ha | ha <;> rcases hsgn k with hb | hb <;> simp only [ha, hb] <;>
      constructor <;> intro h <;>
      first
      | linear_combination h
      | linear_combination -h
  · intro u hu
    have hk : k ∈ Finset.Icc 1 (d - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    obtain ⟨hl1, _, _, hQk, _⟩ := hreg k hk u hu
    unfold bae eq4_3
    have hss : -(sgn odd k * -sgn odd k) = 1 := by
      rcases hsgn k with h | h <;> rw [h] <;> norm_num
    rw [← hlam, div_self hl1, hs1, ← sub_eq_add_neg, sub_neg_eq_add, hss, one_mul]
    have e : Q d roots (k - 1) u * Q d roots k (u - sgn odd k) * Q d roots (k + 1) (u + sgn odd k) /
        (Q d roots (k - 1) (u + sgn odd k) * Q d roots k (u - sgn odd k) * Q d roots (k + 1) u) =
        Q d roots (k - 1) u * Q d roots (k + 1) (u + sgn odd k) /
        (Q d roots (k - 1) (u + sgn odd k) * Q d roots (k + 1) u) := by
      rw [show Q d roots (k - 1) u * Q d roots k (u - sgn odd k) * Q d roots (k + 1) (u + sgn odd k)
          = (Q d roots (k - 1) u * Q d roots (k + 1) (u + sgn odd k)) * Q d roots k (u - sgn odd k)
          by ring,
        show Q d roots (k - 1) (u + sgn odd k) * Q d roots k (u - sgn odd k) * Q d roots (k + 1) u
          = (Q d roots (k - 1) (u + sgn odd k) * Q d roots (k + 1) u) * Q d roots k (u - sgn odd k)
          by ring]
      exact mul_div_mul_right _ _ hQk
    rw [e]
  · intro u _
    unfold bae eq4_4
    rw [show k + 1 - 1 = k by omega, show k + 1 + 1 = k + 2 by omega, hs1,
      ← sub_eq_add_neg, sub_neg_eq_add]
    rcases hsgn k with ha | ha <;> rcases hsgn (k + 2) with hb | hb <;> simp only [ha, hb] <;>
      constructor <;> intro h <;>
      first
      | linear_combination h
      | linear_combination -h
