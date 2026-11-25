-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.wa_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:31:23.721087+00:00
-- url     : https://prove2.me/submissions/91142fbb-d036-4fe7-80e2-008a8230269a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_exists_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_ne_zero_of_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_zpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open Filter
section WeakApproxAux
variable {F : Type*} [Field F]
private theorem exists_pos_neg_valuation (A B : AddValuation F (WithTop ℤ)) {z x : F} {a b m n : ℤ}
    (hza : A z = a) (hzb : B z = b) (hxa : A x = m) (hxb : B x = n) (ha : 0 < a) (hm : 0 ≤ m)
    (hn : n < 0) : ∃ y : F, ∃ c d : ℤ, A y = c ∧ B y = d ∧ 0 < c ∧ d < 0 := by
  refine ⟨z * x ^ (b.toNat + 1), _, _, wa_mul A hza (wa_pow A hxa _),
    wa_mul B hzb (wa_pow B hxb _), ?_, ?_⟩
  · have h1 : (0 : ℤ) ≤ ((b.toNat + 1 : ℕ) : ℤ) * m := mul_nonneg (by positivity) hm
    linarith
  · have h1 := Int.self_le_toNat b
    have h2 : (0 : ℤ) ≤ ((b.toNat + 1 : ℕ) : ℤ) * (-1 - n) := mul_nonneg (by positivity) (by omega)
    have h3 : ((b.toNat + 1 : ℕ) : ℤ) = (b.toNat : ℤ) + 1 := Nat.cast_succ b.toNat
    nlinarith
end WeakApproxAux
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Filter
variable {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (v w : AddValuation F (WithTop ℤ)) (hv : ∀ a : F, a ≠ 0 → v a ≠ ⊤)
    (hw : ∀ a : F, a ≠ 0 → w a ≠ ⊤) (hv1 : ∃ π : F, v π = 1) (hw1 : ∃ ρ : F, w ρ = 1)
    (h : ∀ a, 0 < v a → 0 ≤ w a) : v = w := by
  obtain ⟨q, hq⟩ := hv1
  obtain ⟨q', hq'⟩ := hw1
  have hq1 : v q = ((1 : ℤ) : WithTop ℤ) := by rw [WithTop.coe_one]; exact hq
  have hq1' : w q' = ((1 : ℤ) : WithTop ℤ) := by rw [WithTop.coe_one]; exact hq'
  have hq0 : q ≠ 0 := wa_ne_zero_of_coe v hq1
  have hq0' : q' ≠ 0 := wa_ne_zero_of_coe w hq1'
  obtain ⟨p, hp⟩ := wa_exists_coe w hw hq0
  obtain ⟨r, hr⟩ := wa_exists_coe v hv hq0'
  have key : ∀ x : F, ∀ m n : ℤ, v x = m → w x = n → (0 ≤ m ↔ 0 ≤ n) := by
    intro x m n hm hn
    constructor
    · intro hm0
      by_contra hn0
      push_neg at hn0
      obtain ⟨y, c, d, hc, hd, hc0, hd0⟩ := exists_pos_neg_valuation v w hq1 hp hm hn one_pos hm0 hn0
      have hy := h y (by rw [hc, ← WithTop.coe_zero, WithTop.coe_lt_coe]; exact hc0)
      rw [hd, ← WithTop.coe_zero, WithTop.coe_le_coe] at hy
      omega
    · intro hn0
      by_contra hm0
      push_neg at hm0
      obtain ⟨y, c, d, hc, hd, hc0, hd0⟩ := exists_pos_neg_valuation w v hq1' hr hn hm one_pos hn0 hm0
      have hy := h y⁻¹ (by rw [wa_inv v hd, ← WithTop.coe_zero, WithTop.coe_lt_coe]; omega)
      rw [wa_inv w hc, ← WithTop.coe_zero, WithTop.coe_le_coe] at hy
      omega
  have hunit : ∀ t : F, ∀ d : ℤ, v t = ((0 : ℤ) : WithTop ℤ) → w t = d → d = 0 := by
    intro t d hv0 hwd
    have h1 := (key t 0 d hv0 hwd).mp le_rfl
    have h2 := (key t⁻¹ (-0) (-d) (wa_inv v hv0) (wa_inv w hwd)).mp (by norm_num)
    omega
  have hmul : ∀ x : F, ∀ m n : ℤ, v x = m → w x = n → n = m * p := by
    intro x m n hm hn
    have hv0 := wa_div v hm (wa_zpow v hq1 m)
    have hw0 := wa_div w hn (wa_zpow w hp m)
    have h1 := hunit _ _ (by rw [hv0]; congr 1; ring) hw0
    linarith
  have hp1 : p = 1 := by
    have h1 := hmul q' r 1 hr hq1'
    have h2 := (key q 1 p hq1 hp).mp zero_le_one
    have h3 := (key q' r 1 hr hq1').mpr zero_le_one
    have h4 : p ≠ 0 := by rintro rfl; simp at h1
    have h5 : r ≠ 0 := by rintro rfl; simp at h1
    have h6 : 1 ≤ p := by omega
    have h7 : 1 ≤ r := by omega
    nlinarith
  refine AddValuation.ext fun x => ?_
  by_cases hx : x = 0
  · rw [hx, AddValuation.map_zero, AddValuation.map_zero]
  · obtain ⟨m, hm⟩ := wa_exists_coe v hv hx
    obtain ⟨n, hn⟩ := wa_exists_coe w hw hx
    rw [hm, hn, hmul x m n hm hn, hp1, mul_one]
end ReciprocityTheory.ChartRestriction.G.T0
