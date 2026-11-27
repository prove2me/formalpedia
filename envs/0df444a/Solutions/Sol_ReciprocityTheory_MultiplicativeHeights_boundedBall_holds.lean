-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.boundedBall_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:24.86639+00:00
-- url     : https://prove2.me/submissions/2c355454-7070-45e1-ab4c-9b991d6d4afd

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallC
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBall
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_J_herm
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_J_mul_J
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_cs
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_dot_J
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_dot_split
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_herm_swap
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_negSq_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_normSq_nonneg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_normSq_split
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_posSq_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_re_dot_J
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_re_dot_comm
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_re_star_dot
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_real_bounds
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_setup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : BoundedBallStatement := by
  intro r p H s hH hJ hs0 hs1 hP u
  have hHh : Hᴴ = H := hH.isHermitian
  have hsurj := sb_setup hH hJ hP
  have hTT : ∀ v, signMat p r *ᵥ (H *ᵥ (signMat p r *ᵥ (H *ᵥ v))) = v := fun v => by
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc H, hJ, sb_J_mul_J, one_mulVec]
  have hHx : ∀ x, signMat p r *ᵥ (H *ᵥ x) = x → H *ᵥ x = signMat p r *ᵥ x := fun x hx => by
    calc H *ᵥ x = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ x)) := by
          rw [mulVec_mulVec, sb_J_mul_J, one_mulVec]
      _ = _ := by rw [hx]
  have hHy : ∀ y, signMat p r *ᵥ (H *ᵥ y) = -y → H *ᵥ y = -(signMat p r *ᵥ y) := fun y hy => by
    calc H *ᵥ y = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ y)) := by
          rw [mulVec_mulVec, sb_J_mul_J, one_mulVec]
      _ = _ := by rw [hy, mulVec_neg]
  have horth : ∀ x y, signMat p r *ᵥ (H *ᵥ x) = x → signMat p r *ᵥ (H *ᵥ y) = -y →
      star x ⬝ᵥ (signMat p r *ᵥ y) = 0 := by
    intro x y hx hy
    have e := sb_herm_swap hHh x y
    rw [hHy y hy, hHx x hx, dotProduct_neg, ← sb_herm_swap (sb_J_herm p r)] at e
    linear_combination (-1 / 2 : ℂ) * e
  have horth' : ∀ x y, signMat p r *ᵥ (H *ᵥ x) = x → signMat p r *ᵥ (H *ᵥ y) = -y →
      star y ⬝ᵥ (signMat p r *ᵥ x) = 0 := by
    intro x y hx hy
    have e := sb_herm_swap hHh y x
    rw [hHx x hx, hHy y hy, star_neg, neg_dotProduct, ← sb_herm_swap (sb_J_herm p r)] at e
    linear_combination (1 / 2 : ℂ) * e
  have hNprop : ∀ y, signMat p r *ᵥ (H *ᵥ y) = -y → posSq p y ≤ s ^ 2 * negSq p y := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hsurj y
    have o := horth x y hx hy
    rw [sb_dot_J, sub_eq_zero, hxy] at o
    have hA : posSq p y = (star (sbDn p r *ᵥ x) ⬝ᵥ (sbDn p r *ᵥ y)).re := by
      rw [← o, sb_re_star_dot, sb_posSq_eq]
    have cs := sb_cs (sbDn p r *ᵥ x) (sbDn p r *ᵥ y)
    rw [← hA, ← sb_negSq_eq, ← sb_negSq_eq] at cs
    have hx' := hP x hx
    have hpx : posSq p x = posSq p y := by rw [sb_posSq_eq, sb_posSq_eq, hxy]
    have hA0 : 0 ≤ posSq p y := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
    have hD0 : 0 ≤ negSq p y := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
    rw [hpx] at hx'
    rcases hA0.eq_or_lt with h | h
    · rw [← h]; positivity
    · have h2 := mul_le_mul_of_nonneg_right hx' hD0
      exact le_of_mul_le_mul_left (by nlinarith : posSq p y * posSq p y ≤
        posSq p y * (s ^ 2 * negSq p y)) h
  have hdec : ∃ x y, signMat p r *ᵥ (H *ᵥ x) = x ∧ signMat p r *ᵥ (H *ᵥ y) = -y ∧ x + y = u :=
    ⟨(1 / 2 : ℂ) • (u + signMat p r *ᵥ (H *ᵥ u)), (1 / 2 : ℂ) • (u - signMat p r *ᵥ (H *ᵥ u)),
      by rw [mulVec_smul, mulVec_smul, mulVec_add, mulVec_add, hTT, add_comm],
      by rw [mulVec_smul, mulVec_smul, mulVec_sub, mulVec_sub, hTT, ← smul_neg, neg_sub],
      by ext k; simp; ring⟩
  obtain ⟨x, y, hx, hy, rfl⟩ := hdec
  have hPx := hP x hx
  have hPy := hNprop y hy
  set t := (star (sbDp p r *ᵥ x) ⬝ᵥ (sbDp p r *ᵥ y)).re with htdef
  have ht2 : (star (sbDn p r *ᵥ x) ⬝ᵥ (sbDn p r *ᵥ y)).re = t := by
    have o := horth x y hx hy
    rw [sb_dot_J, sub_eq_zero] at o
    rw [htdef, o]
  have hq_eq : hq H (x + y) = posSq p x - negSq p x - posSq p y + negSq p y := by
    have e1 := sb_re_dot_J p x
    have e2 := sb_re_dot_J p y
    rw [hq, mulVec_add, hHx x hx, hHy y hy, star_add]
    simp only [add_dotProduct, dotProduct_add, dotProduct_neg]
    rw [horth x y hx hy, horth' x y hx hy]
    simp only [Complex.add_re, Complex.neg_re, Complex.zero_re]
    linarith
  have hn_eq : normSq (x + y) =
      posSq p x + negSq p x + posSq p y + negSq p y + 4 * t := by
    have a3 : (star x ⬝ᵥ y).re = 2 * t := by rw [sb_dot_split p, Complex.add_re, ht2]; ring
    have a4 : (star y ⬝ᵥ x).re = 2 * t := by rw [sb_re_dot_comm, a3]
    rw [← sb_re_star_dot, star_add]
    simp only [add_dotProduct, dotProduct_add, Complex.add_re]
    rw [a3, a4, sb_re_star_dot, sb_re_star_dot, sb_normSq_split p x, sb_normSq_split p y]
    ring
  have hA0 : 0 ≤ posSq p x := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
  have hB0 : 0 ≤ negSq p x := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
  have hC0 : 0 ≤ posSq p y := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
  have hD0 : 0 ≤ negSq p y := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
  have hts1 : t ^ 2 ≤ posSq p x * posSq p y := by
    rw [sb_posSq_eq, sb_posSq_eq]; exact sb_cs _ _
  have hts2 : t ^ 2 ≤ negSq p x * negSq p y := by
    rw [← ht2, sb_negSq_eq, sb_negSq_eq]; exact sb_cs _ _
  have hsq : ∀ z : ℝ, 0 ≤ z → Real.sqrt (s ^ 2 * z) = s * Real.sqrt z := fun z hz => by
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]
  have hb : Real.sqrt (negSq p x) ≤ s * Real.sqrt (posSq p x) :=
    (Real.sqrt_le_sqrt hPx).trans (le_of_eq (hsq _ hA0))
  have hc : Real.sqrt (posSq p y) ≤ s * Real.sqrt (negSq p y) :=
    (Real.sqrt_le_sqrt hPy).trans (le_of_eq (hsq _ hD0))
  have h1 : |t| ≤ Real.sqrt (posSq p x) * Real.sqrt (posSq p y) := by
    rw [← Real.sqrt_mul hA0]; exact Real.abs_le_sqrt hts1
  have h2 : |t| ≤ Real.sqrt (negSq p x) * Real.sqrt (negSq p y) := by
    rw [← Real.sqrt_mul hB0]; exact Real.abs_le_sqrt hts2
  obtain ⟨hU, hL⟩ := sb_real_bounds _ _ _ _ s t (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hs0 hs1 hb hc h1 h2
  rw [Real.sq_sqrt hA0, Real.sq_sqrt hB0, Real.sq_sqrt hC0, Real.sq_sqrt hD0] at hU hL
  have h1s : 0 < 1 - s := by linarith
  rw [hq_eq, hn_eq]
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ h1s]; nlinarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ h1s]; nlinarith
end ReciprocityTheory.MultiplicativeHeights
