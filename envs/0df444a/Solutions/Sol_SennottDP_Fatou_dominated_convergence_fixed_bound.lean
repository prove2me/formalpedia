-- Prove2me | solution 1 for SennottDP.Fatou.dominated_convergence_fixed_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:16:04.483714+00:00
-- url     : https://prove2.me/submissions/450ba395-af56-4fe9-8b46-236724c80a1c

import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic

set_option autoImplicit false

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou.P6f8b9e13

lemma toENNReal_coe_real (x : ℝ) : ((x : EReal)).toENNReal = ENNReal.ofReal x := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top x), EReal.toReal_coe]

lemma ofReal_max_zero (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

lemma part_eq {S : Type*} (P : S → ℝ≥0∞) (hP : ∀ j, P j ≠ ⊤) (f : S → ℝ) (b : S → ℝ)
    (hb : Summable (fun j => (P j).toReal * b j)) (hfb : ∀ j, |f j| ≤ b j) :
    Summable (fun j => (P j).toReal * max (f j) 0) ∧
    (((∑' j, P j * ((f j : EReal)).toENNReal : ℝ≥0∞) : EReal)
      = ((∑' j, (P j).toReal * max (f j) 0 : ℝ) : EReal)) := by
  have hs : Summable (fun j => (P j).toReal * max (f j) 0) := by
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _))
      (fun j => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg) hb
    exact max_le ((le_abs_self _).trans (hfb j)) ((abs_nonneg _).trans (hfb j))
  refine ⟨hs, ?_⟩
  have hterm : ∀ j, P j * ((f j : EReal)).toENNReal
      = ENNReal.ofReal ((P j).toReal * max (f j) 0) := by
    intro j
    rw [toENNReal_coe_real, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hP j), ofReal_max_zero]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun j => mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _)) hs, EReal.coe_ennreal_ofReal,
    max_eq_left (tsum_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _)))]

lemma wsum_real {S : Type*} (P : S → ℝ≥0∞) (hP : ∀ j, P j ≠ ⊤) (f : S → ℝ) (b : S → ℝ)
    (hb : Summable (fun j => (P j).toReal * b j)) (hfb : ∀ j, |f j| ≤ b j) :
    wsum P (fun j => (f j : EReal)) = ((∑' j, (P j).toReal * f j : ℝ) : EReal) := by
  unfold wsum
  obtain ⟨h1, e1⟩ := part_eq P hP f b hb hfb
  obtain ⟨h2, e2⟩ := part_eq P hP (fun j => -f j) b hb (fun j => by rw [abs_neg]; exact hfb j)
  have hneg : (fun j => P j * (-((f j : ℝ) : EReal)).toENNReal)
      = (fun j => P j * (((-f j : ℝ) : EReal)).toENNReal) := by
    funext j; rw [EReal.coe_neg]
  rw [hneg, e1, e2, ← EReal.coe_sub, ← h1.tsum_sub h2]
  congr 2
  funext j
  rw [← mul_sub]
  congr 1
  rcases le_total (f j) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

end SennottDP.Fatou.P6f8b9e13

open Filter Topology ENNReal SennottDP.Fatou in
theorem solution {S : Type*} [Countable S] (P : S → ℝ≥0∞)
    (hP : ∑' j, P j = 1) (u : S → ℕ → ℝ) (uL : S → EReal)
    (hu : ∀ j, Tendsto (fun N => (u j N : EReal)) atTop (𝓝 (uL j)))
    (w : S → ℝ) (hdom : ∀ j N, |u j N| ≤ w j) (hfin : wsum P (fun j => (w j : EReal)) < ⊤) :
    Tendsto (fun N => wsum P (fun j => (u j N : EReal))) atTop (𝓝 (wsum P uL)) := by
  have hPt : ∀ j, P j ≠ ⊤ := by
    intro j
    have : P j ≤ 1 := hP ▸ ENNReal.le_tsum j
    exact ne_top_of_le_ne_top ENNReal.one_ne_top this
  have hw0 : ∀ j, 0 ≤ w j := fun j => (abs_nonneg _).trans (hdom j 0)
  -- summability of the bound
  have hsum : Summable (fun j => (P j).toReal * w j) := by
    have hzero : (∑' j, P j * (-((w j : ℝ) : EReal)).toENNReal) = 0 := by
      have : ∀ j, P j * (-((w j : ℝ) : EReal)).toENNReal = 0 := by
        intro j
        rw [EReal.toENNReal_of_nonpos, mul_zero]
        rw [← EReal.coe_neg]; exact_mod_cast neg_nonpos.mpr (hw0 j)
      simp only [this, tsum_zero]
    unfold wsum at hfin
    rw [hzero, EReal.coe_ennreal_zero, sub_zero] at hfin
    have hT : (∑' j, P j * ((w j : ℝ) : EReal).toENNReal) ≠ ⊤ := by
      intro h; rw [h] at hfin; simp at hfin
    have hterm : ∀ j, P j * ((w j : ℝ) : EReal).toENNReal
        = ENNReal.ofReal ((P j).toReal * w j) := by
      intro j
      rw [P6f8b9e13.toENNReal_coe_real, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (hPt j)]
    simp_rw [hterm] at hT
    have := ENNReal.summable_toReal hT
    refine this.congr (fun j => ?_)
    rw [ENNReal.toReal_ofReal (mul_nonneg ENNReal.toReal_nonneg (hw0 j))]
  -- the limit is real
  have hle : ∀ j, uL j ≤ (w j : EReal) := fun j =>
    le_of_tendsto' (hu j) (fun N => EReal.coe_le_coe_iff.mpr (abs_le.mp (hdom j N)).2)
  have hge : ∀ j, ((-w j : ℝ) : EReal) ≤ uL j := fun j =>
    ge_of_tendsto' (hu j) (fun N => EReal.coe_le_coe_iff.mpr (abs_le.mp (hdom j N)).1)
  set v : S → ℝ := fun j => (uL j).toReal with hvdef
  have hv : ∀ j, uL j = (v j : EReal) := by
    intro j
    have h1 : uL j ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hle j)
    have h2 : uL j ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hge j)
    exact (EReal.coe_toReal h1 h2).symm
  have hvlim : ∀ j, Tendsto (fun N => u j N) atTop (𝓝 (v j)) := by
    intro j
    have := hu j
    rw [hv j] at this
    exact EReal.tendsto_coe.mp this
  have hvb : ∀ j, |v j| ≤ w j := by
    intro j
    have a := hle j; have b := hge j
    rw [hv j] at a b
    exact abs_le.mpr ⟨EReal.coe_le_coe_iff.mp b, EReal.coe_le_coe_iff.mp a⟩
  have hL : wsum P uL = ((∑' j, (P j).toReal * v j : ℝ) : EReal) := by
    have : uL = fun j => (v j : EReal) := funext hv
    rw [this]
    exact P6f8b9e13.wsum_real P hPt v w hsum hvb
  have hN : (fun N => wsum P (fun j => (u j N : EReal)))
      = fun N => ((∑' j, (P j).toReal * u j N : ℝ) : EReal) := by
    funext N
    exact P6f8b9e13.wsum_real P hPt (fun j => u j N) w hsum (fun j => hdom j N)
  rw [hL, hN]
  refine EReal.tendsto_coe.mpr ?_
  refine tendsto_tsum_of_dominated_convergence hsum
    (fun j => (tendsto_const_nhds.mul (hvlim j))) (Eventually.of_forall fun N j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hdom j N) ENNReal.toReal_nonneg
