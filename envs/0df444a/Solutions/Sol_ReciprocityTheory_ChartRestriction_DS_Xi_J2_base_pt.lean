-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.base_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:02.111534+00:00
-- url     : https://prove2.me/submissions/22114a17-6dab-49b1-aea4-024a0560761b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution (m : ℕ) (v : ℝ) (hv : 0 < v) (x : Xp 0 m) :
    de x 0 ^ (-(s0N 0 m 0 + v)) ≤ 2 ^ (m + v / 2 : ℝ) *
      ((1 + ‖x.2.2.1‖ ^ 2) ^ (-(2 * (m + v / 2 : ℝ)) / 2) * (1 + ‖x.2.2.2‖ ^ 2) ^ (-(1 + v / 2) / 2)) := by
  set u := x.2.2.1 with hu
  set β := x.2.2.2 with hβ
  set S : ℝ := ∑ i, ‖u i‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have ha : ‖u‖ ^ 2 ≤ S := by
    have h1 : ‖u‖ ≤ Real.sqrt S := by
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro i
      rw [Real.le_sqrt (norm_nonneg _) hS0]
      exact Finset.single_le_sum (f := fun i => ‖u i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i)
    calc ‖u‖ ^ 2 ≤ (Real.sqrt S) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = S := Real.sq_sqrt hS0
  have hL : ∀ l : Fin 1, Lsq x l = 1 := by
    intro l
    simp [Lsq]
  have hrho : rhoSq x 0 = 1 + S := by
    simp [rhoSq, hL, hS, hu]
  have hbco : ‖bco x 0‖ ^ 2 = (S / 2) ^ 2 + β ^ 2 := by
    have h1 : bco x 0 = ((-S / 2 : ℝ) : ℂ) + (β : ℂ) * Complex.I := by
      simp [bco, hS, hu, hβ]
    rw [h1, Complex.sq_norm, Complex.normSq_add_mul_I]
    ring
  have hpos : 0 < (1 + S / 2) ^ 2 + β ^ 2 := by positivity
  have hAq : de x 0 = Real.sqrt ((1 + S / 2) ^ 2 + β ^ 2) := by
    unfold de
    rw [hL, hrho, hbco]
    congr 1
    ring
  have hs0 : s0N 0 m 0 = (m : ℝ) + 1 := by simp [s0N]
  rw [hAq, hs0, Real.sqrt_eq_rpow, ← Real.rpow_mul hpos.le]
  have hsplit : (1 / 2 : ℝ) * -((m : ℝ) + 1 + v) = -((m : ℝ) + v / 2) / 2 + -(1 + v / 2) / 2 := by ring
  rw [hsplit, Real.rpow_add hpos]
  have he1 : 0 ≤ (m : ℝ) + v / 2 := by positivity
  have hb1 : ((1 + S / 2) ^ 2 + β ^ 2) ^ (-((m : ℝ) + v / 2) / 2) ≤
      2 ^ ((m : ℝ) + v / 2) * (1 + ‖u‖ ^ 2) ^ (-(2 * ((m : ℝ) + v / 2)) / 2) := by
    have hh : (1 + ‖u‖ ^ 2) / 2 ≤ 1 + S / 2 := by linarith
    have h0 : 0 ≤ (1 + ‖u‖ ^ 2) / 2 := by positivity
    have hq : ((1 + ‖u‖ ^ 2) / 2) ^ 2 ≤ (1 + S / 2) ^ 2 + β ^ 2 := by
      nlinarith [mul_le_mul hh hh h0 (by linarith), sq_nonneg β]
    have hq0 : 0 < ((1 + ‖u‖ ^ 2) / 2) ^ 2 := by positivity
    calc ((1 + S / 2) ^ 2 + β ^ 2) ^ (-((m : ℝ) + v / 2) / 2)
        ≤ (((1 + ‖u‖ ^ 2) / 2) ^ 2) ^ (-((m : ℝ) + v / 2) / 2) :=
          Real.rpow_le_rpow_of_nonpos hq0 hq (by linarith)
      _ = 2 ^ ((m : ℝ) + v / 2) * (1 + ‖u‖ ^ 2) ^ (-(2 * ((m : ℝ) + v / 2)) / 2) := by
          have hy : ((1 + ‖u‖ ^ 2) / 2) ^ 2 = ((1 + ‖u‖ ^ 2) / 2) ^ (2 : ℝ) := (Real.rpow_two _).symm
          rw [hy, ← Real.rpow_mul h0, Real.div_rpow (by positivity) (by norm_num)]
          rw [show (2 : ℝ) * (-((m : ℝ) + v / 2) / 2) = -((m : ℝ) + v / 2) by ring,
            show -(2 * ((m : ℝ) + v / 2)) / 2 = -((m : ℝ) + v / 2) by ring,
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
          ring
  have hb2 : ((1 + S / 2) ^ 2 + β ^ 2) ^ (-(1 + v / 2) / 2) ≤ (1 + ‖β‖ ^ 2) ^ (-(1 + v / 2) / 2) := by
    have hq : 1 + ‖β‖ ^ 2 ≤ (1 + S / 2) ^ 2 + β ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
      nlinarith
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hq (by linarith)
  calc ((1 + S / 2) ^ 2 + β ^ 2) ^ (-((m : ℝ) + v / 2) / 2) * ((1 + S / 2) ^ 2 + β ^ 2) ^ (-(1 + v / 2) / 2)
      ≤ (2 ^ ((m : ℝ) + v / 2) * (1 + ‖u‖ ^ 2) ^ (-(2 * ((m : ℝ) + v / 2)) / 2)) *
          (1 + ‖β‖ ^ 2) ^ (-(1 + v / 2) / 2) :=
        mul_le_mul hb1 hb2 (Real.rpow_nonneg hpos.le _) (by positivity)
    _ = _ := by ring
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
