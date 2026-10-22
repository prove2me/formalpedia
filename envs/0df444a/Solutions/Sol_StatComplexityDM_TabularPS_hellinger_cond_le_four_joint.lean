-- Prove2me | solution 1 for StatComplexityDM.TabularPS.hellinger_cond_le_four_joint
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:03:22.076821+00:00
-- url     : https://prove2.me/submissions/686ca4ce-0de4-48ba-87e4-55e0a6972c39

import Mathlib
import Definitions.Def_StatComplexityDM_PCIGW_MDP

set_option autoImplicit false

theorem solution {X Y : Type*} [Fintype X] [Fintype Y]
    (PX QX : X → ℝ) (K L : X → Y → ℝ)
    (hPX : StatComplexityDM.LowerBound.IsDist PX) (hQX : StatComplexityDM.LowerBound.IsDist QX)
    (hK : ∀ x, StatComplexityDM.LowerBound.IsDist (K x))
    (hL : ∀ x, StatComplexityDM.LowerBound.IsDist (L x)) :
    ∑ x, PX x * FoundationsRL.GeneralDM.hellingerSq (K x) (L x) ≤
      4 * FoundationsRL.GeneralDM.hellingerSq
        (fun xy : X × Y => PX xy.1 * K xy.1 xy.2)
        (fun xy : X × Y => QX xy.1 * L xy.1 xy.2) := by
  unfold FoundationsRL.GeneralDM.hellingerSq
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum (fun x _ => ?_)
  have hp := hPX.1 x
  have hq := hQX.1 x
  have hk0 := (hK x).1
  have hl0 := (hL x).1
  have hk1 := (hK x).2
  have hl1 := (hL x).2
  set s := ∑ y, Real.sqrt (K x y) * Real.sqrt (L x y) with hs
  -- left side
  have eL : ∑ y, (Real.sqrt (K x y) - Real.sqrt (L x y)) ^ 2 = 2 - 2 * s := by
    have : ∀ y, (Real.sqrt (K x y) - Real.sqrt (L x y)) ^ 2 =
        K x y + L x y - 2 * (Real.sqrt (K x y) * Real.sqrt (L x y)) := by
      intro y
      have h1 := Real.sq_sqrt (hk0 y)
      have h2 := Real.sq_sqrt (hl0 y)
      nlinarith
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hk1, hl1]
    ring
  -- right side
  have eR : ∑ y, (Real.sqrt (PX x * K x y) - Real.sqrt (QX x * L x y)) ^ 2 =
      PX x + QX x - 2 * (Real.sqrt (PX x) * Real.sqrt (QX x)) * s := by
    have : ∀ y, (Real.sqrt (PX x * K x y) - Real.sqrt (QX x * L x y)) ^ 2 =
        PX x * K x y + QX x * L x y -
          2 * (Real.sqrt (PX x) * Real.sqrt (QX x)) * (Real.sqrt (K x y) * Real.sqrt (L x y)) := by
      intro y
      rw [Real.sqrt_mul hp, Real.sqrt_mul hq]
      have h1 := Real.sq_sqrt hp
      have h2 := Real.sq_sqrt hq
      have h3 := Real.sq_sqrt (hk0 y)
      have h4 := Real.sq_sqrt (hl0 y)
      nlinarith
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hk1, hl1]
    ring
  -- Cauchy-Schwarz type bounds for s
  have hs1 : s ≤ 1 := by
    have : 0 ≤ ∑ y, (Real.sqrt (K x y) - Real.sqrt (L x y)) ^ 2 :=
      Finset.sum_nonneg (fun y _ => sq_nonneg _)
    linarith
  have hs2 : -1 ≤ s := by
    have : 0 ≤ ∑ y, (Real.sqrt (K x y) + Real.sqrt (L x y)) ^ 2 :=
      Finset.sum_nonneg (fun y _ => sq_nonneg _)
    have e : ∑ y, (Real.sqrt (K x y) + Real.sqrt (L x y)) ^ 2 = 2 + 2 * s := by
      have h' : ∀ y, (Real.sqrt (K x y) + Real.sqrt (L x y)) ^ 2 =
          K x y + L x y + 2 * (Real.sqrt (K x y) * Real.sqrt (L x y)) := by
        intro y
        have h1 := Real.sq_sqrt (hk0 y)
        have h2 := Real.sq_sqrt (hl0 y)
        nlinarith
      simp_rw [h']
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hk1, hl1]
      ring
    linarith
  rw [eL, eR]
  set a := Real.sqrt (PX x) with ha
  set b := Real.sqrt (QX x) with hb
  have hpa : PX x = a ^ 2 := (Real.sq_sqrt hp).symm
  have hqb : QX x = b ^ 2 := (Real.sq_sqrt hq).symm
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  rw [hpa, hqb]
  nlinarith [mul_nonneg (show 0 ≤ 1 + s by linarith) (sq_nonneg (a - b)),
    mul_nonneg (show 0 ≤ 1 - s by linarith) (add_nonneg (sq_nonneg b) (mul_nonneg (mul_nonneg ha0 hb0) (by norm_num : (0:ℝ) ≤ 2)))]
