-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_raw_injective_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T08:18:36.054643+00:00
-- url     : https://prove2.me/submissions/1c8261cc-91b6-4301-bd7e-e43cbde3801f

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma leftBraidFun_injective (n : ℕ) (i j : Fin (n - 1)) (q : ℝ) :
    Function.Injective (leftBraidFun n i j q) := by
  intro k l hkl
  by_cases hq1 : q ≤ 1 / 2
  · simp only [leftBraidFun, if_pos hq1] at hkl
    exact halfTwistFun_injective n i (2 * q) hkl
  · by_cases hq2 : q ≤ 3 / 4
    · simp only [leftBraidFun, if_neg hq1, if_pos hq2] at hkl
      have hs := halfTwistFun_injective n j (4 * q - 2) hkl
      exact (Equiv.swap (strandIdx i) (strandIdxSucc i)).injective hs
    · simp only [leftBraidFun, if_neg hq1, if_neg hq2] at hkl
      have hs := halfTwistFun_injective n i (4 * q - 3) hkl
      have hs' := (Equiv.swap (strandIdx j) (strandIdxSucc j)).injective hs
      exact (Equiv.swap (strandIdx i) (strandIdxSucc i)).injective hs'

lemma rightBraidFun_injective (n : ℕ) (i j : Fin (n - 1)) (q : ℝ) :
    Function.Injective (rightBraidFun n i j q) := by
  intro k l hkl
  by_cases hq1 : q ≤ 1 / 2
  · simp only [rightBraidFun, if_pos hq1] at hkl
    exact halfTwistFun_injective n j (2 * q) hkl
  · by_cases hq2 : q ≤ 3 / 4
    · simp only [rightBraidFun, if_neg hq1, if_pos hq2] at hkl
      have hs := halfTwistFun_injective n i (4 * q - 2) hkl
      exact (Equiv.swap (strandIdx j) (strandIdxSucc j)).injective hs
    · simp only [rightBraidFun, if_neg hq1, if_neg hq2] at hkl
      have hs := halfTwistFun_injective n j (4 * q - 3) hkl
      have hs' := (Equiv.swap (strandIdx i) (strandIdxSucc i)).injective hs
      exact (Equiv.swap (strandIdx j) (strandIdxSucc j)).injective hs'

lemma twistPoint_neg_ne_pos (c a t : ℝ) (ha : a ≠ 0) :
    twistPoint c (-a) t ≠ twistPoint c a t := by
  intro h
  have hsin : Real.sin (Real.pi * t) ^ 2 + Real.cos (Real.pi * t) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have hre : c + (-a) * Real.cos (Real.pi * t) / 2 =
      c + a * Real.cos (Real.pi * t) / 2 := by
    simpa using congrArg Complex.re h
  have him : (-a) * Real.sin (Real.pi * t) / 2 =
      a * Real.sin (Real.pi * t) / 2 := by
    simpa using congrArg Complex.im h
  have hcprod : a * Real.cos (Real.pi * t) = 0 := by linarith
  have hsprod : a * Real.sin (Real.pi * t) = 0 := by linarith
  have hc : Real.cos (Real.pi * t) = 0 := (mul_eq_zero.mp hcprod).resolve_left ha
  have hs : Real.sin (Real.pi * t) = 0 := (mul_eq_zero.mp hsprod).resolve_left ha
  rw [hc, hs] at hsin
  norm_num at hsin

lemma twistPoint_ne_center (c a t : ℝ) (ha : a ≠ 0) :
    twistPoint c a t ≠ (c : ℂ) := by
  intro h
  have hsin : Real.sin (Real.pi * t) ^ 2 + Real.cos (Real.pi * t) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have hre : c + a * Real.cos (Real.pi * t) / 2 = c := by
    simpa using congrArg Complex.re h
  have him : a * Real.sin (Real.pi * t) / 2 = 0 := by
    simpa using congrArg Complex.im h
  have hcprod : a * Real.cos (Real.pi * t) = 0 := by linarith
  have hsprod : a * Real.sin (Real.pi * t) = 0 := by linarith
  have hc : Real.cos (Real.pi * t) = 0 := (mul_eq_zero.mp hcprod).resolve_left ha
  have hs : Real.sin (Real.pi * t) = 0 := (mul_eq_zero.mp hsprod).resolve_left ha
  rw [hc, hs] at hsin
  norm_num at hsin

lemma outerTwist_ne_fixed {n : ℕ} {i : Fin (n - 1)} {k : Fin n}
    (s t : ℝ) (hs1 : -2 ≤ s) (hs2 : s ≤ 2)
    (h0 : (k : ℕ) ≠ (i : ℕ)) (h1 : (k : ℕ) ≠ (i : ℕ) + 1) (h2 : (k : ℕ) ≠ (i : ℕ) + 2) :
    twistPoint ((i : ℕ) + 2) s t ≠ (((k : ℕ) + 1 : ℝ) : ℂ) := by
  intro h
  have hc1 := Real.neg_one_le_cos (Real.pi * t)
  have hc2 := Real.cos_le_one (Real.pi * t)
  have hp1 : -2 ≤ s * Real.cos (Real.pi * t) := by nlinarith
  have hp2 : s * Real.cos (Real.pi * t) ≤ 2 := by nlinarith
  have hre : ((i : ℕ) : ℝ) + 2 + s * Real.cos (Real.pi * t) / 2 =
      ((k : ℕ) : ℝ) + 1 := by
    simpa using congrArg Complex.re h
  have hloR : ((i : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by nlinarith
  have hhiR : ((k : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) + 2 := by nlinarith
  have hlo : (i : ℕ) ≤ (k : ℕ) := by exact_mod_cast hloR
  have hhi : (k : ℕ) ≤ (i : ℕ) + 2 := by exact_mod_cast hhiR
  omega

lemma outerRotateFun_injective {n : ℕ} (i : Fin (n - 1)) (q : ℝ)
    (hi2 : (i : ℕ) + 2 < n) : Function.Injective (outerRotateFun n i q) := by
  intro k l hkl
  by_cases hk0 : (k : ℕ) = (i : ℕ)
  · by_cases hl0 : (l : ℕ) = (i : ℕ)
    · exact Fin.ext (hk0.trans hl0.symm)
    · by_cases hl1 : (l : ℕ) = (i : ℕ) + 1
      · simp [outerRotateFun, hk0, hl0, hl1] at hkl
        exact absurd hkl (by simpa using
          (twistPoint_ne_center (((i : ℕ) : ℝ) + 2) (-2) q (by norm_num)))
      · by_cases hl2 : (l : ℕ) = (i : ℕ) + 2
        · simp [outerRotateFun, hk0, hl0, hl1, hl2] at hkl
          exact absurd hkl (twistPoint_neg_ne_pos _ 2 _ (by norm_num))
        · simp [outerRotateFun, hk0, hl0, hl1, hl2] at hkl
          exact absurd hkl (by simpa using
            (outerTwist_ne_fixed (-2) q (by norm_num) (by norm_num) hl0 hl1 hl2))
  · by_cases hk1 : (k : ℕ) = (i : ℕ) + 1
    · by_cases hl0 : (l : ℕ) = (i : ℕ)
      · simp [outerRotateFun, hk0, hk1, hl0] at hkl
        exact absurd hkl.symm (by simpa using
          (twistPoint_ne_center (((i : ℕ) : ℝ) + 2) (-2) q (by norm_num)))
      · by_cases hl1 : (l : ℕ) = (i : ℕ) + 1
        · exact Fin.ext (hk1.trans hl1.symm)
        · by_cases hl2 : (l : ℕ) = (i : ℕ) + 2
          · simp [outerRotateFun, hk0, hk1, hl0, hl1, hl2] at hkl
            exact absurd hkl.symm (by simpa using
            (twistPoint_ne_center (((i : ℕ) : ℝ) + 2) 2 q (by norm_num)))
          · simp [outerRotateFun, hk0, hk1, hl0, hl1, hl2] at hkl
            have hre := congrArg Complex.re hkl
            simp at hre
            have hnat : (i : ℕ) + 2 = (l : ℕ) + 1 := by exact_mod_cast hre
            apply Fin.ext
            omega
    · by_cases hk2 : (k : ℕ) = (i : ℕ) + 2
      · by_cases hl0 : (l : ℕ) = (i : ℕ)
        · simp [outerRotateFun, hk0, hk1, hk2, hl0] at hkl
          exact absurd hkl.symm (twistPoint_neg_ne_pos _ 2 _ (by norm_num))
        · by_cases hl1 : (l : ℕ) = (i : ℕ) + 1
          · simp [outerRotateFun, hk0, hk1, hk2, hl0, hl1] at hkl
            exact absurd hkl (by simpa using
            (twistPoint_ne_center (((i : ℕ) : ℝ) + 2) 2 q (by norm_num)))
          · by_cases hl2 : (l : ℕ) = (i : ℕ) + 2
            · exact Fin.ext (hk2.trans hl2.symm)
            · simp [outerRotateFun, hk0, hk1, hk2, hl0, hl1, hl2] at hkl
              exact absurd hkl (by simpa using
                (outerTwist_ne_fixed 2 q (by norm_num) (by norm_num) hl0 hl1 hl2))
      · by_cases hl0 : (l : ℕ) = (i : ℕ)
        · simp [outerRotateFun, hk0, hk1, hk2, hl0] at hkl
          exact absurd hkl.symm (by simpa using
            (outerTwist_ne_fixed (-2) q (by norm_num) (by norm_num) hk0 hk1 hk2))
        · by_cases hl1 : (l : ℕ) = (i : ℕ) + 1
          · simp [outerRotateFun, hk0, hk1, hk2, hl0, hl1] at hkl
            have hre := congrArg Complex.re hkl
            simp at hre
            have hnat : (k : ℕ) + 1 = (i : ℕ) + 2 := by exact_mod_cast hre
            exfalso
            apply hk1
            omega
          · by_cases hl2 : (l : ℕ) = (i : ℕ) + 2
            · simp [outerRotateFun, hk0, hk1, hk2, hl0, hl1, hl2] at hkl
              exact absurd hkl.symm (by simpa using
                (outerTwist_ne_fixed 2 q (by norm_num) (by norm_num) hk0 hk1 hk2))
            · simp [outerRotateFun, hk0, hk1, hk2, hl0, hl1, hl2] at hkl
              exact Fin.ext hkl


end TarchaBraids

open BraidsLinksMCG TarchaBraids
theorem solution :
    (∀ {n : ℕ} (i j : Fin (n - 1)) (q : ℝ),
      Function.Injective (leftBraidFun n i j q)) ∧
    (∀ {n : ℕ} (i j : Fin (n - 1)) (q : ℝ),
      Function.Injective (rightBraidFun n i j q)) ∧
    (∀ {n : ℕ} (i : Fin (n - 1)) (q : ℝ),
      (i : ℕ) + 2 < n → Function.Injective (outerRotateFun n i q)) := by
  exact ⟨fun i j q => leftBraidFun_injective _ i j q,
    ⟨fun i j q => rightBraidFun_injective _ i j q,
      fun i q hi2 => outerRotateFun_injective i q hi2⟩⟩

