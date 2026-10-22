-- Prove2me | solution 1 for Teletriage.OneShot.posterior_straddle
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:31:15.587835+00:00
-- url     : https://prove2.me/submissions/5624b626-1b1e-4352-8b57-091944a75741

import Mathlib
import Definitions.Def_Teletriage_OneShot_Model

namespace Teletriage.OneShot.Dev

open Teletriage.OneShot

variable (P : Params)

theorem b0_facts (hS : P.Standing) :
    0 < b0 P ∧ b0 P < 1 ∧ P.cP = (1 - b0 P) * P.cE ∧ 0 < P.cE := by
  obtain ⟨hp, hpe, -⟩ := hS
  have hE : 0 < P.cE := by linarith
  have hlt : P.cP / P.cE < 1 := (div_lt_one hE).2 hpe
  have hpos : 0 < P.cP / P.cE := div_pos hp hE
  refine ⟨by unfold b0; linarith, by unfold b0; linarith, ?_, hE⟩
  unfold b0; field_simp; ring

theorem k_eq (hS : P.Standing) : P.cT / P.cP * (1 - b0 P) = P.cT / P.cE := by
  obtain ⟨hp, hpe, -⟩ := hS
  have hE : 0 < P.cE := by linarith
  unfold b0; field_simp; ring

theorem cT_eq (hS : P.Standing) : P.cT = P.cT / P.cE * P.cE := by
  have := (b0_facts P hS).2.2.2
  field_simp

/-- products `p * (a / p) = a` when `0 ≤ a ≤ p`. -/
theorem mul_div_self' (p a : ℝ) (ha : 0 ≤ a) (hap : a ≤ p) : p * (a / p) = a := by
  rcases eq_or_lt_of_le (ha.trans hap) with h | h
  · rw [← h]; simp; linarith
  · field_simp

theorem pS_bPS (hS : P.Standing) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    probPS P b * bPS P b = P.α * b := by
  obtain ⟨-, -, -, hα0, hα1, hβ0, hβ1⟩ := hS
  unfold bPS
  apply mul_div_self' _ _ (mul_nonneg hα0 hb0)
  unfold probPS; nlinarith [mul_nonneg (sub_nonneg.2 hβ1) (sub_nonneg.2 hb1)]

theorem pC_bPC (hS : P.Standing) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    probPC P b * bPC P b = (1 - P.α) * b := by
  obtain ⟨-, -, -, hα0, hα1, hβ0, hβ1⟩ := hS
  unfold bPC
  apply mul_div_self' _ _ (mul_nonneg (sub_nonneg.2 hα1) hb0)
  unfold probPC; nlinarith [mul_nonneg hβ0 (sub_nonneg.2 hb1)]

theorem pS_nonneg (hS : P.Standing) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ probPS P b := by
  obtain ⟨-, -, -, hα0, hα1, hβ0, hβ1⟩ := hS
  unfold probPS
  nlinarith [mul_nonneg (sub_nonneg.2 hβ1) (sub_nonneg.2 hb1), mul_nonneg hα0 hb0]

theorem pC_nonneg (hS : P.Standing) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ probPC P b := by
  obtain ⟨-, -, -, hα0, hα1, hβ0, hβ1⟩ := hS
  unfold probPC
  nlinarith [mul_nonneg hβ0 (sub_nonneg.2 hb1), mul_nonneg (sub_nonneg.2 hα1) hb0]

theorem pS_add_pC (b : ℝ) : probPS P b + probPC P b = 1 := by
  unfold probPS probPC; ring

/-- The general formula for the teletriage cost. -/
theorem costTT_formula (hS : P.Standing) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    costTT P b = P.cT + min (probPS P b * P.cE) (probPS P b * P.cP + P.α * b * P.cE)
      + min (probPC P b * P.cE) (probPC P b * P.cP + (1 - P.α) * b * P.cE) := by
  unfold costTT V0 costPCP
  rw [mul_min_of_nonneg _ _ (pS_nonneg P hS b hb0 hb1),
    mul_min_of_nonneg _ _ (pC_nonneg P hS b hb0 hb1)]
  have h1 := pS_bPS P hS b hb0 hb1
  have h2 := pC_bPC P hS b hb0 hb1
  congr 2
  · congr 1; rw [mul_add, ← mul_assoc, h1]
  · congr 1; rw [mul_add, ← mul_assoc, h2]

theorem DL_pos (hS : P.Standing) (hI : P.Informative) :
    0 < P.β * b0 P + (1 - P.α) * (1 - b0 P) := by
  obtain ⟨hb0, hb1, -⟩ := b0_facts P hS
  obtain ⟨-, -, -, hα0, hα1, hβ0, hβ1⟩ := hS
  unfold Params.Informative at hI
  nlinarith [mul_pos (show (0:ℝ) < 1 - P.α by linarith) (show (0:ℝ) < 1 - b0 P by linarith),
    mul_nonneg hβ0 hb0.le]

theorem DH_pos (hS : P.Standing) (hI : P.Informative) :
    0 < (1 - P.β) * b0 P + P.α * (1 - b0 P) := by
  obtain ⟨hb0, hb1, -⟩ := b0_facts P hS
  obtain ⟨-, -, -, hα0, hα1, hβ0, hβ1⟩ := hS
  unfold Params.Informative at hI
  nlinarith [mul_pos (show (0:ℝ) < 1 - P.β by linarith) hb0,
    mul_nonneg hα0 (show (0:ℝ) ≤ 1 - b0 P by linarith)]

theorem bLL_mul (hS : P.Standing) (hI : P.Informative) :
    bLowLow P * (P.β * b0 P + (1 - P.α) * (1 - b0 P)) = P.β * b0 P := by
  unfold bLowLow; exact div_mul_cancel₀ _ (DL_pos P hS hI).ne'

theorem bHH_mul (hS : P.Standing) (hI : P.Informative) :
    bHighHigh P * ((1 - P.β) * b0 P + P.α * (1 - b0 P)) = (1 - P.β) * b0 P := by
  unfold bHighHigh; exact div_mul_cancel₀ _ (DH_pos P hS hI).ne'

theorem bL_mul (hS : P.Standing) (hI : P.Informative) :
    bLow P * (P.β * b0 P + (1 - P.α) * (1 - b0 P)) = P.β * b0 P + P.cT / P.cE := by
  unfold bLow; rw [div_mul_cancel₀ _ (DL_pos P hS hI).ne', k_eq P hS]

theorem bH_mul (hS : P.Standing) (hI : P.Informative) :
    bHigh P * ((1 - P.β) * b0 P + P.α * (1 - b0 P)) = (1 - P.β) * b0 P - P.cT / P.cE := by
  unfold bHigh; rw [div_mul_cancel₀ _ (DH_pos P hS hI).ne', k_eq P hS]

theorem k_nonneg (hS : P.Standing) : 0 ≤ P.cT / P.cE :=
  div_nonneg hS.2.2.1 (b0_facts P hS).2.2.2.le

/-- Comparison `x ≤ t` where `t * D = N`, `D > 0`. -/
theorem le_of_mul {x t D N : ℝ} (hD : 0 < D) (ht : t * D = N) : x ≤ t ↔ x * D ≤ N := by
  rw [← ht]; exact (mul_le_mul_iff_of_pos_right hD).symm

theorem lt_of_mul {x t D N : ℝ} (hD : 0 < D) (ht : t * D = N) : x < t ↔ x * D < N := by
  rw [← ht]; exact (mul_lt_mul_iff_of_pos_right hD).symm

theorem ge_of_mul {x t D N : ℝ} (hD : 0 < D) (ht : t * D = N) : t ≤ x ↔ N ≤ x * D := by
  rw [← ht]; exact (mul_le_mul_iff_of_pos_right hD).symm

theorem gt_of_mul {x t D N : ℝ} (hD : 0 < D) (ht : t * D = N) : t < x ↔ N < x * D := by
  rw [← ht]; exact (mul_lt_mul_iff_of_pos_right hD).symm

/-- Ordering of thresholds. -/
theorem thresholds (hS : P.Standing) (hI : P.Informative) :
    bLowLow P ≤ bLow P ∧ bHigh P ≤ bHighHigh P ∧ bLowLow P ≤ b0 P ∧ b0 P ≤ bHighHigh P ∧
    0 ≤ bLowLow P ∧ bHighHigh P ≤ 1 ∧ 0 < bHighHigh P ∧ bLowLow P < 1 := by
  have hDL := DL_pos P hS hI
  have hDH := DH_pos P hS hI
  have hk := k_nonneg P hS
  obtain ⟨hb0, hb1, -⟩ := b0_facts P hS
  have e1 := bLL_mul P hS hI
  have e2 := bHH_mul P hS hI
  have e3 := bL_mul P hS hI
  have e4 := bH_mul P hS hI
  obtain ⟨-, -, -, hα0, hα1, hβ0, hβ1⟩ := hS
  unfold Params.Informative at hI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ge_of_mul hDL e1).2 (by rw [e3]; linarith)
  · exact (le_of_mul hDH e2).2 (by rw [e4]; linarith)
  · refine (ge_of_mul hDL e1).2 ?_
    nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 1 - P.α - P.β by linarith) hb0.le)
      (show (0:ℝ) ≤ 1 - b0 P by linarith)]
  · refine (le_of_mul hDH e2).2 ?_
    nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 1 - P.α - P.β by linarith) hb0.le)
      (show (0:ℝ) ≤ 1 - b0 P by linarith)]
  · unfold bLowLow; exact div_nonneg (mul_nonneg hβ0 hb0.le) hDL.le
  · refine (ge_of_mul hDH e2).2 ?_
    nlinarith [mul_nonneg hα0 (show (0:ℝ) ≤ 1 - b0 P by linarith)]
  · unfold bHighHigh; exact div_pos (mul_pos (by linarith) hb0) hDH
  · refine (gt_of_mul hDL e1).2 ?_
    nlinarith [mul_pos (show (0:ℝ) < 1 - P.α by linarith) (show (0:ℝ) < 1 - b0 P by linarith)]

theorem ED_iff (hS : P.Standing) (x : ℝ) : P.cE ≤ costPCP P x ↔ b0 P ≤ x := by
  obtain ⟨-, -, hcP, hE⟩ := b0_facts P hS
  unfold costPCP; rw [hcP]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem piED_eq (hS : P.Standing) (x : ℝ) : piED P x = if b0 P ≤ x then 1 else x := by
  unfold piED actNoTT
  by_cases h : b0 P ≤ x
  · rw [if_pos ((ED_iff P hS x).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((ED_iff P hS x).1 h')), if_neg h]

theorem piDD_eq (hS : P.Standing) (x : ℝ) : piDD P x = if b0 P ≤ x then 0 else x := by
  unfold piDD actNoTT
  by_cases h : b0 P ≤ x
  · rw [if_pos ((ED_iff P hS x).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((ED_iff P hS x).1 h')), if_neg h]

theorem idS (hS : P.Standing) (b : ℝ) :
    b0 P * probPS P b - P.α * b = (1 - P.β) * b0 P - b * ((1 - P.β) * b0 P + P.α * (1 - b0 P)) := by
  unfold probPS; ring

theorem idC (hS : P.Standing) (b : ℝ) :
    b0 P * probPC P b - (1 - P.α) * b = P.β * b0 P - b * (P.β * b0 P + (1 - P.α) * (1 - b0 P)) := by
  unfold probPC; ring

theorem bPS_lt_iff (hS : P.Standing) (hI : P.Informative) (b : ℝ) (hp : 0 < probPS P b) :
    bPS P b < b0 P ↔ b < bHighHigh P := by
  unfold bPS
  rw [div_lt_iff₀ hp, lt_of_mul (DH_pos P hS hI) (bHH_mul P hS hI)]
  have := idS P hS b
  constructor <;> intro h <;> nlinarith

theorem bPS_le_iff (hS : P.Standing) (hI : P.Informative) (b : ℝ) (hp : 0 < probPS P b) :
    bPS P b ≤ b0 P ↔ b ≤ bHighHigh P := by
  unfold bPS
  rw [div_le_iff₀ hp, le_of_mul (DH_pos P hS hI) (bHH_mul P hS hI)]
  have := idS P hS b
  constructor <;> intro h <;> nlinarith

theorem bPC_lt_iff (hS : P.Standing) (hI : P.Informative) (b : ℝ) (hp : 0 < probPC P b) :
    bPC P b < b0 P ↔ b < bLowLow P := by
  unfold bPC
  rw [div_lt_iff₀ hp, lt_of_mul (DL_pos P hS hI) (bLL_mul P hS hI)]
  have := idC P hS b
  constructor <;> intro h <;> nlinarith

theorem bPC_le_iff (hS : P.Standing) (hI : P.Informative) (b : ℝ) (hp : 0 < probPC P b) :
    bPC P b ≤ b0 P ↔ b ≤ bLowLow P := by
  unfold bPC
  rw [div_le_iff₀ hp, le_of_mul (DL_pos P hS hI) (bLL_mul P hS hI)]
  have := idC P hS b
  constructor <;> intro h <;> nlinarith

theorem pS_pos (hS : P.Standing) (hI : P.Informative) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    0 < probPS P b := by
  obtain ⟨-, -, -, hα0, hα1, hβ0, hβ1⟩ := hS
  unfold Params.Informative at hI
  unfold probPS
  nlinarith [mul_pos (show (0:ℝ) < 1 - P.β by linarith) (show (0:ℝ) < 1 - b by linarith),
    mul_nonneg hα0 hb0]

theorem pC_pos (hS : P.Standing) (hI : P.Informative) (b : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    0 < probPC P b := by
  obtain ⟨-, -, -, hα0, hα1, hβ0, hβ1⟩ := hS
  unfold Params.Informative at hI
  unfold probPC
  nlinarith [mul_pos (show (0:ℝ) < 1 - P.α by linarith) hb0,
    mul_nonneg hβ0 (show (0:ℝ) ≤ 1 - b by linarith)]

theorem idM1 (hS : P.Standing) (b : ℝ) :
    probPS P b * P.cE - (probPS P b * P.cP + P.α * b * P.cE) =
      P.cE * ((1 - P.β) * b0 P - b * ((1 - P.β) * b0 P + P.α * (1 - b0 P))) := by
  rw [(b0_facts P hS).2.2.1]; unfold probPS; ring

theorem idM2 (hS : P.Standing) (b : ℝ) :
    probPC P b * P.cE - (probPC P b * P.cP + (1 - P.α) * b * P.cE) =
      P.cE * (P.β * b0 P - b * (P.β * b0 P + (1 - P.α) * (1 - b0 P))) := by
  rw [(b0_facts P hS).2.2.1]; unfold probPC; ring

theorem costTT_high (hS : P.Standing) (hI : P.Informative) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (h : bHighHigh P ≤ b) : costTT P b = P.cT + P.cE := by
  have th := thresholds P hS hI
  have hE := (b0_facts P hS).2.2.2
  have h1 := (ge_of_mul (DH_pos P hS hI) (bHH_mul P hS hI)).1 h
  obtain ⟨-, -, t3, t4, -⟩ := th
  have h2 := (ge_of_mul (x := b) (DL_pos P hS hI) (bLL_mul P hS hI)).1 (by linarith)
  have m1 := idM1 P hS b
  have m2 := idM2 P hS b
  rw [costTT_formula P hS b hb0 hb1, min_eq_left (by nlinarith), min_eq_left (by nlinarith)]
  have := pS_add_pC P b
  linear_combination P.cE * this

theorem costTT_low (hS : P.Standing) (hI : P.Informative) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (h : b ≤ bLowLow P) : costTT P b = P.cT + costPCP P b := by
  have th := thresholds P hS hI
  have hE := (b0_facts P hS).2.2.2
  obtain ⟨-, -, t3, t4, -⟩ := th
  have h1 := (le_of_mul (x := b) (DH_pos P hS hI) (bHH_mul P hS hI)).1 (by linarith)
  have h2 := (le_of_mul (DL_pos P hS hI) (bLL_mul P hS hI)).1 h
  have m1 := idM1 P hS b
  have m2 := idM2 P hS b
  rw [costTT_formula P hS b hb0 hb1, min_eq_right (by nlinarith), min_eq_right (by nlinarith)]
  have := pS_add_pC P b
  unfold costPCP
  linear_combination P.cP * this

theorem costTT_mid (hS : P.Standing) (hI : P.Informative) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hlo : bLowLow P ≤ b) (hhi : b ≤ bHighHigh P) :
    costTT P b - P.cE = P.cE * (b * ((1 - P.β) * b0 P + P.α * (1 - b0 P)) -
      ((1 - P.β) * b0 P - P.cT / P.cE)) ∧
    costTT P b - costPCP P b = P.cE * ((P.β * b0 P + P.cT / P.cE) -
      b * (P.β * b0 P + (1 - P.α) * (1 - b0 P))) := by
  have hE := (b0_facts P hS).2.2.2
  have hcP := (b0_facts P hS).2.2.1
  have hcT := cT_eq P hS
  have h1 := (le_of_mul (DH_pos P hS hI) (bHH_mul P hS hI)).1 hhi
  have h2 := (ge_of_mul (DL_pos P hS hI) (bLL_mul P hS hI)).1 hlo
  have m1 := idM1 P hS b
  have m2 := idM2 P hS b
  rw [costTT_formula P hS b hb0 hb1, min_eq_right (by nlinarith), min_eq_left (by nlinarith)]
  unfold costPCP
  rw [hcP]; rw [hcP] at m1 m2
  have hs := pS_add_pC P b
  constructor
  · unfold probPS at *; unfold probPC at *; linear_combination hcT
  · unfold probPS at *; unfold probPC at *; linear_combination hcT

theorem crossing (hS : P.Standing) (hI : P.Informative) :
    (bLow P < b0 P ↔ 0 < (1 - P.α - P.β) * b0 P * (1 - b0 P) - P.cT / P.cE) ∧
    (b0 P < bHigh P ↔ 0 < (1 - P.α - P.β) * b0 P * (1 - b0 P) - P.cT / P.cE) := by
  rw [gt_of_mul (DL_pos P hS hI) (bL_mul P hS hI), lt_of_mul (DH_pos P hS hI) (bH_mul P hS hI)]
  constructor <;> constructor <;> intro h <;> nlinarith

theorem m_posterior_straddle (P : Params) (hS : P.Standing) (hI : P.Informative) :
    (bLowLow P ≤ bLow P ∧ bHigh P ≤ bHighHigh P) ∧
    (∀ b : ℝ, 0 ≤ b → b < 1 → bHighHigh P ≤ b → b0 P ≤ bPS P b) ∧
    (∀ b : ℝ, 0 ≤ b → b ≤ 1 → b ≤ bLowLow P → bPC P b ≤ b0 P) ∧
    (∀ b : ℝ, 0 ≤ b → b ≤ 1 → bLowLow P < b → b < bHighHigh P →
      bPS P b < b0 P ∧ b0 P < bPC P b) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := thresholds P hS hI
  have hb0 := (b0_facts P hS).1
  refine ⟨⟨t1, t2⟩, ?_, ?_, ?_⟩
  · intro b h0 h1 h
    exact not_lt.1 (fun h' => absurd ((bPS_lt_iff P hS hI b (pS_pos P hS hI b h0 h1)).1 h')
      (not_lt.2 h))
  · intro b h0 h1 h
    rcases eq_or_lt_of_le (pC_nonneg P hS b h0 h1) with hp | hp
    · unfold bPC; rw [← hp, div_zero]; exact hb0.le
    · exact (bPC_le_iff P hS hI b hp).2 h
  · intro b h0 h1 hl hh
    have hbpos : 0 < b := lt_of_le_of_lt t5 hl
    have hb1 : b < 1 := lt_of_lt_of_le hh t6
    constructor
    · exact (bPS_lt_iff P hS hI b (pS_pos P hS hI b h0 hb1)).2 hh
    · exact not_le.1 (fun h' => absurd ((bPC_le_iff P hS hI b (pC_pos P hS hI b hbpos h1)).1 h')
        (not_le.2 hl))


end Teletriage.OneShot.Dev

open Teletriage.OneShot

theorem solution (P : Params) (hS : P.Standing) (hI : P.Informative) :
    (bLowLow P ≤ bLow P ∧ bHigh P ≤ bHighHigh P) ∧
    (∀ b : ℝ, 0 ≤ b → b < 1 → bHighHigh P ≤ b → b0 P ≤ bPS P b) ∧
    (∀ b : ℝ, 0 ≤ b → b ≤ 1 → b ≤ bLowLow P → bPC P b ≤ b0 P) ∧
    (∀ b : ℝ, 0 ≤ b → b ≤ 1 → bLowLow P < b → b < bHighHigh P →
      bPS P b < b0 P ∧ b0 P < bPC P b) :=
  Teletriage.OneShot.Dev.m_posterior_straddle P hS hI
