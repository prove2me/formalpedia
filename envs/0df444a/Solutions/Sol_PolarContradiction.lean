-- Prove2me | solution 1 for PolarContradiction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:39:28.426843+00:00
-- url     : https://prove2.me/submissions/62f1f93f-09ab-4da0-8252-dc3fe21e296b

module
public import Definitions.Def_PHarmonicPoly_ABound
public import Definitions.Def_PHarmonicPoly_AbsorbK
public import Definitions.Def_PHarmonicPoly_Endgame
public import Definitions.Def_PHarmonicPoly_PolarContradiction
public import Theorems.Thm_ABound
public import Theorems.Thm_AbsorbK
public import Theorems.Thm_Endgame


set_option autoImplicit false
@[expose] public section
public section
open Real
theorem _root_.solution {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) (p a b c q κ : ℝ)
    (hp : (n : ℝ) - 1 / 13 ≤ p) (hpn : p ≤ (n : ℝ))
    (ha : 8 / 13 < a) (ha1 : a ≤ 1)
    (hq : q = a ^ 2 + b ^ 2) (hq1 : q ≤ 1)
    (hbc : b ^ 2 + c ^ 2 ≤ 1)
    (hk0 : 0 ≤ κ) (hk : κ ≤ 1 / Real.pi) :
    c - (p - 1 + ((n : ℝ) - p) / m) * a + ((n : ℝ) - 2) * κ * b
        + (p - 2) * (b ^ 2 * (c - a) / q) < 0 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have ha0 : (0 : ℝ) < a := by linarith
  have hd0 : (0 : ℝ) ≤ (n : ℝ) - p := by linarith
  have hd13 : (n : ℝ) - p ≤ 1 / 13 := by linarith
  have hp2 : (0 : ℝ) < p - 2 := by linarith
  have hk1 : (1 : ℝ) ≤ (n : ℝ) - 2 := by linarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  obtain ⟨s, hs0, hs2⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 2 = 1 - b ^ 2 :=
    ⟨Real.sqrt (1 - b ^ 2), Real.sqrt_nonneg _, Real.sq_sqrt (by linarith)⟩
  have hsq : s ^ 2 + b ^ 2 = 1 := by linarith
  have ha2s : a ^ 2 ≤ s ^ 2 := by rw [hs2]; nlinarith
  have has : a ≤ s := by
    rcases le_or_gt a s with h | h
    · exact h
    · nlinarith
  have hc2s : c ^ 2 ≤ s ^ 2 := by rw [hs2]; linarith
  have hcs : c ≤ s := by
    rcases le_or_gt c s with h | h
    · exact h
    · nlinarith
  have hq0 : (0 : ℝ) < q := by nlinarith [sq_nonneg b]
  obtain ⟨hA0, hA⟩ := ABound a b s q ha0 has hq hsq
  have hAstep : b ^ 2 * (c - a) / q ≤ b ^ 2 * (s - a) / q :=
    div_le_div_of_nonneg_right (by nlinarith [sq_nonneg b]) hq0.le
  have hAstep' : (p - 2) * (b ^ 2 * (c - a) / q) ≤ (p - 2) * (b ^ 2 * (s - a) / q) :=
    mul_le_mul_of_nonneg_left hAstep hp2.le
  have hdm : (0 : ℝ) ≤ ((n : ℝ) - p) / m * a :=
    mul_nonneg (div_nonneg hd0 (by linarith)) ha0.le
  have hcot : κ * b ≤ |b| / Real.pi := by
    have h1 : κ * b ≤ κ * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) hk0
    have h2 : κ * |b| ≤ 1 / Real.pi * |b| := mul_le_mul_of_nonneg_right hk (abs_nonneg b)
    have h3 : 1 / Real.pi * |b| = |b| / Real.pi := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hcot' : ((n : ℝ) - 2) * (κ * b) ≤ ((n : ℝ) - 2) * (|b| / Real.pi) :=
    mul_le_mul_of_nonneg_left hcot (by linarith)
  have hcot'' : ((n : ℝ) - 2) * κ * b = ((n : ℝ) - 2) * (κ * b) := by ring
  have e1 : (((n : ℝ) - 2) + 1 - ((n : ℝ) - p)) = p - 1 := by ring
  have e2 : (((n : ℝ) - 2) - ((n : ℝ) - p)) = p - 2 := by ring
  have hpa : (p - 1 + ((n : ℝ) - p) / m) * a
      = (p - 1) * a + ((n : ℝ) - p) / m * a := by ring
  have habs := AbsorbK ((n : ℝ) - 2) ((n : ℝ) - p) a b s (b ^ 2 * (s - a) / q)
      hk1 hd0 hA0 (by nlinarith)
  rw [e1, e2] at habs
  have hend := Endgame a b s ((n : ℝ) - p) hd0 hd13 ha ha1 hs0 hsq
  have hneg : s + |b| / Real.pi - (2 - ((n : ℝ) - p)) * a + b ^ 2 * (s - a) / q < 0 := by
    linarith
  have hfinal : ((n : ℝ) - 2)
      * (s + |b| / Real.pi - (2 - ((n : ℝ) - p)) * a + b ^ 2 * (s - a) / q) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) hneg
  rw [hcot'', hpa]
  linarith [habs, hfinal, hAstep', hcot', hdm, hcs]
