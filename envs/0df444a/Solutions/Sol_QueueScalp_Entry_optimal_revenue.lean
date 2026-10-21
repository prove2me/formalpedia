-- Prove2me | solution 1 for QueueScalp.Entry.optimal_revenue
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T22:18:57.743478+00:00
-- url     : https://prove2.me/submissions/c6a36657-f8b3-4c13-926b-c2c7fe9e37f0

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model
import Theorems.Thm_QueueScalp_Entry_pricing_problem
import Theorems.Thm_QueueScalp_Entry_lemma_A_1

open QueueScalp.Entry

namespace QSOptRevAux

/-- reduced revenue as a function of the buying cutoff -/
noncomputable def g (mu Lam c x : ℝ) : ℝ :=
  Lam ^ 3 * c ^ 2 * x * (c - x) / (mu ^ 2 * (mu - Lam * x))

lemma core_id (mu Lam c s x : ℝ) (hs2 : s ^ 2 = mu ^ 2 - Lam * c * mu) :
    (mu - s) ^ 2 * (mu - Lam * x) - Lam ^ 2 * x * (c - x) * mu =
      mu * (mu - s - Lam * x) ^ 2 := by
  linear_combination (-(Lam * x)) * hs2

lemma g_le (mu Lam c s x : ℝ) (hmu : 0 < mu) (hLam : 0 < Lam) (hc : 0 < c)
    (hs2 : s ^ 2 = mu ^ 2 - Lam * c * mu) (hx : Lam * x < mu) :
    g mu Lam c x ≤ Lam * c ^ 2 * (mu - s) ^ 2 / mu ^ 3 := by
  unfold g
  have hd : 0 < mu - Lam * x := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h := core_id mu Lam c s x hs2
  have h2 : Lam ^ 2 * x * (c - x) * mu ≤ (mu - s) ^ 2 * (mu - Lam * x) := by
    nlinarith [mul_nonneg hmu.le (sq_nonneg (mu - s - Lam * x))]
  have hk : 0 < Lam * c ^ 2 * mu ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h2 hk.le
  nlinarith

lemma g_eq (mu Lam c s : ℝ) (hmu : 0 < mu) (hLam : 0 < Lam) (hc : 0 < c)
    (hs2 : s ^ 2 = mu ^ 2 - Lam * c * mu) (hs0 : 0 < s) :
    g mu Lam c ((mu - s) / Lam) = Lam * c ^ 2 * (mu - s) ^ 2 / mu ^ 3 := by
  have h := core_id mu Lam c s ((mu - s) / Lam) hs2
  have e : mu - Lam * ((mu - s) / Lam) = s := by field_simp; ring
  have e2 : mu - s - Lam * ((mu - s) / Lam) = 0 := by field_simp; ring
  rw [e, e2] at h
  unfold g
  rw [e, div_eq_div_iff (by positivity) (by positivity)]
  have h' : Lam ^ 2 * ((mu - s) / Lam) * (c - (mu - s) / Lam) * mu = (mu - s) ^ 2 * s := by
    linarith [h]
  linear_combination (Lam * c ^ 2 * mu ^ 2) * h'

end QSOptRevAux

open QSOptRevAux in
theorem solution (P : Params) (hS : P.Standing)
    (Lam : ℝ) (hLam : 0 < Lam) :
    IsOptRevenue P Lam (PiStar P Lam) := by
  obtain ⟨hpp1, hpp2⟩ := pricing_problem P hS Lam hLam
  have hS' := hS
  obtain ⟨hmu, hV, -⟩ := hS'
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  set c := cSOf P Lam with hcdef
  have hc : 0 < c ∧ Lam * c < P.mu := by
    simp only [hcdef, cSOf]
    split_ifs with h
    · have : 0 < 1 / P.V := by positivity
      constructor <;> linarith
    · have hLV : 0 < 1 + Lam * P.V := by positivity
      refine ⟨by positivity, ?_⟩
      rw [mul_div_assoc', div_lt_iff₀ hLV]; nlinarith
  obtain ⟨hc0, hst⟩ := hc
  set s := Real.sqrt (P.mu ^ 2 - Lam * c * P.mu) with hsdef
  have hin : 0 < P.mu ^ 2 - Lam * c * P.mu := by nlinarith
  have hs2 : s ^ 2 = P.mu ^ 2 - Lam * c * P.mu := Real.sq_sqrt hin.le
  have hs0 : 0 < s := Real.sqrt_pos.2 hin
  have hsmu : s ≤ P.mu := by nlinarith [mul_pos (mul_pos hLam hc0) hmu]
  set M := Lam * c ^ 2 * (P.mu - s) ^ 2 / P.mu ^ 3 with hM
  have hxs : ctStar P Lam = (P.mu - s) / Lam := rfl
  -- PiStar equals M
  have hPi : PiStar P Lam = M := by
    by_cases h : Lam ≤ P.mu - 1 / P.V
    · have hc1 : c = 1 := by simp only [hcdef, cSOf, if_pos h]
      have := g_eq P.mu Lam c s hmu hLam hc0 hs2 hs0
      rw [← hM] at this
      rw [← this]
      simp only [PiStar, if_pos h, g, hxs, hc1]
      ring
    · have hc2 : c = P.mu * P.V / (1 + Lam * P.V) := by simp only [hcdef, cSOf, if_neg h]
      set t := Real.sqrt (Lam * P.V + 1) with htdef
      have ht2 : t ^ 2 = Lam * P.V + 1 := Real.sq_sqrt (by positivity)
      have ht0 : 0 < t := Real.sqrt_pos.2 (by positivity)
      have e : Real.sqrt (P.mu ^ 2 * (Lam * P.V + 1)) = P.mu * t := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hmu.le]
      have es : s = P.mu / t := by
        rw [hsdef]
        have : P.mu ^ 2 - Lam * c * P.mu = (P.mu / t) ^ 2 := by
          rw [hc2, div_pow, ht2]; field_simp; ring
        rw [this, Real.sqrt_sq (by positivity)]
      simp only [PiStar, if_neg h]
      rw [e, hM, es, hc2]
      have hLV : Lam * P.V + 1 = t ^ 2 := ht2.symm
      rw [show 1 + Lam * P.V = t ^ 2 by linarith, hLV]
      have : t ≠ 0 := ht0.ne'
      have : P.mu ≠ 0 := hmu.ne'
      field_simp
      linear_combination (t - 1) * hLV
  refine ⟨?_, ?_⟩
  · have hx0 : 0 ≤ (P.mu - s) / Lam := div_nonneg (by linarith) hLam.le
    have hxc : (P.mu - s) / Lam ≤ c := by
      rw [div_le_iff₀ hLam]
      -- μ - Λc ≤ s
      have h1 : 0 ≤ P.mu - Lam * c := by linarith
      have h2 : (P.mu - Lam * c) ^ 2 ≤ P.mu ^ 2 - Lam * c * P.mu := by
        nlinarith [mul_pos (mul_pos hLam hc0) hmu]
      have h3 := Real.abs_le_sqrt h2
      rw [← hsdef, abs_of_nonneg h1] at h3
      linarith
    obtain ⟨price, lam, q, -, hpnn, heq⟩ := hpp2 ((P.mu - s) / Lam) ⟨hx0, hxc⟩
    refine ⟨price, lam, q, c, (P.mu - s) / Lam, hpnn, heq, ?_⟩
    rw [hpp1 _ _ _ _ _ hpnn heq, hPi]
    have := g_eq P.mu Lam c s hmu hLam hc0 hs2 hs0
    simpa [g] using this
  · intro price lam q cS ct hp he
    have hcS : cS = c := lemma_A_1 P hS Lam hLam price lam q cS ct he
    rw [hpp1 _ _ _ _ _ hp he, hPi, hcS]
    have hct : Lam * ct < P.mu := by
      have := mul_le_mul_of_nonneg_left he.ct_le_cS hLam.le
      rw [hcS] at this; linarith
    have := g_le P.mu Lam c s ct hmu hLam hc0 hs2 hct
    simpa [g] using this
