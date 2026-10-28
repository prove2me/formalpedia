-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.networkOptimum
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T23:18:01.662988+00:00
-- url     : https://prove2.me/submissions/2e3d4b31-85bd-438c-b7eb-f47ed5d70a99

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)


namespace P25NetH

lemma gle (t : ℝ) : t * Real.exp (-t) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (t-1)
  have : t * Real.exp (-t) ≤ Real.exp (t-1) * Real.exp (-t) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  rw [← Real.exp_add] at this; ring_nf at this ⊢; linarith

lemma geq (t : ℝ) (h : t * Real.exp (-t) = Real.exp (-1)) : t = 1 := by
  by_contra hne
  have h1 := Real.add_one_lt_exp (show t - 1 ≠ 0 from sub_ne_zero.mpr hne)
  have : t * Real.exp (-t) < Real.exp (t-1) * Real.exp (-t) :=
    mul_lt_mul_of_pos_right (by linarith) (Real.exp_pos _)
  rw [← Real.exp_add] at this; ring_nf at this h; linarith

lemma gmono (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ 1) :
    s * Real.exp (-s) ≤ t * Real.exp (-t) := by
  have h := Real.add_one_le_exp (-(t-s))
  have e : Real.exp (-s) = Real.exp (-t) * Real.exp (t-s) := by rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-t) = Real.exp (-s) * Real.exp (-(t-s)) := by rw [← Real.exp_add]; ring_nf
  rw [e2]
  have hp := Real.exp_pos (-s)
  have : s ≤ t * Real.exp (-(t-s)) := by nlinarith
  nlinarith

end P25NetH

/-- Eqs.(79)–(80), PDF p.40: continuous device-count relaxation, including the
unique unconstrained optimum and the finite-chain constrained optimizer. -/
theorem solution (C L target a k alpha : ℝ) (hC : 0 < C) (hL : 0 < L)
    (htarget : 0 < target) (ha : 0 < a) (hk : 0 < k) (halpha : 0 < alpha) :
    let K := fun ell : ℝ => a*Real.rpow 10 (-k*alpha*ell/10)
    let opt := 10/(k*alpha*Real.log 10)
    0 < opt ∧
    (∀ ell : ℝ, 0 < ell → networkCost C L target ell (K ell) = C*L*target/(ell*K ell)) ∧
    (∀ ell : ℝ, 0 < ell → ell*K ell ≤ opt*K opt ∧
      (ell*K ell = opt*K opt ↔ ell = opt) ∧
      networkCost C L target opt (K opt) ≤ networkCost C L target ell (K ell)) ∧
    (∀ ell : ℝ, 0 < ell → ell ≤ L → ell*K ell ≤ min L opt*K (min L opt)) := by
  intro K opt
  set b := k*alpha*Real.log 10/10 with hb
  have hl : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hbpos : 0 < b := by positivity
  have hopt : opt = 1/b := by simp only [opt, hb]; field_simp
  have hK : ∀ ell, K ell = a*Real.exp (-(b*ell)) := by
    intro ell; simp only [K]
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (by norm_num)]
    congr 2; rw [hb]; ring
  have hKpos : ∀ ell, 0 < K ell := fun ell => by rw [hK]; positivity
  -- b * (ell*K ell) = a * g(b ell)
  have hprod : ∀ ell, ell * K ell = (a/b) * ((b*ell) * Real.exp (-(b*ell))) := by
    intro ell; rw [hK]; field_simp
  have hoptK : opt * K opt = (a/b) * Real.exp (-1) := by
    rw [hprod, hopt]; field_simp
  have habpos : 0 < a/b := by positivity
  have hoptpos : 0 < opt := by rw [hopt]; positivity
  have hmax : ∀ ell, ell * K ell ≤ opt * K opt := by
    intro ell; rw [hprod, hoptK]
    exact mul_le_mul_of_nonneg_left (P25NetH.gle _) habpos.le
  have hcost : ∀ ell : ℝ, 0 < ell → networkCost C L target ell (K ell) = C*L*target/(ell*K ell) := by
    intro ell hell; unfold networkCost networkCount
    have := hKpos ell; field_simp
  refine ⟨hoptpos, hcost, fun ell hell => ⟨hmax ell, ⟨fun h => ?_, fun h => by rw [h]⟩, ?_⟩, fun ell hell hellL => ?_⟩
  · rw [hprod, hoptK] at h
    have h2 := P25NetH.geq _ (mul_left_cancel₀ habpos.ne' h)
    rw [hopt]; field_simp; linarith
  · rw [hcost ell hell, hcost opt hoptpos]
    have h1 := mul_pos hell (hKpos ell)
    exact div_le_div_of_nonneg_left (by positivity) h1 (hmax ell)
  · rcases le_total L opt with hLo | hLo
    · rw [min_eq_left hLo, hprod, hprod]
      apply mul_le_mul_of_nonneg_left _ habpos.le
      apply P25NetH.gmono _ _ (by positivity) (mul_le_mul_of_nonneg_left hellL hbpos.le)
      have : b * opt = 1 := by rw [hopt]; field_simp
      nlinarith
    · rw [min_eq_right hLo]; exact hmax ell




