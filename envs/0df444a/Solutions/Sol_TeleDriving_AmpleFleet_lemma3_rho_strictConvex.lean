-- Prove2me | solution 1 for TeleDriving.AmpleFleet.lemma3_rho_strictConvex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:18:56.466967+00:00
-- url     : https://prove2.me/submissions/becbd732-3a85-455d-a685-f545a94b49c3

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

set_option autoImplicit false
open TeleDriving.ScarceFleet

lemma td_h_concave (mu : ℕ → ℝ → ℝ) (s : ℝ) (m : ℕ) (hA1 : Assumption1 mu s) :
    StrictConcaveOn ℝ (Set.Icc (1 : ℝ) m) (fun q => q * mu m q) := by
  have hanti := hA1.2.2.2.1 m
  have hconc := hA1.2.2.2.2.1 m
  refine ⟨hconc.1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hb' : b = 1 - a := by linarith
  have hm := hconc.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at hm ⊢
  have hz : 0 < a * x + b * y := by
    have := hx.1; have := hy.1; nlinarith
  have h1 : (a * x + b * y) * (a * mu m x + b * mu m y) < (a * x + b * y) * mu m (a * x + b * y) :=
    mul_lt_mul_of_pos_left hm hz
  have hprod : 0 ≤ (x - y) * (mu m y - mu m x) := by
    rcases le_total x y with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hanti hx hy h])
    · exact mul_nonneg (by linarith) (by linarith [hanti hy hx h])
  have key : (a * x + b * y) * (a * mu m x + b * mu m y) - (a * (x * mu m x) + b * (y * mu m y))
      = a * b * ((x - y) * (mu m y - mu m x)) := by rw [hb']; ring
  nlinarith [mul_nonneg (mul_nonneg ha.le hb.le) hprod]

theorem solution (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : Assumption1 mu s)
    (hA2 : Assumption2 mu mbar) (hsize : StandingSize mu s mbar m lam) :
    StrictConvexOn ℝ (Set.Icc (1 : ℝ) m) (rho mu lam m) ∧
      StrictConcaveOn ℝ (Set.Icc (1 : ℝ) m) (fun q => 1 / rho mu lam m q) := by
  have hs : 0 < s := hA1.1
  have hlam : 0 < lam := lt_trans (by positivity) hsize.2.1
  have hH := td_h_concave mu s m hA1
  have hpos : ∀ q ∈ Set.Icc (1 : ℝ) m, 0 < q * mu m q := fun q hq =>
    mul_pos (by linarith [hq.1]) (hA1.2.1 m q hq)
  constructor
  · refine ⟨hH.1, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have h1 := hH.2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at h1 ⊢
    have hb' : b = 1 - a := by linarith
    have hxp := hpos x hx
    have hyp := hpos y hy
    have hHp : 0 < a * (x * mu m x) + b * (y * mu m y) := by positivity
    unfold rho
    have step1 : lam / ((a * x + b * y) * mu m (a * x + b * y)) <
        lam / (a * (x * mu m x) + b * (y * mu m y)) :=
      div_lt_div_of_pos_left hlam hHp h1
    have step2 : 1 / (a * (x * mu m x) + b * (y * mu m y)) ≤
        a / (x * mu m x) + b / (y * mu m y) := by
      rw [div_add_div _ _ hxp.ne' hyp.ne', div_le_div_iff₀ hHp (mul_pos hxp hyp)]
      have key : (a * (y * mu m y) + (x * mu m x) * b) * (a * (x * mu m x) + b * (y * mu m y))
          - 1 * ((x * mu m x) * (y * mu m y)) = a * b * (x * mu m x - y * mu m y) ^ 2 := by
        rw [hb']; ring
      nlinarith [mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg (x * mu m x - y * mu m y))]
    have step3 : lam / (a * (x * mu m x) + b * (y * mu m y)) ≤
        a * (lam / (x * mu m x)) + b * (lam / (y * mu m y)) := by
      have := mul_le_mul_of_nonneg_left step2 hlam.le
      calc lam / (a * (x * mu m x) + b * (y * mu m y))
          = lam * (1 / (a * (x * mu m x) + b * (y * mu m y))) := by rw [mul_one_div]
        _ ≤ lam * (a / (x * mu m x) + b / (y * mu m y)) := this
        _ = a * (lam / (x * mu m x)) + b * (lam / (y * mu m y)) := by ring
    linarith
  · refine ⟨hH.1, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have h1 := hH.2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at h1 ⊢
    unfold rho
    have e : ∀ q : ℝ, 1 / (lam / (q * mu m q)) = q * mu m q / lam := fun q => by
      rw [one_div_div]
    simp only [e]
    have := div_lt_div_of_pos_right h1 hlam
    calc a * (x * mu m x / lam) + b * (y * mu m y / lam)
        = (a * (x * mu m x) + b * (y * mu m y)) / lam := by ring
      _ < _ := this
