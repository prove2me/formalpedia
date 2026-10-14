-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_turing_offset
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T10:08:25.369933+00:00
-- url     : https://prove2.me/submissions/84a32b2c-206c-49db-8ee7-0a7f3c8ebcde

/- The elementary integer-offset step in Turing's method. All analytic integral
bounds and the relation to zeta's total count remain explicit inputs. -/
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0
open Set MeasureTheory

theorem solution (a c b B : ℝ) (hac : a≤c) (hcb : c≤b)
    (d : ℝ → ℤ) (S V : ℝ → ℝ)
    (hmono : MonotoneOn d (Icc a b))
    (hrel : ∀ t ∈ Icc a b, S t=(d t:ℝ)+V t)
    (hSL : IntervalIntegrable S volume a c)
    (hSR : IntervalIntegrable S volume c b)
    (hVL : IntervalIntegrable V volume a c)
    (hVR : IntervalIntegrable V volume c b)
    (hboundL : -B≤∫ t in a..c, S t)
    (hboundR : (∫ t in c..b, S t)≤B)
    (hmarginL : (∫ t in a..c, V t)<c-a-B)
    (hmarginR : B-(b-c)<∫ t in c..b, V t) : d c=0 := by
  have hc : c ∈ Icc a b := ⟨hac,hcb⟩
  by_contra hn
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hdi : (d c:ℝ)≤-1 := by
      exact_mod_cast (show d c≤-1 by omega)
    have hp : ∀ t ∈ Icc a c, S t≤V t-1 := by
      intro t ht
      have ht' : t ∈ Icc a b := ⟨ht.1,ht.2.trans hcb⟩
      have hdt : (d t:ℝ)≤(d c:ℝ) := by exact_mod_cast (hmono ht' hc ht.2)
      rw [hrel t ht']
      linarith
    have hi := intervalIntegral.integral_mono_on hac hSL
      (hVL.sub intervalIntegrable_const) hp
    rw [intervalIntegral.integral_sub hVL intervalIntegrable_const,
      intervalIntegral.integral_const] at hi
    simp only [smul_eq_mul,mul_one] at hi
    linarith
  · have hdi : 1≤(d c:ℝ) := by
      exact_mod_cast (show 1≤d c by omega)
    have hp : ∀ t ∈ Icc c b, V t+1≤S t := by
      intro t ht
      have ht' : t ∈ Icc a b := ⟨hac.trans ht.1,ht.2⟩
      have hdt : (d c:ℝ)≤(d t:ℝ) := by exact_mod_cast (hmono hc ht' ht.1)
      rw [hrel t ht']
      linarith
    have hi := intervalIntegral.integral_mono_on hcb
      (hVR.add intervalIntegrable_const) hSR hp
    rw [intervalIntegral.integral_add hVR intervalIntegrable_const,
      intervalIntegral.integral_const] at hi
    simp only [smul_eq_mul,mul_one] at hi
    linarith
