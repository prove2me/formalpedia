-- Prove2me | solution 1 for QualityEncroach.FixedCost.claim_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:10:20.521863+00:00
-- url     : https://prove2.me/submissions/9851d881-0197-4481-90ac-7252b2bc22c1

import Mathlib
import Definitions.Def_QualityEncroach_FixedCost_Reduced

open Filter Topology

theorem solution (k c t u : ℝ) (hk : 0 < k) (hc : 0 < c)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hu : (8 - 3 * t) * c / (8 - 5 * t) < u)
    (hopt : ∀ t' u' : ℝ, 0 < t' → t' ≤ 1 →
      (8 - 3 * t') * c / (8 - 5 * t') < u' →
      QualityEncroach.FixedCost.PiHi k c t' u' ≤ QualityEncroach.FixedCost.PiHi k c t u) :
    t = 1 := by
  by_contra hne
  have htl : t < 1 := lt_of_le_of_ne ht1 hne
  have h85 : 0 < 8 - 5 * t := by linarith
  have hupos : 0 < u := by
    have : 0 < (8 - 3 * t) * c / (8 - 5 * t) := by
      apply div_pos _ h85; nlinarith
    linarith
  -- feasibility is an open condition in `t`
  have hcont : ContinuousAt (fun s : ℝ => (8 - 3 * s) * c / (8 - 5 * s)) t := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop) (by linarith)
  have hev : ∀ᶠ s in 𝓝 t, (8 - 3 * s) * c / (8 - 5 * s) < u :=
    hcont.eventually (Iio_mem_nhds hu)
  have hev2 : ∀ᶠ s in 𝓝[>] t, ((8 - 3 * s) * c / (8 - 5 * s) < u) ∧ s ∈ Set.Ioo t 1 :=
    (hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT htl)
  obtain ⟨s, hs1, hs2, hs3⟩ := hev2.exists
  have hle := hopt s u (by linarith) hs3.le hs1
  have h85s : 0 < 8 - 5 * s := by linarith
  have key : (8 - t) / (8 - 5 * t) < (8 - s) / (8 - 5 * s) := by
    rw [div_lt_div_iff₀ h85 h85s]; nlinarith
  have key2 : c ^ 2 / u * ((8 - t) / (8 - 5 * t)) < c ^ 2 / u * ((8 - s) / (8 - 5 * s)) :=
    mul_lt_mul_of_pos_left key (by positivity)
  unfold QualityEncroach.FixedCost.PiHi at hle
  have e1 : (8 - t) * c ^ 2 / ((8 - 5 * t) * u) = c ^ 2 / u * ((8 - t) / (8 - 5 * t)) := by
    field_simp
  have e2 : (8 - s) * c ^ 2 / ((8 - 5 * s) * u) = c ^ 2 / u * ((8 - s) / (8 - 5 * s)) := by
    field_simp
  rw [e1, e2] at hle
  linarith
