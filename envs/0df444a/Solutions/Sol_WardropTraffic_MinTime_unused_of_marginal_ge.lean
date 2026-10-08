-- Prove2me | solution 1 for WardropTraffic.MinTime.unused_of_marginal_ge
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:52:56.702833+00:00
-- url     : https://prove2.me/submissions/19a5e43b-b4b6-4f06-8694-0eec3dc3d9d7

import Mathlib
import Definitions.Def_WardropTraffic_MinTime_Setting
open WardropTraffic.MinTime

theorem solution {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ)
    (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i) (hQ : 0 < Q) (hQp : Q < ∑ i, p i)
    (q : Fin D → ℝ) (hmin : IsMinAvgTime b p Q q) (ε : ℝ)
    (hε : ∀ i, 0 < q i → b i / (1 - q i / p i) ^ 2 = ε) :
    ∀ j, ε ≤ b j → q j = 0 := by
  intro j hj
  have hq0 := (hmin.1.1 j).1
  have hqp := (hmin.1.1 j).2
  by_contra hne
  have hq : 0 < q j := lt_of_le_of_ne hq0 (Ne.symm hne)
  have hd0 : 0 < 1 - q j / p j := sub_pos.mpr ((div_lt_one (hp j)).mpr hqp)
  have hd1 : 1 - q j / p j < 1 := by
    have := div_pos hq (hp j)
    linarith
  have he := hε j hq
  have hm : b j = ε * (1 - q j / p j) ^ 2 :=
    (div_eq_iff (ne_of_gt (sq_pos_of_pos hd0))).mp he
  have hepos : 0 < ε := by
    rw [← he]
    exact div_pos (hb j) (sq_pos_of_pos hd0)
  have hsq : (1 - q j / p j) ^ 2 < 1 := by nlinarith
  nlinarith

#print axioms solution

