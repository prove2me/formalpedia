-- Prove2me | solution 1 for WardropTraffic.EqualTimes.flow_eq_of_used
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:17:58.689201+00:00
-- url     : https://prove2.me/submissions/dcd5ba21-1c8a-44e5-af6e-f0208418156d

import Mathlib
import Definitions.Def_WardropTraffic_EqualTimes_Setting

open WardropTraffic.EqualTimes

theorem solution {D : ℕ} (b p : Fin D → ℝ) (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i)
    (Q t : ℝ) (q : Fin D → ℝ) (h : IsEqualTimes b p Q q t) :
    ∀ i, 0 < q i → q i = p i * (1 - b i / t) := by
  intro i hi
  have hd : 0 < 1 - q i / p i := by
    have := (div_lt_one (hp i)).mpr (h.1.1 i).2
    linarith
  have ht := h.2.1 i hi
  unfold routeTime at ht
  have htp : 0 < t := ht ▸ div_pos (hb i) hd
  have he := (div_eq_iff (ne_of_gt hd)).mp ht
  have hp0 := ne_of_gt (hp i)
  have ht0 := ne_of_gt htp
  field_simp at he ⊢
  nlinarith [he]

#print axioms solution
