-- Prove2me | solution 1 for WardropTraffic.MinTime.hasDerivAt_flow_mul_routeTime
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:38:37.044395+00:00
-- url     : https://prove2.me/submissions/4960a4fc-5eca-42ce-a442-ac64d034a741

import Definitions.Def_WardropTraffic_MinTime_Setting

theorem solution {D : ℕ} (b p : Fin D → ℝ) (hp : ∀ i, 0 < p i)
    (i : Fin D) :
    (∀ x : ℝ, x < p i →
      HasDerivAt (fun y => y * WardropTraffic.EqualTimes.routeTime b p i y) (b i / (1 - x / p i) ^ 2) x) ∧
    HasDerivAt (fun y => y * WardropTraffic.EqualTimes.routeTime b p i y) (b i) 0 := by
  have h : ∀ x : ℝ, x < p i →
      HasDerivAt (fun y => y * WardropTraffic.EqualTimes.routeTime b p i y)
        (b i / (1 - x / p i) ^ 2) x := by
    intro x hx
    have hden : 1 - x / p i ≠ 0 := ne_of_gt (by
      have := (div_lt_one (hp i)).mpr hx
      linarith)
    have hd := (hasDerivAt_id x).mul
      ((hasDerivAt_const x (b i)).div
        ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).div_const (p i))) hden)
    convert hd using 1 <;> try rfl
    simp only [Pi.div_apply, Pi.sub_apply, id_eq]
    field_simp [hden, (hp i).ne']
    <;> ring
  exact ⟨h, by simpa using h 0 (hp i)⟩

#print axioms solution
