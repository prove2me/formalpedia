-- Prove2me | solution 1 for RayBundle.four_point_of_dense_image
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-10-08T19:38:28.951893+00:00
-- url     : https://prove2.me/submissions/8d9e5c1e-31f3-4300-beb7-f6ce7fc8240f

import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Basic

-- Source: RayBundle.Thm_Cayley_four_point_of_dense_image
namespace RayBundle

end RayBundle

open RayBundle
universe u
/-- A uniformly dense vertex image transfers a four-point inequality to the entire space. -/
theorem solution {X V : Type*} [MetricSpace X] (f : V → X) (R C : ℝ)
    (hnear : ∀ x, ∃ v, dist x (f v) ≤ R)
    (hfour : ∀ a b c d, dist (f a) (f b) + dist (f c) (f d) ≤
      max (dist (f a) (f c) + dist (f b) (f d))
        (dist (f a) (f d) + dist (f b) (f c)) + C) (a b c d : X) :
    dist a b + dist c d ≤
      max (dist a c + dist b d) (dist a d + dist b c) + (C + 8 * R) := by
  obtain ⟨av, ha⟩ := hnear a
  obtain ⟨bv, hb⟩ := hnear b
  obtain ⟨cv, hc⟩ := hnear c
  obtain ⟨dv, hd⟩ := hnear d
  have approx (x y : X) (v w : V) (hx : dist x (f v) ≤ R) (hy : dist y (f w) ≤ R) :
      dist x y ≤ dist (f v) (f w) + 2 * R ∧
      dist (f v) (f w) ≤ dist x y + 2 * R := by
    have h1 := dist_triangle4 x (f v) (f w) y
    have h2 := dist_triangle4 (f v) x y (f w)
    rw [dist_comm (f w) y] at h1
    rw [dist_comm (f v) x] at h2
    constructor <;> linarith
  have hab := approx a b av bv ha hb
  have hcd := approx c d cv dv hc hd
  have hac := approx a c av cv ha hc
  have hbd := approx b d bv dv hb hd
  have had := approx a d av dv ha hd
  have hbc := approx b c bv cv hb hc
  have hmax : max (dist (f av) (f cv) + dist (f bv) (f dv))
      (dist (f av) (f dv) + dist (f bv) (f cv)) ≤
      max (dist a c + dist b d) (dist a d + dist b c) + 4 * R := by
    apply max_le
    · linarith [le_max_left (dist a c + dist b d) (dist a d + dist b c)]
    · linarith [le_max_right (dist a c + dist b d) (dist a d + dist b c)]
  linarith [hfour av bv cv dv]

namespace RayBundle


end RayBundle
