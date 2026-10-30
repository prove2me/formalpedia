-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P28.proposition59
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:13:43.21471+00:00
-- url     : https://prove2.me/submissions/05c14f04-df4c-4f32-b793-432a11e675ef

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

open QAlgorithms.Papers.Independent.Extend50.P28

namespace S108Q

theorem inv_eq (x : ℝ) (hx : 0 < x) : inverseRoot x = x ^ (-(1/2 : ℝ)) := by
  unfold inverseRoot
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hx.le]

theorem ev_eq (x : ℝ) (hx : 0 < x) : inverseRoot =ᶠ[nhds x] fun y => y ^ (-(1/2 : ℝ)) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy using inv_eq y hy

theorem d1 (x : ℝ) (hx : 0 < x) :
    deriv inverseRoot x = (-(1/2 : ℝ)) * x ^ (-(1/2 : ℝ) - 1) := by
  rw [(ev_eq x hx).deriv_eq, Real.deriv_rpow_const]

theorem ev_d1 (x : ℝ) (hx : 0 < x) :
    deriv inverseRoot =ᶠ[nhds x] fun y => (-(1/2 : ℝ)) * y ^ (-(1/2 : ℝ) - 1) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy using d1 y hy

theorem d2 (x : ℝ) (hx : 0 < x) :
    deriv (deriv inverseRoot) x = (3 / 4 : ℝ) * Real.rpow x (-5 / 2 : ℝ) := by
  rw [(ev_d1 x hx).deriv_eq, deriv_const_mul _ (Real.differentiableAt_rpow_const_of_ne _ hx.ne'),
    Real.deriv_rpow_const]
  have : (-(1/2 : ℝ) - 1 - 1) = -5/2 := by norm_num
  rw [this]
  show _ = (3/4 : ℝ) * x ^ (-5/2 : ℝ)
  ring

end S108Q

open S108Q

theorem solution :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) inverseRoot ∧
    ∀ x : ℝ, 0 < x →
      deriv (deriv inverseRoot) x = (3 / 4 : ℝ) * Real.rpow x (-5 / 2 : ℝ) ∧
      0 ≤ deriv (deriv inverseRoot) x := by
  have key : ∀ x : ℝ, 0 < x →
      deriv (deriv inverseRoot) x = (3 / 4 : ℝ) * Real.rpow x (-5 / 2 : ℝ) ∧
      0 ≤ deriv (deriv inverseRoot) x := by
    intro x hx
    refine ⟨d2 x hx, ?_⟩
    rw [d2 x hx]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hx.le _)
  refine ⟨?_, key⟩
  have hc : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun y : ℝ => y ^ (-(1/2 : ℝ))) := by
    apply convexOn_of_deriv2_nonneg (convex_Ioi 0)
    · exact fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hy))).continuousWithinAt
    · intro y hy
      exact (Real.differentiableAt_rpow_const_of_ne _ (ne_of_gt (by simpa using hy))).differentiableWithinAt
    · intro y hy
      have hy' : 0 < y := by simpa using hy
      have := fun z (hz : 0 < z) => Real.deriv_rpow_const z (-(1/2 : ℝ))
      have he : deriv (fun y : ℝ => y ^ (-(1/2 : ℝ))) =ᶠ[nhds y]
          fun z => (-(1/2 : ℝ)) * z ^ (-(1/2 : ℝ) - 1) := by
        filter_upwards [Ioi_mem_nhds hy'] with z hz using this z hz
      exact (((Real.differentiableAt_rpow_const_of_ne _ hy'.ne').const_mul _).congr_of_eventuallyEq
        he).differentiableWithinAt
    · intro y hy
      have hy' : 0 < y := by simpa using hy
      have h1 := key y hy'
      have hd : deriv (deriv fun y : ℝ => y ^ (-(1/2 : ℝ))) y = deriv (deriv inverseRoot) y := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [Ioi_mem_nhds hy'] with z hz
        exact ((ev_eq z hz).deriv_eq).symm
      show 0 ≤ deriv (deriv fun y : ℝ => y ^ (-(1/2 : ℝ))) y
      rw [hd]; exact h1.2
  exact hc.congr (fun y hy => (inv_eq y hy).symm)
