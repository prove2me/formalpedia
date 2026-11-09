-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P85.coherent_bright_noise_exponent
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T09:54:06.817401+00:00
-- url     : https://prove2.me/submissions/32d083d5-93db-4f22-81ae-118698ad70b7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P85

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Renew46.P41 (coherentProductCoefficient)

open QAlgorithms.Papers.Independent.Intakenext100.P85 in
theorem solution (k NS : ℝ)
    (hk : 0 < k) (hk1 : k < 1) (hNS : 0 ≤ NS) :
    Tendsto (fun NB : ℝ => NB * coherentExponent k NS NB)
      atTop (nhds (k * NS / 4)) := by
  have hid : ∀ NB : ℝ, 0 < NB → NB * coherentExponent k NS NB =
      k * NS * ((Real.sqrt (1 + NB⁻¹) + 1)⁻¹) ^ 2 := by
    intro NB hNB
    unfold coherentExponent
    obtain ⟨u, hu⟩ : ∃ u, u = Real.sqrt (NB + 1) := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt NB := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hNB
    have hu0 : 0 ≤ u := by rw [hu]; exact Real.sqrt_nonneg _
    have hu2 : u ^ 2 = NB + 1 := by rw [hu]; exact Real.sq_sqrt (by linarith)
    have hs2 : s ^ 2 = NB := by rw [hs]; exact Real.sq_sqrt hNB.le
    have hsq : Real.sqrt (1 + NB⁻¹) = u / s := by
      rw [hu, hs, ← Real.sqrt_div (by linarith)]
      congr 1
      rw [add_div, div_self hNB.ne', one_div]
    rw [hsq, ← hu, ← hs]
    have hus : 0 < u + s := by linarith
    have h1 : (u - s) * (u + s) = 1 := by linear_combination hu2 - hs2
    have h2 : u - s = 1 / (u + s) := by rw [eq_div_iff hus.ne']; exact h1
    have h3 : (u / s + 1)⁻¹ = s / (u + s) := by
      rw [div_add_one hs0.ne', inv_div]
    rw [h2, h3, ← hs2]
    ring
  have hlim : Tendsto (fun NB : ℝ => k * NS * ((Real.sqrt (1 + NB⁻¹) + 1)⁻¹) ^ 2)
      atTop (nhds (k * NS / 4)) := by
    have h0 : Tendsto (fun NB : ℝ => Real.sqrt (1 + NB⁻¹) + 1) atTop
        (nhds (Real.sqrt (1 + 0) + 1)) :=
      ((tendsto_const_nhds.add tendsto_inv_atTop_zero).sqrt).add tendsto_const_nhds
    have hne : Real.sqrt (1 + 0) + 1 ≠ 0 := by
      have := Real.sqrt_nonneg (1 + 0 : ℝ); linarith
    have h1 := (tendsto_const_nhds (x := k * NS)).mul ((h0.inv₀ hne).pow 2)
    have hval : k * NS * ((Real.sqrt (1 + 0) + 1)⁻¹) ^ 2 = k * NS / 4 := by
      norm_num <;> ring
    rw [hval] at h1
    exact h1
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with NB hNB
  exact (hid NB hNB).symm

end
