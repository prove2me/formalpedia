-- Prove2me | solution 1 for SamuelCahnProphet.IID.tendsto_Q_two
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T21:46:06.325993+00:00
-- url     : https://prove2.me/submissions/df322e31-b7f2-420c-879d-12a4874a5131

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology


namespace SamuelCahnProphet.IID

theorem Q_two_core :
    Tendsto (fun p : ℝ × ℝ => Q p.1 p.2) ((𝓝[>] (0 : ℝ)) ×ˢ atTop) (𝓝 2) := by
  set F : Filter (ℝ × ℝ) := (𝓝[>] (0 : ℝ)) ×ˢ atTop with hF
  have tb : Tendsto Prod.fst F (𝓝[>] (0:ℝ)) := tendsto_fst
  have tc : Tendsto Prod.snd F atTop := tendsto_snd
  have tb0 : Tendsto Prod.fst F (𝓝 (0:ℝ)) := tb.mono_right nhdsWithin_le_nhds
  have bpos : ∀ᶠ p in F, 0 < p.1 := tb.eventually self_mem_nhdsWithin
  have cpos : ∀ᶠ p in F, 0 < p.2 := tc.eventually (eventually_gt_atTop 0)
  have hlt : ∀ t : ℝ, 0 < t → Real.exp (-t) < 1 := by
    intro t ht
    have := Real.exp_lt_exp.2 (show -t < 0 by linarith); simpa using this
  have hx : Tendsto (fun p : ℝ × ℝ => Real.exp (-p.1)) F (𝓝 1) := by
    have := (Real.continuous_exp.tendsto (-0)).comp tb0.neg
    simpa [Function.comp_def] using this
  have hy : Tendsto (fun p : ℝ × ℝ => Real.exp (-p.2)) F (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tc
  have hxy : ∀ p : ℝ × ℝ, Real.exp (-p.1 - p.2) = Real.exp (-p.1) * Real.exp (-p.2) := by
    intro p; rw [sub_eq_add_neg, Real.exp_add]
  have hz : Tendsto (fun p : ℝ × ℝ => Real.exp (-p.1) * Real.exp (-p.2)) F (𝓝 0) := by
    simpa using hx.mul hy
  -- second term
  have h2 : Tendsto (fun p : ℝ × ℝ => (Real.exp (-p.1) - Real.exp (-p.1) * Real.exp (-p.2)) /
      (1 - Real.exp (-p.1) * Real.exp (-p.2))) F (𝓝 1) := by
    have h := (hx.sub hz).div (tendsto_const_nhds.sub hz) (by norm_num : (1:ℝ) - 0 ≠ 0)
    rw [show ((1:ℝ) - 0) / (1 - 0) = 1 by norm_num] at h
    exact h
  -- ratio b/(1-x)
  have hA : Tendsto (fun p : ℝ × ℝ => p.1 / (1 - Real.exp (-p.1))) F (𝓝 1) := by
    have hinv : Tendsto (fun p : ℝ × ℝ => (Real.exp (-p.1))⁻¹) F (𝓝 1) := by
      simpa using hx.inv₀ (by norm_num)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
    · filter_upwards [bpos] with p hp
      have h1 : 1 - Real.exp (-p.1) ≤ p.1 := by
        have := Real.add_one_le_exp (-p.1); linarith
      have h0 : 0 < 1 - Real.exp (-p.1) := by
        have := hlt p.1 hp; linarith
      rw [le_div_iff₀ h0]; linarith
    · filter_upwards [bpos] with p hp
      have h1 : p.1 * Real.exp (-p.1) < 1 - Real.exp (-p.1) := by
        have := Real.add_one_lt_exp (x := p.1) hp.ne'
        have h2 : Real.exp p.1 * Real.exp (-p.1) = 1 := by rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (-p.1)]
      have h0 : 0 < 1 - Real.exp (-p.1) := by
        have := hlt p.1 hp; linarith
      rw [div_le_iff₀ h0, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos _)]
      linarith
  -- third term: A * B * (1/c) where B = (x - xy)^2/(1 - xy)
  have hB : Tendsto (fun p : ℝ × ℝ => (Real.exp (-p.1) - Real.exp (-p.1) * Real.exp (-p.2)) ^ 2 /
      (1 - Real.exp (-p.1) * Real.exp (-p.2))) F (𝓝 1) := by
    have h := ((hx.sub hz).pow 2).div (tendsto_const_nhds.sub hz) (by norm_num : (1:ℝ) - 0 ≠ 0)
    rw [show ((1:ℝ) - 0) ^ 2 / (1 - 0) = 1 by norm_num] at h
    exact h
  have hC : Tendsto (fun p : ℝ × ℝ => (p.2)⁻¹) F (𝓝 0) := tendsto_inv_atTop_zero.comp tc
  have h3 : Tendsto (fun p : ℝ × ℝ => (p.1 / (1 - Real.exp (-p.1))) *
      ((Real.exp (-p.1) - Real.exp (-p.1) * Real.exp (-p.2)) ^ 2 /
      (1 - Real.exp (-p.1) * Real.exp (-p.2))) * (p.2)⁻¹) F (𝓝 0) := by
    simpa using (hA.mul hB).mul hC
  have := (tendsto_const_nhds (x := (1:ℝ))).add h2 |>.sub h3
  have e : (1:ℝ) + 1 - 0 = 2 := by norm_num
  rw [e] at this
  refine this.congr' ?_
  filter_upwards [bpos, cpos] with p hp hq
  unfold Q
  rw [hxy p]
  have h0 : 0 < 1 - Real.exp (-p.1) := by
    have := hlt p.1 hp; linarith
  have h1 : 0 < 1 - Real.exp (-p.1) * Real.exp (-p.2) := by
    have a1 : Real.exp (-p.1) < 1 := by linarith
    have a2 : Real.exp (-p.2) < 1 := hlt p.2 hq
    nlinarith [Real.exp_pos (-p.1), Real.exp_pos (-p.2)]
  field_simp

end SamuelCahnProphet.IID

open SamuelCahnProphet.IID


theorem solution :
    Tendsto (fun p : ℝ × ℝ => Q p.1 p.2) ((𝓝[>] (0 : ℝ)) ×ˢ atTop) (𝓝 2) := by
  exact Q_two_core
