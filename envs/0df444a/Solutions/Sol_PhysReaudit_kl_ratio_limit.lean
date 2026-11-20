-- Prove2me | solution 1 for PhysReaudit.kl_ratio_limit
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:08:29.408878+00:00
-- url     : https://prove2.me/submissions/731a2679-e72a-4062-93af-8bc26ab2c19e

import Definitions.Def_LimitedPriceChanges_LowerBound_KL

open Filter Topology LimitedPriceChanges.LowerBound

theorem solution :
    Tendsto (fun δ : ℝ => klBer (1 - δ) δ / Real.log (1 / δ)) (𝓝[>] 0) (𝓝 1) := by
  have hev : (fun δ : ℝ => (1 - 2 * δ) * (1 + Real.log (1 - δ) * (-Real.log δ)⁻¹))
      =ᶠ[𝓝[>] 0] (fun δ : ℝ => klBer (1 - δ) δ / Real.log (1 / δ)) := by
    have h1 : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [h1] with δ ⟨h0, h2⟩
    have hd1 : 0 < 1 - δ := by linarith
    have hlog : Real.log δ < 0 := Real.log_neg h0 (by linarith)
    have hne : Real.log δ ≠ 0 := hlog.ne
    simp only [klBer, sub_sub_cancel, one_div, Real.log_inv]
    rw [Real.log_div hd1.ne' h0.ne', Real.log_div h0.ne' hd1.ne']
    field_simp
    ring
  refine Tendsto.congr' hev ?_
  have hA : Tendsto (fun δ : ℝ => 1 - 2 * δ) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun δ : ℝ => 1 - 2 * δ) (𝓝 0) (𝓝 (1 - 2 * 0)) :=
      (continuous_const.sub (continuous_const.mul continuous_id)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun δ : ℝ => Real.log (1 - δ)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun δ : ℝ => Real.log (1 - δ)) (𝓝 0) (𝓝 (Real.log (1 - 0))) :=
      ((Real.continuousAt_log (by norm_num)).comp
        ((continuous_const.sub continuous_id).continuousAt)).tendsto
    simpa using this.mono_left nhdsWithin_le_nhds
  have hC : Tendsto (fun δ : ℝ => (-Real.log δ)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).inv_tendsto_atTop
  simpa using hA.mul (tendsto_const_nhds.add (hB.mul hC))
