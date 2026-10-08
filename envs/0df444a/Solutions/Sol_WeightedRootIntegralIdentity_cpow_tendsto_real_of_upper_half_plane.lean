-- Prove2me | solution 1 for WeightedRootIntegralIdentity.cpow_tendsto_real_of_upper_half_plane
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-14T20:54:32.177061+00:00
-- url     : https://prove2.me/submissions/6354904f-606d-4447-aceb-adf5f2dd7fac

import Mathlib
open Filter Set Topology

theorem solution (b w : ℝ) (hb : b ≠ 0) :
    Tendsto (fun ε : ℝ => ((b : ℂ) + ε * Complex.I) ^ (w : ℂ))
      (𝓝[>] 0) (𝓝 ((b : ℂ) ^ (w : ℂ))) := by
  have hbase : Tendsto (fun ε : ℝ => (b : ℂ) + ε * Complex.I)
      (𝓝[>] 0) (𝓝 (b : ℂ)) := by
    have hcast : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt
    have h : Tendsto (fun ε : ℝ => (b : ℂ) + ε * Complex.I)
        (𝓝 0) (𝓝 (b : ℂ)) := by
      simpa using tendsto_const_nhds.add (hcast.mul_const Complex.I)
    exact h.mono_left inf_le_left
  by_cases hbpos : 0 < b
  · apply (continuousAt_cpow_const (b := (w : ℂ)) ?_).tendsto.comp hbase
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using hbpos
  · have hbneg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbpos) hb
    have hbase_nonneg : Tendsto (fun ε : ℝ => (b : ℂ) + ε * Complex.I)
        (𝓝[>] 0) (𝓝[{z : ℂ | 0 ≤ z.im}] (b : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hbase, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      simpa using le_of_lt hε
    have hlog : Tendsto
        (fun ε : ℝ => Complex.log ((b : ℂ) + ε * Complex.I))
        (𝓝[>] 0) (𝓝 (Complex.log (b : ℂ))) := by
      apply (Complex.continuousWithinAt_log_of_re_neg_of_im_zero ?_ ?_).tendsto.comp hbase_nonneg
      · simpa using hbneg
      · simp
    have hexp := Complex.continuous_exp.continuousAt.tendsto.comp
      (hlog.mul_const (w : ℂ))
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb)]
    apply hexp.congr'
    filter_upwards with ε
    rw [Complex.cpow_def_of_ne_zero]
    · rfl
    · intro hz
      apply hb
      have hre := congrArg Complex.re hz
      simpa using hre
