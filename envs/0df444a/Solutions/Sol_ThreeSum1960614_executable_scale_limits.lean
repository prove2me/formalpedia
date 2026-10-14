-- Prove2me | solution 1 for ThreeSum1960614.executable_scale_limits
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T07:37:50.310225+00:00
-- url     : https://prove2.me/submissions/c65bd12d-9745-464e-a178-b0de81f01a7e

import Theorems.Thm_ThreeSum1960614_executable_scale_rounding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
open ThreeSum1960614 ThreeSum1960614.Schedule Filter
open scoped Topology

/- The microblock estimates use the even cube-root construction inherited
   from the pinned upstream Scales.lean. The block and band limits concern
   the new exact integer schedule, rather than the upstream 1/5 schedule. -/

private theorem micro_rounding (m : ℕ) :
    microSize m ≤ Nat.nthRoot 3 m ∧ Nat.nthRoot 3 m < microSize m + 2 := by
  have h := Nat.mod_add_div (Nat.nthRoot 3 m) 2
  have hr := Nat.mod_lt (Nat.nthRoot 3 m) (by decide : 0 < 2)
  unfold microSize
  omega

private theorem micro_atTop : Tendsto microSize atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop ((b + 2) ^ 3)] with m hm
  have hr : b + 2 ≤ Nat.nthRoot 3 m :=
    (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr hm
  have hround := (micro_rounding m).2
  omega

private theorem square_ratio :
    Tendsto (fun m : ℕ => (microSize m : ℝ) ^ 2 / m) atTop (𝓝 0) := by
  have hcast : Tendsto (fun m : ℕ => (microSize m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp micro_atTop
  apply squeeze_zero' _ _ hcast.inv_tendsto_atTop
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · filter_upwards [micro_atTop.eventually (eventually_ge_atTop 1)] with m hm
    have hx : (0 : ℝ) < microSize m := by exact_mod_cast (by omega : 0 < microSize m)
    have hc : microSize m ^ 3 ≤ m :=
      (Nat.pow_le_pow_left (micro_rounding m).1 3).trans
        (Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0)))
    have hcube : (microSize m : ℝ) ^ 3 ≤ (m : ℝ) := by exact_mod_cast hc
    have hmp : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hcube
    apply (div_le_iff₀ hmp).mpr
    simp only [Pi.inv_apply]
    rw [mul_comm ((microSize m : ℝ)⁻¹) (m : ℝ)]
    change (microSize m : ℝ) ^ 2 ≤ (m : ℝ) / microSize m
    apply (le_div_iff₀ hx).mpr
    nlinarith only [hcube]

private theorem micro_ratio :
    Tendsto (fun m : ℕ => (microSize m : ℝ) / m) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ square_ratio
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · filter_upwards [micro_atTop.eventually (eventually_ge_atTop 1)] with m hm
    have hmr : (1 : ℝ) ≤ microSize m := by exact_mod_cast hm
    exact div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg m)

theorem solution :
    Tendsto (fun m : ℕ => (microSize m : ℝ) ^ 2 / m) atTop (𝓝 0) ∧
    Tendsto (fun m : ℕ => (totalSize m : ℝ) / m) atTop (𝓝 epsilon) ∧
    Tendsto (fun m : ℕ => (bandExponent m : ℝ) / m) atTop (𝓝 ((-beta) * epsilon)) ∧
    Tendsto (fun m : ℕ => Real.log (bandDivisor m : ℝ) / m) atTop
      (𝓝 (Real.log 2 * ((-beta) * epsilon))) := by
  have htotal : Tendsto (fun m : ℕ => (totalSize m : ℝ) / m) atTop (𝓝 epsilon) := by
    have hlo : Tendsto (fun m : ℕ => epsilon - 20 * ((microSize m : ℝ) / m))
        atTop (𝓝 epsilon) := by
      simpa using tendsto_const_nhds.sub (micro_ratio.const_mul 20)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    · filter_upwards [micro_atTop.eventually (eventually_ge_atTop 1),
        eventually_ge_atTop (1 : ℕ)] with m hm hmpos
      have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hl := ((ThreeSum1960614.executable_scale_rounding m).2.2.1 (by omega)).2.le
      apply (le_div_iff₀ hmp).mpr
      calc
        _ = epsilon * (m : ℝ) - 20 * microSize m := by field_simp
        _ ≤ _ := by linarith
    · filter_upwards [micro_atTop.eventually (eventually_ge_atTop 1),
        eventually_ge_atTop (1 : ℕ)] with m hm hmpos
      have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      apply (div_le_iff₀ hmp).mpr
      have hu := ((ThreeSum1960614.executable_scale_rounding m).2.2.1 (by omega)).1
      linarith
  have hband : Tendsto (fun m : ℕ => (bandExponent m : ℝ) / m) atTop
      (𝓝 ((-beta) * epsilon)) := by
    have hid : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
    have hup := htotal.const_mul (-beta)
    have hlo : Tendsto (fun m : ℕ => (-beta) * ((totalSize m : ℝ) / m) - 1 / m)
        atTop (𝓝 ((-beta) * epsilon)) := by
      simpa only [one_div, sub_zero] using hup.sub hid
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
      have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      apply (le_div_iff₀ hmp).mpr
      have hl := (ThreeSum1960614.executable_scale_rounding m).2.2.2.2.1
      calc
        _ = (-beta) * (totalSize m : ℝ) - 1 := by field_simp
        _ ≤ _ := by linarith
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
      have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      apply (div_le_iff₀ hmp).mpr
      have hu := (ThreeSum1960614.executable_scale_rounding m).2.2.2.1
      calc
        _ ≤ (-beta) * (totalSize m : ℝ) := by linarith
        _ = _ := by field_simp
  refine ⟨square_ratio, htotal, hband, ?_⟩
  convert hband.const_mul (Real.log 2) using 1
  ext m
  rw [bandDivisor, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  ring
