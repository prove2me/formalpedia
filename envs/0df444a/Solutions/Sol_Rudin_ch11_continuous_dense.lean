-- Prove2me | solution 1 for Rudin.ch11_continuous_dense
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:42:43.087594+00:00
-- url     : https://prove2.me/submissions/f1106c66-943c-4dbf-ab20-941c32d38741

import Mathlib
import Definitions.Def_Rudin_ch11_L2
open Filter Topology MeasureTheory Rudin
open scoped ENNReal
set_option maxHeartbeats 1000000
set_option autoImplicit false
noncomputable section
namespace RudinSetup
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
theorem memLp_of_mem (hf : Rudin.MemL2 μ f) : MemLp f 2 μ :=
  (memLp_two_iff_integrable_sq hf.1.aestronglyMeasurable).mpr hf.2

theorem inner_eq (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, conj_trivial, mul_comm]

theorem norm_eq (hf : MemLp f 2 μ) : ‖hf.toLp f‖ = Rudin.L2Norm μ f := by
  rw [← Real.sqrt_sq (norm_nonneg (hf.toLp f)), Rudin.L2Norm]
  congr 1
  rw [← real_inner_self_eq_norm_sq, inner_eq hf hf]
  simp only [pow_two]
theorem dist_eq (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    dist (hf.toLp f) (hg.toLp g) = Rudin.L2Norm μ (fun x => f x - g x) := by
  rw [dist_eq_norm, ← MemLp.toLp_sub, norm_eq]
  rfl
end RudinSetup
/-- Rudin, Theorem 11.38: the continuous functions are dense in `ℒ²` on `[a, b]`: for
`f ∈ ℒ²` on `[a, b]` and `ε > 0` there is a continuous `g` with `‖f - g‖₂ < ε`. -/
theorem solution (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : MemL2 (volume.restrict (Set.Icc a b)) f) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, Continuous g ∧
      L2Norm (volume.restrict (Set.Icc a b)) (fun x => f x - g x) < ε := by
  have hfp : MemLp f (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Set.Icc a b)) := by
    simpa using RudinSetup.memLp_of_mem hf
  obtain ⟨g, _, hg, hgc, _⟩ := hfp.exists_hasCompactSupport_integral_rpow_sub_le
    (p := (2 : ℝ)) (by norm_num) (ε := (ε / 2) ^ 2) (sq_pos_of_pos (half_pos hε))
  refine ⟨g, hgc, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  apply (Real.sqrt_le_left (le_of_lt (half_pos hε))).mpr
  simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hg

#print axioms solution
