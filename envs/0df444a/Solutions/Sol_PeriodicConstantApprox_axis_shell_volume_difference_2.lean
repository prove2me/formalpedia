-- Prove2me | solution 2 for PeriodicConstantApprox.axis_shell_volume_difference
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:14:49.741953+00:00
-- url     : https://prove2.me/submissions/822ac655-d009-487f-aefa-8de47e235f6b

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
open PeriodicConstantApprox
open Filter
variable {d : ℕ}


theorem solution (L : ℝ) :
    volume (((uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0) \
        insetAxisAlignedCell (d := d) L 1) =
      volume (insetAxisAlignedCell (d := d) (L + 1) 0) - volume (insetAxisAlignedCell (d := d) L 1) := by
  have hsub : insetAxisAlignedCell (d := d) L 1 ⊆
      uniformShellShift d (-(1/2:ℝ)) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0 := by
    intro x hx
    refine ⟨x - uniformShellShift d (-(1/2:ℝ)), ?_, by simp⟩
    intro i
    obtain ⟨h1, h2⟩ := hx i
    simp only [uniformShellShift, PiLp.sub_apply, Set.mem_Icc]
    constructor <;> (try simp) <;> linarith
  have hmeasB : MeasurableSet (insetAxisAlignedCell (d := d) L 1) := by
    have : insetAxisAlignedCell (d := d) L 1 =
        ⋂ i : Fin d, (fun x : EuclideanSpace ℝ (Fin d) => x i) ⁻¹' Set.Icc 1 (L - 1) := by
      ext x; simp [insetAxisAlignedCell]
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_Icc.preimage
      ((by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) => x i).measurable)
  have hbdd : Bornology.IsBounded (insetAxisAlignedCell (d := d) L 1) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨Real.sqrt (d * (|L| + 1) ^ 2), fun x hx => ?_⟩
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, (|L| + 1) ^ 2 := Finset.sum_le_sum (fun i _ => by
          obtain ⟨h1, h2⟩ := hx i
          rw [Real.norm_eq_abs, sq_abs]
          have : |x i| ≤ |L| + 1 :=
            abs_le.mpr ⟨by linarith [abs_nonneg L], by linarith [le_abs_self L]⟩
          have h3 := pow_le_pow_left₀ (abs_nonneg _) this 2
          rwa [sq_abs] at h3)
      _ = d * (|L| + 1) ^ 2 := by simp
  rw [measure_diff hsub hmeasB.nullMeasurableSet hbdd.measure_lt_top.ne, measure_vadd]

