-- Prove2me | solution 1 for SupportVectorMachines.Kernels.lemma_4_5_sums_of_kernels
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T04:29:53.653708+00:00
-- url     : https://prove2.me/submissions/4445d6e0-875a-4838-92c1-7bdbb8f1455e

import Mathlib
import Definitions.Def_SupportVectorMachines_Kernels_IsKernel

set_option autoImplicit false

open SupportVectorMachines.Kernels in
theorem solution {X : Type*} (α : ℝ) (hα : 0 ≤ α) (k k1 k2 : X → X → ℝ)
    (hk : IsKernel k) (hk1 : IsKernel k1) (hk2 : IsKernel k2) :
    IsKernel (fun x x' => α * k x x') ∧
      IsKernel (fun x x' => k1 x x' + k2 x x') := by
  constructor
  · obtain ⟨H, i1, i2, i3, Φ, hΦ⟩ := hk
    refine ⟨H, i1, i2, i3, fun x => Real.sqrt α • Φ x, fun x x' => ?_⟩
    show α * k x x' = inner ℝ (Real.sqrt α • Φ x) (Real.sqrt α • Φ x')
    rw [hΦ, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, Real.mul_self_sqrt hα]
  · obtain ⟨H1, a1, b1, c1, Φ1, h1⟩ := hk1
    obtain ⟨H2, a2, b2, c2, Φ2, h2⟩ := hk2
    refine ⟨WithLp 2 (H1 × H2), inferInstance, inferInstance, inferInstance,
      fun x => WithLp.toLp 2 (Φ1 x, Φ2 x), fun x x' => ?_⟩
    show k1 x x' + k2 x x' = inner ℝ (WithLp.toLp 2 (Φ1 x, Φ2 x)) (WithLp.toLp 2 (Φ1 x', Φ2 x'))
    rw [h1, h2, WithLp.prod_inner_apply]
