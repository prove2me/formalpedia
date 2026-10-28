-- Prove2me | solution 1 for PESContracts.Linear.rent_free_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:04:35.870211+00:00
-- url     : https://prove2.me/submissions/2036eabd-f8ee-4166-9e34-5ed2a0a8da00

import Mathlib
import Definitions.Def_PESContracts_Linear_Model
open MeasureTheory

open PESContracts.Linear in
theorem solution (M : Params) (hM : M.Standing) (k : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ M.typesᶜ = 0)
    (C : DirectContract) (hC : C.Feasible M)
    (ha : Integrable C.a μ) (hP : Integrable C.P μ) :
    C.payoff k μ ≤
      ∫ θ, (k * C.a θ - cost M.h (C.a θ - θ * M.a0)) ∂μ := by
  obtain ⟨_, hh, -⟩ := hM
  have hae : ∀ᵐ θ ∂μ, θ ∈ M.types := mem_ae_iff.mpr hμ
  have hcost_eq : ∀ x, cost M.h x = M.h / 2 * (max x 0) ^ 2 := by
    intro x; unfold cost
    split_ifs with h
    · rw [max_eq_left h]
    · rw [max_eq_right (le_of_lt (not_le.mp h))]; ring
  have hcont : Continuous (fun x => cost M.h x) := by
    simp_rw [hcost_eq]; fun_prop
  have hcm : AEStronglyMeasurable (fun θ => cost M.h (C.a θ - θ * M.a0)) μ :=
    hcont.comp_aestronglyMeasurable (ha.aestronglyMeasurable.sub
      (by fun_prop : Continuous fun θ : ℝ => θ * M.a0).aestronglyMeasurable)
  have hnn : ∀ x, 0 ≤ cost M.h x := fun x => by
    rw [hcost_eq]; exact mul_nonneg (by linarith) (sq_nonneg _)
  have hci : Integrable (fun θ => cost M.h (C.a θ - θ * M.a0)) μ := by
    refine hP.mono' hcm ?_
    filter_upwards [hae] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn _)]
    have := (hC θ hθ).2.2.1
    unfold DirectContract.util at this
    linarith
  unfold DirectContract.payoff
  apply integral_mono_ae ((ha.const_mul k).sub hP) ((ha.const_mul k).sub hci)
  filter_upwards [hae] with θ hθ
  have := (hC θ hθ).2.2.1
  unfold DirectContract.util at this
  show k * C.a θ - C.P θ ≤ k * C.a θ - cost M.h (C.a θ - θ * M.a0)
  linarith
