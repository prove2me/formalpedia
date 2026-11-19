-- Prove2me | solution 1 for Plasticity.exists_completeSpace_not_hasPlasticUnitBall
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-11-18T19:27:15.901217+00:00
-- url     : https://prove2.me/submissions/78a03a90-ab3e-4eb2-a6cf-b242d695eeea

import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_SeqSpace
import Definitions.Def_Plasticity_C0Sum
import Theorems.Thm_Plasticity_C0Sum_not_hasPlasticUnitBall_ell1_c0

namespace Sol_Plasticity_exists_completeSpace_not_hasPlasticUnitBall
open Plasticity Filter Topology

theorem isClosed_c0Sum {ι : Type*} (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] : IsClosed ((c0Sum E : Submodule ℝ (lp E ⊤)) : Set (lp E ⊤)) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  show Tendsto (fun i => ‖x i‖) cofinite (𝓝 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / 2) (half_pos hε)
  have hy' : Tendsto (fun i => ‖y i‖) cofinite (𝓝 0) := hy
  have h2 := (Metric.tendsto_nhds.1 hy') (ε / 2) (half_pos hε)
  filter_upwards [h2] with i hi
  have h3 : ‖x i - y i‖ ≤ ‖x - y‖ := by
    have := lp.norm_apply_le_norm (by simp : (⊤ : ENNReal) ≠ 0) (x - y) i
    simpa using this
  rw [dist_eq_norm] at hxy
  have h4 : ‖x i‖ ≤ ‖y i‖ + ‖x i - y i‖ := by
    have := norm_add_le (y i) (x i - y i); simpa [add_comm] using this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hi ⊢
  linarith

theorem isClosed_c0 (Γ : Type*) : IsClosed ((c0 Γ : Submodule ℝ (Linf Γ)) : Set (Linf Γ)) := by
  have := isClosed_c0Sum (fun _ : Γ => ℝ)
  have e : ((c0 Γ : Submodule ℝ (Linf Γ)) : Set (Linf Γ)) =
      ((c0Sum (fun _ : Γ => ℝ) : Submodule ℝ (lp (fun _ : Γ => ℝ) ⊤)) : Set (Linf Γ)) := by
    ext x
    show Tendsto (⇑x) cofinite (𝓝 0) ↔ Tendsto (fun i => ‖x i‖) cofinite (𝓝 0)
    exact tendsto_zero_iff_norm_tendsto_zero
  rw [e]; exact this

instance instC0 (Γ : Type*) : CompleteSpace (c0 Γ) := (isClosed_c0 Γ).completeSpace_coe

instance instC0Sum {ι : Type*} (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)] : CompleteSpace (c0Sum E) :=
  (isClosed_c0Sum E).completeSpace_coe

end Sol_Plasticity_exists_completeSpace_not_hasPlasticUnitBall

open Plasticity Sol_Plasticity_exists_completeSpace_not_hasPlasticUnitBall in
theorem solution :
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace ℝ Z),
      CompleteSpace Z ∧ ¬ HasPlasticUnitBall Z :=
  ⟨c0Sum (fun _ : ℕ => lp (fun _ : ℝ => ℝ) 1) × c0Sum (fun _ : ℕ => c0 ℝ), inferInstance, inferInstance, inferInstance,
    C0Sum.not_hasPlasticUnitBall_ell1_c0⟩
