-- Prove2me | solution 1 for ReciprocityTheory.AnForm.Osgood.kern_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:35.810695+00:00
-- url     : https://prove2.me/submissions/aa24d3df-c9c1-4a69-a8b5-804b9ef4529c

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_OsgoodA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_torusMap_sub_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.AnForm.Osgood
open Complex Metric MeasureTheory Set Filter Topology
open scoped Real
variable {n : ℕ}
private theorem cubeCoord_sub_smul_one_apply (c z : Fin n → ℂ) (r : ℝ) (i : Fin n) (θ : Cube n) :
    (cubeCoord c r i - z i • (1 : C(Cube n, ℂ))) θ = torusMap c (fun _ => r) θ.1 i - z i := by
  simp [cubeCoord]
private theorem cubeCoord_sub_smul_one_ne_zero_of_mem_ball {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r) (i : Fin n)
    (θ : Cube n) : (cubeCoord c r i - z i • (1 : C(Cube n, ℂ))) θ ≠ 0 := by
  rw [cubeCoord_sub_smul_one_apply]
  exact torusMap_sub_ne hr hz θ.1 i
private theorem continuousMap_isUnit_of_forall_ne_zero {X : Type*} [TopologicalSpace X] (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0) :
    IsUnit g :=
  ⟨⟨g, ⟨fun x => (g x)⁻¹, g.continuous.inv₀ hg⟩, by ext x; simp [hg x], by ext x; simp [hg x]⟩, rfl⟩
private theorem continuousMap_ring_inverse_apply {X : Type*} [TopologicalSpace X] (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0)
    (x : X) : Ring.inverse g x = (g x)⁻¹ := by
  obtain ⟨u, rfl⟩ := continuousMap_isUnit_of_forall_ne_zero g hg
  rw [Ring.inverse_unit]
  exact eq_inv_of_mul_eq_one_right (by rw [← ContinuousMap.mul_apply, Units.mul_inv, ContinuousMap.one_apply])
end ReciprocityTheory.AnForm.Osgood
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.Osgood
open Complex Metric MeasureTheory Set Filter Topology
open scoped Real
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.Osgood
theorem _root_.solution {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r) (θ : Cube n) :
    kern c r z θ = ∏ i, (torusMap c (fun _ => r) θ.1 i - z i)⁻¹ := by
  unfold kern
  simp only [ContinuousMap.coe_prod, Finset.prod_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [continuousMap_ring_inverse_apply _ (cubeCoord_sub_smul_one_ne_zero_of_mem_ball hr hz i) θ, cubeCoord_sub_smul_one_apply]
end ReciprocityTheory.AnForm.Osgood
