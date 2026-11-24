-- Prove2me | solution 1 for ReciprocityTheory.AnForm.Osgood.kern_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:35.616782+00:00
-- url     : https://prove2.me/submissions/50191513-e19d-45fb-812d-3e158e7a4d3b

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
theorem _root_.solution (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) : AnalyticAt ℂ (kern c r) c := by
  have hK : kern c r = ∏ i ∈ Finset.univ,
      fun z : Fin n → ℂ => Ring.inverse (cubeCoord c r i - z i • (1 : C(Cube n, ℂ))) := by
    funext z
    rw [Finset.prod_apply]
    rfl
  rw [hK]
  refine Finset.analyticAt_prod _ fun i _ => ?_
  have hlin : AnalyticAt ℂ (fun z : Fin n → ℂ => z i • (1 : C(Cube n, ℂ))) c :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).smulRight
      (1 : C(Cube n, ℂ))).analyticAt c
  obtain ⟨u, hu⟩ := continuousMap_isUnit_of_forall_ne_zero _ (cubeCoord_sub_smul_one_ne_zero_of_mem_ball hr (mem_ball_self hr) i)
  exact (analyticAt_inverse (𝕜 := ℂ) u).comp_of_eq (analyticAt_const.sub hlin) hu.symm
end ReciprocityTheory.AnForm.Osgood
