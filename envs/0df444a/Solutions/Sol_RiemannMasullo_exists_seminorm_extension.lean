-- Prove2me | solution 1 for RiemannMasullo.exists_seminorm_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:16:40.486752+00:00
-- url     : https://prove2.me/submissions/6f7cabcf-6cec-469f-be9a-07e99e92851e

module
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Definitions.Def_RiemannMasullo_ForMathlib_Analysis_LocallyConvex_WithSeminorms

set_option autoImplicit false
@[expose] public section
public section
open Set Topology
open RiemannMasullo
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [PolynormableSpace 𝕜 F]
namespace RiemannMasullo
theorem _root_.solution {f : E →ₗ[𝕜] F} (hf : IsInducing f)
    {p : Seminorm 𝕜 E} (hp : Continuous p) :
    ∃ q : Seminorm 𝕜 F, Continuous q ∧ q.comp f = p := by
  obtain ⟨q, hq, hpq⟩ := p.exists_le_comp_of_isInducing hp hf
  let cost (y : F) (x : E) := p x + q (y - f x)
  have hbounded (y : F) : BddBelow (range (cost y)) :=
    ⟨0, forall_mem_range.mpr fun x ↦ add_nonneg (apply_nonneg p x) (apply_nonneg q _)⟩
  let r (y : F) := ⨅ x, cost y x
  have hr_le (y : F) (x : E) : r y ≤ cost y x := ciInf_le (hbounded y) x
  have hrq (y : F) : r y ≤ q y := by simpa [cost] using hr_le y 0
  have hr_zero : r 0 = 0 :=
    le_antisymm ((hrq 0).trans_eq (map_zero q)) (le_ciInf fun x ↦
      add_nonneg (apply_nonneg p x) (apply_nonneg q _))
  let r' : Seminorm 𝕜 F := Seminorm.ofSMulLE r hr_zero (fun y z ↦ by
    refine le_ciInf_add_ciInf fun x w ↦ (hr_le (y + z) (x + w)).trans ?_
    dsimp only [cost]
    rw [map_add f, add_sub_add_comm, add_add_add_comm]
    exact add_le_add (map_add_le_add p _ _) (map_add_le_add q _ _)) (fun a y ↦ by
    rw [show r y = ⨅ x, cost y x from rfl, Real.mul_iInf_of_nonneg (norm_nonneg a)]
    refine le_ciInf fun x ↦ (hr_le (a • y) (a • x)).trans_eq ?_
    simp only [cost, map_smul, ← smul_sub, map_smul_eq_mul, mul_add])
  refine ⟨r', Seminorm.continuous_of_le hq hrq, Seminorm.ext fun x ↦ ?_⟩
  change r (f x) = p x
  refine le_antisymm (by simpa [cost] using hr_le (f x) x) (le_ciInf fun w ↦ ?_)
  exact (le_map_add_map_sub p x w).trans (add_le_add_right (by
    simpa only [Seminorm.comp_apply, map_sub] using hpq (x - w)) _)
end RiemannMasullo
