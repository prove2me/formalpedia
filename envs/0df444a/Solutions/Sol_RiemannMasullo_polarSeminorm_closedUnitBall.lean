-- Prove2me | solution 1 for RiemannMasullo.polarSeminorm_closedUnitBall
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:37:02.587178+00:00
-- url     : https://prove2.me/submissions/a75c48c3-cc81-41b8-a799-6b666c7422e2

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean#L334-L347
import Definitions.Def_RiemannMasullo_AppC_Duality

open Set Filter Topology Bornology
open scoped UniformConvergence UniformConvergenceCLM Pointwise
open RiemannMasullo
local instance {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [PolynormableSpace ℂ V] : ContinuousSMul ℂ V :=
  (PolynormableSpace.withSeminorms ℂ V).continuousSMul

open scoped ComplexOrder
variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
variable (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)

theorem solution
    (A : {A : Set F // IsVonNBounded (E := WeakBilin B.flip) ℂ A}) :
    (polarSeminorm B A).closedBall 0 1 = B.flip.polar A.val := by
  have hbounded : BddAbove (range fun y : A.val ↦ (normSeminorm ℂ ℂ).comp (B.flip (y : F))) := by
    apply Seminorm.bddAbove_range_iff.mpr
    intro x
    obtain ⟨r, hr⟩ := (NormedSpace.image_isVonNBounded_iff ℂ).mp
      (A.property.image (WeakBilin.eval B.flip x))
    exact ⟨r, forall_mem_range.mpr fun y ↦ hr (y : F) y.property⟩
  rw [polarSeminorm, Seminorm.closedBall_iSup hbounded 0 one_pos]
  ext x
  simp only [mem_iInter, Seminorm.mem_closedBall_zero, LinearMap.polar_mem_iff,
    Seminorm.comp_apply, coe_normSeminorm]
  exact ⟨fun h y hy ↦ h ⟨y, hy⟩, fun h y ↦ h y y.property⟩
