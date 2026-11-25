-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.sh_jac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:25:37.659669+00:00
-- url     : https://prove2.me/submissions/2825a547-0505-4fe0-9f8d-9a2a10dab3fa

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_shG_contDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_sh_wd_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) (y : V n) (hy : y ∈ e.target) :
    jac n z g (e.symm y) = LinearMap.det (fderiv ℂ (shG n g e.symm) y : V n →ₗ[ℂ] V n) := by
  have hd : DifferentiableAt ℂ (shG n g e.symm) y :=
    ((shG_contDiffOn n z g hg e he).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt
      (by simp)
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis]
  unfold jac
  congr 1
  ext i k
  rw [Matrix.of_apply, d_comp_symm n z e he k (g i) y hy, LinearMap.toMatrix_apply]
  have hdi : DifferentiableAt ℂ (g i ∘ e.symm) y :=
    (hg i e he).differentiableAt (e.open_target.mem_nhds hy)
  rw [sh_wd_eq n k _ y hdi]
  have hcomp : HasFDerivAt (g i ∘ e.symm)
      ((EuclideanSpace.proj i : V n →L[ℂ] ℂ).comp (fderiv ℂ (shG n g e.symm) y)) y :=
    (EuclideanSpace.proj i : V n →L[ℂ] ℂ).hasFDerivAt.comp y hd.hasFDerivAt
  rw [hcomp.fderiv]
  simp [bas]
end ReciprocityTheory.L2DbarEstimates.I
