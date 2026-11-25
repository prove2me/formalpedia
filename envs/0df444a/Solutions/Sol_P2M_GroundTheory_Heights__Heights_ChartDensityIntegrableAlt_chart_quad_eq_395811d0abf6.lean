-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_chart_quad_eq_395811d0abf6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:44.808804+00:00
-- url     : https://prove2.me/submissions/10573121-fcfa-4bdb-9d59-8cc8fa016c8f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
namespace GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
theorem _root_.solution {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hH : M.IsHermitian)
    {C : Matrix (Fin e) (Fin e) ℂ} (hNC : M.submatrix Fin.succ Fin.succ = Cᴴ * C) {d : Fin e → ℂ}
    (hd : Cᴴ *ᵥ d = fun i => M i.succ 0) (y : Fin e → ℂ) :
    star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) =
      (M 0 0 - star d ⬝ᵥ d) + star (C *ᵥ y + d) ⬝ᵥ (C *ᵥ y + d) := by
  have h1 : star (C *ᵥ y + d) ⬝ᵥ (C *ᵥ y + d) =
      star y ⬝ᵥ ((Cᴴ * C) *ᵥ y) + star y ⬝ᵥ (Cᴴ *ᵥ d) + star (Cᴴ *ᵥ d) ⬝ᵥ y + star d ⬝ᵥ d := by
    rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add, star_mulVec, ← dotProduct_mulVec,
      ← dotProduct_mulVec, mulVec_mulVec, star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec, dotProduct_mulVec (star d) C y]
    ring
  rw [h1, ← hNC, hd]
  have hw : ∀ j : Fin e, M 0 j.succ = star (M j.succ 0) := fun j => (hH.apply 0 j.succ).symm
  simp only [dotProduct, mulVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.star_apply, star_one,
    one_mul, mul_one, submatrix_apply, hw, mul_add, Finset.sum_add_distrib]
  ring
end GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
