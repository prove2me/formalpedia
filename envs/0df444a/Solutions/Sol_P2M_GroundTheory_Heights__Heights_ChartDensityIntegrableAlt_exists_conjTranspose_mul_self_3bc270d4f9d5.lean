-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_exists_conjTranspose_mul_self_3bc270d4f9d5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:40.281422+00:00
-- url     : https://prove2.me/submissions/a282e04a-a604-4b27-b8c1-6ed4d3afaeb4

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
theorem _root_.solution {e : ℕ} {N : Matrix (Fin e) (Fin e) ℂ} (hN : N.PosDef) :
    ∃ C : Matrix (Fin e) (Fin e) ℂ, N = Cᴴ * C ∧ C.det ≠ 0 := by
  obtain ⟨U, l, hl, hspec⟩ : ∃ (U : Matrix (Fin e) (Fin e) ℂ) (l : Fin e → ℝ), (∀ k, 0 ≤ l k) ∧
      N = U * diagonal (fun k => (l k : ℂ)) * star U := by
    refine ⟨(hN.1.eigenvectorUnitary : Matrix (Fin e) (Fin e) ℂ), hN.1.eigenvalues,
      fun k => (hN.eigenvalues_pos k).le, ?_⟩
    have h := hN.1.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h
    exact h
  set s : Fin e → ℂ := fun k => ((Real.sqrt (l k) : ℝ) : ℂ) with hs
  have hss : (fun i => star s i * s i) = fun k => (l k : ℂ) := by
    funext k
    simp only [hs, Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hl k)]
  have hNC : N = (diagonal s * star U)ᴴ * (diagonal s * star U) := by
    rw [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose, diagonal_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal (star s)), diagonal_mul_diagonal, hss, hspec,
      star_eq_conjTranspose, Matrix.mul_assoc]
  refine ⟨diagonal s * star U, hNC, fun h => ?_⟩
  have hdet := (hN.det_pos).ne'
  rw [hNC, det_mul, h, mul_zero] at hdet
  exact hdet rfl
end GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
