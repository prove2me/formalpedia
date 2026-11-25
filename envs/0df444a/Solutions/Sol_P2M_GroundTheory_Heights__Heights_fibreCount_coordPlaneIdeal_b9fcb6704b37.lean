-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fibreCount_coordPlaneIdeal_b9fcb6704b37
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:45.092421+00:00
-- url     : https://prove2.me/submissions/513fa194-a6bd-4a97-9a1e-ed5952348fca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_coneSet_coordPlaneIdeal_035a9c42b072
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eq_zeroExt_of_a65a279d9723
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_zeroExt_apply_of_le_3705d4a23042
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linProj_zeroExt_b38aab75c095

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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ)
    (hπ : (coordPlaneBlock π).det ≠ 0) (w : EuclideanSpace ℂ (Fin m)) :
    fibreCount (HermNorm.std (m + k)) (coordPlaneIdeal m k) π w = 1 := by
  have hB : IsUnit (coordPlaneBlock π).det := Ne.isUnit hπ
  set x₀ : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 ((coordPlaneBlock π)⁻¹.mulVec fun i => w i)
  have hfib : {y | y ∈ coneSet (HermNorm.std (m + k)) (coordPlaneIdeal m k) ∧ linProj π y = w} =
      {zeroExt m k x₀} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, mem_coneSet_coordPlaneIdeal]
    constructor
    · rintro ⟨hy, hπy⟩
      rw [eq_zeroExt_of hy] at hπy ⊢
      congr 1
      rw [linProj_zeroExt] at hπy
      have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin m) => (coordPlaneBlock π)⁻¹.mulVec fun i => v i) hπy
      simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec] at h2
      ext i
      simp only [x₀]
      rw [← h2]
    · rintro rfl
      refine ⟨zeroExt_apply_of_le x₀, ?_⟩
      rw [linProj_zeroExt]
      ext i
      simp [x₀, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB]
  rw [fibreCount, hfib, Set.encard_singleton]
end GroundTheory.Heights₂.Heights
