-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarIntAdd_abs_chartDens_le_0d8d1be60cc4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:46.003871+00:00
-- url     : https://prove2.me/submissions/a0365c7e-98eb-46d2-ae30-8135364f9953

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntAdd

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
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.VarIntAdd
namespace GroundTheory.Heights₂.Heights.VarIntAdd
theorem _root_.solution {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin k) (Fin n) ℂ}
    (hfin : ∀ y, (fibre J A y).Finite) (w : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ)
    (y : Fin k → ℂ) : |chartDens J A w φ y| ≤ chartAbsDens J A w φ y := by
  simp only [chartDens, chartAbsDens, sheetSum]
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.VarIntAdd
