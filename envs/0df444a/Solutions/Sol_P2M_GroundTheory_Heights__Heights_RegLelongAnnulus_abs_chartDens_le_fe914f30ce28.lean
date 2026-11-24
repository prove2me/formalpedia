-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_chartDens_le_fe914f30ce28
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:17.273425+00:00
-- url     : https://prove2.me/submissions/57c64715-730c-4e6d-a18c-aea9e6235f3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_fibre_finite_7d46f66826ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_finite_20785c71949c


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
variable {n m : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin m) (Fin n) ℂ}
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution (hA : IsFiniteProjection J A) {w f : (Fin n → ℂ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ z, |w z| ≤ C * f z) (φ : Fin m → (Fin n → ℂ) → ℝ) (y : Fin m → ℂ) :
    |chartDens J A w φ y| ≤ C * chartAbsDens J A f φ y := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
  split_ifs with h
  · beta_reduce
    rw [abs_mul, abs_mul]
    calc |w z| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y|
        ≤ (C * |f z|) * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y| :=
          mul_le_mul_of_nonneg_right ((hw z).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC))
            (abs_nonneg _)
      _ = C * (|f z| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y|) := by ring
  · simp
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
