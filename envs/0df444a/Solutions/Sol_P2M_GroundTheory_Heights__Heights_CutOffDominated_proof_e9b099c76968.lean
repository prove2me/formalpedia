-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CutOffDominated_proof_e9b099c76968
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:37:42.470739+00:00
-- url     : https://prove2.me/submissions/edfe9a13-bef6-4808-b432-4ae9c836e9a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_chartDens_congr_zeroSet_8fa8af5e5701
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_sheetSum_eq_sum_7191afe3cbd4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_ae_eval_ne_zero_80133a975faf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_isClosed_zeroSet_b1e5ce62660e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1


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
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace CutOffDominated
theorem _root_.solution : CutOffDominated.Statement := by
  classical
  intro n d J A P χ f ψ hJ hdim hA hP hχm hχ01 hlim hf hψ hint
  have hfin : ∀ y, (fibre J A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n d J A hJ hdim hA y).2.1
  set g : (Fin n → ℂ) → ℝ := (zeroSet J).piecewise f 0 with hgdef
  have hg : Measurable g :=
    hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet
  have hmeas : ∀ k, Measurable (chartDens J A (fun x => χ k x * f x) ψ) := fun k => by
    rw [CutOffDominated.chartDens_congr_zeroSet (g := fun x => χ k x * g x)
      (fun x hx => by rw [hgdef, Set.piecewise_eq_of_mem _ _ _ hx])]
    exact (SheetSumMeasurable.proof n d J A _ ψ hJ hdim hA ((hχm k).mul hg) hψ).1
  refine tendsto_integral_of_dominated_convergence (chartAbsDens J A f ψ)
    (fun k => (hmeas k).aestronglyMeasurable) hint (fun k => Eventually.of_forall fun y => ?_) ?_
  · rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens
    rw [CutOffDominated.sheetSum_eq_sum _ (hfin y), CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    split_ifs with h
    · rw [mul_assoc, abs_mul, abs_of_nonneg (hχ01 k x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hχ01 k x).2
    · simp
  · filter_upwards [CutOffDominated.ae_eval_ne_zero P hP] with y hy
    unfold chartDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine tendsto_finsetSum _ fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    have hxl := hlim x hx.1 (by rw [show A *ᵥ x = y from hx.2]; exact hy)
    split_ifs with h
    · simpa using (hxl.mul_const (f x)).mul_const
        (ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ h.choose) y)
    · exact tendsto_const_nhds
end CutOffDominated
end GroundTheory.Heights₂.Heights
