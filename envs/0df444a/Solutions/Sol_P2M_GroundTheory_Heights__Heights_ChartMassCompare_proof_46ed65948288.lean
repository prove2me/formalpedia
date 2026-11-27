-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMassCompare_proof_46ed65948288
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:53:20.674155+00:00
-- url     : https://prove2.me/submissions/a3159eb1-19eb-4b36-9c66-ec4a27eba069

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetComass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetAreaCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sheetJac_nonneg_cd90e2bb5cf3


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
open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ChartMassCompare
theorem _root_.solution (h1 : SheetComass.Statement) (h2 : SheetAreaCompare.Statement) :
    ChartMassCompare.Statement := by
  intro n d J A φ R hJ hdim hA hφ
  obtain ⟨C, hC⟩ := h1 n d J A φ R hφ
  obtain ⟨c, hc, hca⟩ := h2 n d J A
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set B := Metric.closedBall (0 : Fin n → ℂ) R
  refine ⟨ENNReal.ofReal C' * c, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc, fun g hg => ?_⟩
  set gB := B.indicator g with hgBdef
  have hgB : Measurable gB := hg.indicator measurableSet_closedBall

  have hpt : ∀ y, chartAbsDens J A gB φ y ≤
      C' * sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y := by
    intro y
    have hfin := (ComplexSets.FibreBound.proof n d J A hJ hdim hA y).2.1
    unfold chartAbsDens sheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    have hxf : x ∈ fibre J A y := hfin.mem_toFinset.mp hx
    split_ifs with hs
    · dsimp only
      rw [← hxf.2]
      by_cases hxB : x ∈ B
      · have hb := hC x ⟨hxf.1, hxB⟩ _ hs.choose_spec
        rw [abs_mul]
        calc |gB x| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ hs.choose) (A *ᵥ x)|
            ≤ |gB x| * (C' * sheetJac hs.choose (A *ᵥ x)) :=
              mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
                (sheetJac_nonneg _ _))) (abs_nonneg _)
          _ = C' * (|gB x| * sheetJac hs.choose (A *ᵥ x)) := by ring
      · simp [gB, hxB]
    · simp
  have hnn : ∀ y, 0 ≤ chartAbsDens J A gB φ y := fun y =>
    finsum_nonneg fun x => finsum_nonneg fun _ => by split_ifs; exacts [abs_nonneg _, le_rfl]
  calc ∫⁻ y, ‖chartAbsDens J A gB φ y‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal C' * ‖sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y‖ₑ := by
        refine lintegral_mono fun y => ?_
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn y),
          ← ENNReal.ofReal_mul hC'0]
        exact ENNReal.ofReal_le_ofReal ((hpt y).trans
          (mul_le_mul_of_nonneg_left (le_abs_self _) hC'0))
    _ = ENNReal.ofReal C' * ∫⁻ y, ‖sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C' * (c * ∫⁻ z in zeroSetEuc J, ‖gB (WithLp.ofLp z)‖ₑ
          ∂(μH[((2 * d : ℕ) : ℝ)])) := by gcongr; exact hca gB hgB
    _ = ENNReal.ofReal C' * c * ∫⁻ z in zeroSetEuc J ∩ {z | WithLp.ofLp z ∈ B},
          ‖g (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        have hT : MeasurableSet {z : EuclideanSpace ℂ (Fin n) | WithLp.ofLp z ∈ B} :=
          measurableSet_closedBall.preimage (PiLp.continuous_ofLp 2 _).measurable
        have hfun : (fun z : EuclideanSpace ℂ (Fin n) => ‖gB (WithLp.ofLp z)‖ₑ) =
            {z : EuclideanSpace ℂ (Fin n) | WithLp.ofLp z ∈ B}.indicator
              (fun z => ‖g (WithLp.ofLp z)‖ₑ) := by
          ext z
          by_cases hz : WithLp.ofLp z ∈ B <;> simp [gB, hz, Set.indicator]
        rw [hfun, lintegral_indicator hT, Measure.restrict_restrict hT, Set.inter_comm, mul_assoc]
end ChartMassCompare
end GroundTheory.Heights₂.Heights
