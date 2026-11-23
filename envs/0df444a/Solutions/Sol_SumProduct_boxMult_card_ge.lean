-- Prove2me | solution 1 for SumProduct.boxMult_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:34:06.761082+00:00
-- url     : https://prove2.me/submissions/adf50fb1-ba69-4531-86b6-bf61d59a64a1

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_Blichfeldt
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_CubeSectionHensley
import Definitions.Def_SumProduct_MultiplicativeCount
import Theorems.Thm_SumProduct_unitLattice_inter_unitBox_finite
import Theorems.Thm_SumProduct_unitLattice_multiplicity_le
import Theorems.Thm_SumProduct_unitLattice_inter_unitBox_ncard_le
import Theorems.Thm_SumProduct_hensley_unitBox_volume
import Theorems.Thm_SumProduct_volume_le_of_tsum_indicator_le


set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem Metric
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) (Y : ℝ) (hY : 1 ≤ Y) :
    Y ^ (d - 1) / (Real.sqrt d * NumberField.Units.regulator K) ≤ (boxMult K Y).card := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hRpos : 0 < regulator K := regulator_pos K
  have hdpos : 0 < Real.sqrt (d : ℝ) := by
    rw [Real.sqrt_pos]
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    rw [hd] at this; exact_mod_cast this
  set b := (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K) with hb
  set F := ZSpan.fundamentalDomain b with hF
  have hfund : IsAddFundamentalDomain (unitLattice K) F volume := by
    have h := ZSpan.isAddFundamentalDomain b volume
    rwa [(basisUnitLattice K).ofZLatticeBasis_span ℝ] at h
  haveI : MeasurableVAdd (unitLattice K) (logSpace K) :=
    inferInstanceAs (MeasurableVAdd (unitLattice K).toAddSubgroup _)
  haveI : VAddInvariantMeasure (unitLattice K) (logSpace K) volume :=
    inferInstanceAs (VAddInvariantMeasure (unitLattice K).toAddSubgroup _ _)
  have hSmeas : MeasurableSet (unitBox K (Y / 2)) := by
    rw [unitBox, Set.setOf_and]
    refine (IsClosed.inter ?_ ?_).measurableSet
    · rw [Set.setOf_forall]
      exact isClosed_iInter fun w =>
        isClosed_le (continuous_abs.comp (continuous_apply w)) continuous_const
    · exact isClosed_le
        (continuous_abs.comp (continuous_finsetSum _ fun w _ => continuous_apply w))
        continuous_const
  have hfin := unitLattice_inter_unitBox_finite (K := K) (Y := Y) hY0
  set N := (↑(unitLattice K) ∩ unitBox K Y).ncard with hNdef
  have hbli : volume (unitBox K (Y / 2)) ≤ (N : ENNReal) * volume F := by
    refine volume_le_of_tsum_indicator_le hfund hSmeas (fun y => ?_)
    refine (unitLattice_multiplicity_le y).trans ?_
    rw [hNdef, ← Set.Finite.cast_ncard_eq hfin]
    exact_mod_cast le_refl _
  have hcov : ZLattice.covolume (unitLattice K) volume = regulator K := rfl
  have hFreal : (volume F).toReal = regulator K := by
    rw [← hcov, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hfund, Measure.real]
  have hFne : volume F ≠ ⊤ := by
    intro htop; rw [htop, ENNReal.toReal_top] at hFreal; exact (ne_of_gt hRpos) hFreal.symm
  have hsub : unitBox K (Y / 2) ⊆ closedBall 0 (Y / 2) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by linarith)]
    intro w; rw [Real.norm_eq_abs]; exact hx.1 w
  have hSne : volume (unitBox K (Y / 2)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hsub) (isCompact_closedBall 0 (Y / 2)).measure_lt_top)
  have hprodne : (N : ENNReal) * volume F ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFne
  have hreal := (ENNReal.toReal_le_toReal hSne hprodne).mpr hbli
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hFreal] at hreal
  obtain ⟨hlo, -⟩ := hensley_unitBox_volume K (Y / 2) (by linarith)
  rw [hd, show (2 : ℝ) * (Y / 2) = Y by ring] at hlo
  have hNR : Y ^ (d - 1) / Real.sqrt d ≤ (N : ℝ) * regulator K := le_trans hlo hreal
  have key : Y ^ (d - 1) ≤ (N : ℝ) * regulator K * Real.sqrt d := (div_le_iff₀ hdpos).mp hNR
  have hNle : (N : ℝ) ≤ (boxMult K Y).card := by
    exact_mod_cast unitLattice_inter_unitBox_ncard_le (K := K) (Y := Y)
  calc Y ^ (d - 1) / (Real.sqrt d * regulator K)
      ≤ (N : ℝ) := by
        rw [div_le_iff₀ (by positivity),
          show (N : ℝ) * (Real.sqrt (d : ℝ) * regulator K) = N * regulator K * Real.sqrt d by ring]
        exact key
    _ ≤ (boxMult K Y).card := hNle
end SumProduct
