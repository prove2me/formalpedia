-- Prove2me | solution 1 for QFS.lintegral_compl_ball_rpow_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:29:07.667981+00:00
-- url     : https://prove2.me/submissions/3174e7a4-8e37-4e23-aeff-db31b4c789e9




import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Definitions.Def_QFS_LebesgueDiff
import Definitions.Def_QFS_LebesgueDiff2
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Definitions.Def_QFS_Section32
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

open QFS

variable {d : ℕ}


set_option autoImplicit false

theorem solution (hd : 0 < d) {r γ : ℝ} (hr : 0 < r)
    (hγ : γ < -(d : ℝ)) :
    ∫⁻ u in {u : EuclideanSpace ℝ (Fin d) | r < ‖u‖}, ENNReal.ofReal (‖u‖ ^ γ) < ∞ := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  have hnt : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
    rw [← Module.finrank_pos_iff (R := ℝ), hdim]; exact hd
  have hdcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have h1 : 1 ≤ d := hd
    push_cast [Nat.cast_sub h1]
    ring
  have hexp : ((d - 1 : ℕ) : ℝ) + γ < -1 := by rw [hdcast]; linarith
  -- the radial integrand
  have hrad : IntegrableOn
      (fun y : ℝ => y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1) •
        (Set.Ioi r).indicator (fun y : ℝ => y ^ γ) y) (Set.Ioi 0) volume := by
    rw [hdim]
    have hcongr : ∀ y ∈ Set.Ioi (0 : ℝ),
        y ^ (d - 1) • (Set.Ioi r).indicator (fun y : ℝ => y ^ γ) y
          = (Set.Ioi r).indicator (fun y : ℝ => y ^ (((d - 1 : ℕ) : ℝ) + γ)) y := by
      intro y hy
      by_cases hyr : y ∈ Set.Ioi r
      · rw [Set.indicator_of_mem hyr, Set.indicator_of_mem hyr, smul_eq_mul,
          ← Real.rpow_natCast y (d - 1), ← Real.rpow_add hy]
      · rw [Set.indicator_of_notMem hyr, Set.indicator_of_notMem hyr, smul_zero]
    refine (integrableOn_congr_fun hcongr measurableSet_Ioi).mpr ?_
    rw [integrableOn_indicator_iff measurableSet_Ioi]
    have hinter : Set.Ioi r ∩ Set.Ioi (0 : ℝ) = Set.Ioi r := by
      rw [Set.inter_eq_left]
      exact Set.Ioi_subset_Ioi hr.le
    rw [hinter]
    exact integrableOn_Ioi_rpow_of_lt hexp hr
  have hint : Integrable
      (fun u : EuclideanSpace ℝ (Fin d) => (Set.Ioi r).indicator (fun y : ℝ => y ^ γ) ‖u‖)
      volume :=
    (integrable_fun_norm_addHaar volume
      (f := fun y : ℝ => (Set.Ioi r).indicator (fun y : ℝ => y ^ γ) y)).mpr hrad
  have hfin := hint.hasFiniteIntegral
  have hSm : MeasurableSet {u : EuclideanSpace ℝ (Fin d) | r < ‖u‖} :=
    measurableSet_lt measurable_const measurable_norm
  refine lt_of_le_of_lt ?_ hfin
  calc ∫⁻ u in {u : EuclideanSpace ℝ (Fin d) | r < ‖u‖}, ENNReal.ofReal (‖u‖ ^ γ)
      = ∫⁻ u in {u : EuclideanSpace ℝ (Fin d) | r < ‖u‖},
          ‖(Set.Ioi r).indicator (fun y : ℝ => y ^ γ) ‖u‖‖ₑ := by
        refine setLIntegral_congr_fun hSm fun u hu => ?_
        rw [← ofReal_norm, Set.indicator_of_mem (show ‖u‖ ∈ Set.Ioi r from hu),
          Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg u) γ)]
    _ ≤ ∫⁻ u, ‖(Set.Ioi r).indicator (fun y : ℝ => y ^ γ) ‖u‖‖ₑ :=
        lintegral_mono' Measure.restrict_le_self le_rfl
#print axioms solution
