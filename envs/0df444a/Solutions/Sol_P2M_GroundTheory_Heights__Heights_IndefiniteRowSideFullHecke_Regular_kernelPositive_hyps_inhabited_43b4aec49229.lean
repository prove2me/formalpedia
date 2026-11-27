-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_kernelPositive_hyps_inhabited_43b4aec49229
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:00:55.3468+00:00
-- url     : https://prove2.me/submissions/eeab3386-de63-4daa-a7e7-a75374a1333b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_diagPeriod_tau0Cov_e3db7c180e1c
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (polyMax Mollifier molli regMax coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart maMeasure)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
theorem _root_.solution :
    ∃ τ₀ : (Fin 1 → ℂ) → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ p q, AnalyticOnNhd ℂ (fun z => τ₀ z p q) (ball 0 1)) ∧
      (∀ w ∈ coverSet 1 1, τ₀ (expCov 1 w) = periodGenusTwo.tau0Cov w) ∧
      ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ ∀ i, periodGenusTwo.Br i *ᵥ v = 0 := by
  refine ⟨fun _ => diagonal (fun _ => Complex.I), fun p q => fun _ _ => analyticAt_const,
    fun w _ => (diagPeriod_tau0Cov 2 ![1, 0] w).symm, ![0, 1], ?_, ?_⟩
  · intro h
    have := congrFun h 1
    simp at this
  · intro i
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst hi0
    ext k
    fin_cases k <;> simp [PeriodPolydisc.Br, periodGenusTwo, diagPeriod, mulVec, dotProduct,
      diagonal_apply]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
