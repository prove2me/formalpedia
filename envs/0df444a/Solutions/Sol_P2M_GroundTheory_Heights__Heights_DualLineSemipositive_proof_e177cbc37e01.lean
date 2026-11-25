-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualLineSemipositive_proof_e177cbc37e01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:46.856929+00:00
-- url     : https://prove2.me/submissions/58109d27-3654-4348-b773-3d533436b394

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineSemipositive
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_dualLine_h_eq_61af8b077351
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isSmoothMetric_fs_21e0570fe462
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_leviForm_log_fs_nonneg_4c974b17d733
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__id_ce5e717798ac
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField
open scoped ComplexOrder
noncomputable section
open DualLineSemipositiveAlt
namespace GroundTheory.Heights₂.Heights
namespace DualLineSemipositive
theorem _root_.solution : DualLineSemipositive.Statement := by
  intro K _ _ i F T _ _ b hb
  set τc : ((Σ _ : Unit, T) → ℂ) →L[ℂ] ((K →+* ℂ) × Fin i → ℂ) :=
    LinearMap.toContinuousLinearMap (coordMap b hb) with hτc
  have hh : ∀ z, (dualLine F b hb).h z = (fsMetric ((K →+* ℂ) × Fin i)).ρ (τc z) :=
    dualLine_h_eq b hb
  have hne : ∀ z : (Σ _ : Unit, T) → ℂ, (∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) → τc z ≠ 0 := by
    intro z hz h0
    have hp := (dualLine F b hb).pos z hz
    rw [hh, h0] at hp
    simp [fsMetric] at hp
  have hfun : (dualLine F b hb).h = (fsMetric ((K →+* ℂ) × Fin i)).ρ ∘ τc := funext hh
  refine ⟨?_, fun z hz w _ => ?_⟩
  · intro z hz
    rw [hfun]
    exact ((HilbertSamuel.ProjLine.isSmoothMetric_fs.contDiffAt (isOpen_ne.mem_nhds (hne z hz))).comp z
      (τc.restrictScalars ℝ).contDiff.contDiffAt).contDiffWithinAt
  · change 0 ≤ ReciprocityTheory.AnForm.levi (fun z => Real.log ((dualLine F b hb).h z)) z w
    have hlog : (fun z => Real.log ((dualLine F b hb).h z)) =
        (fun u => Real.log ((fsMetric ((K →+* ℂ) × Fin i)).ρ u)) ∘ τc := by
      funext y
      simp only [Function.comp_apply, hh]
    rw [hlog, ReciprocityTheory.AnForm.levi_comp w (τc.analyticAt z)
      (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id HilbertSamuel.ProjLine.isSmoothMetric_fs
        (hne z hz.1))]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg (hne z hz.1) _
end DualLineSemipositive
end GroundTheory.Heights₂.Heights
