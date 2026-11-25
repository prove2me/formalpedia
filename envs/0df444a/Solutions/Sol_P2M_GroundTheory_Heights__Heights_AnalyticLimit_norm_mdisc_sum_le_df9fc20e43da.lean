-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_norm_mdisc_sum_le_df9fc20e43da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:28.215163+00:00
-- url     : https://prove2.me/submissions/c804d4bb-94f4-4075-b2c3-361b02e64fe1

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_EnergySum
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_multilinearMap_eq_mdisc
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_nonneg_of_posSemidef
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open MeasureTheory
open scoped ContDiff ComplexOrder
open ReciprocityTheory.AnForm (hessC maDens mdisc levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens integralWith)
noncomputable section
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {m : ℕ} (a : Fin D → Fin m → ℝ)
    (B : Fin D → Fin m → Matrix (Fin D) (Fin D) ℂ) (hB : ∀ k i, (B k i).PosSemidef) :
    ‖mdisc (fun k => ∑ i, (a k i : ℂ) • B k i)‖ ≤
      ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * (mdisc fun k => B k (σ k)).re := by
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  rw [← hM, MultilinearMap.map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  rw [MultilinearMap.map_smul_univ, norm_smul, hM, norm_prod]
  obtain ⟨him, hre⟩ := ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef _ fun k => hB k (σ k)
  have hz : mdisc (fun k => B k (σ k)) = ((mdisc fun k => B k (σ k)).re : ℂ) :=
    Complex.ext (by simp) (by simp [him])
  rw [hz, Complex.norm_of_nonneg hre]
  simp [Complex.norm_real]
end GroundTheory.Heights₂.Heights.AnalyticLimit
