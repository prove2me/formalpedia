-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_mInt_0ce76d64badf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:53:57.207445+00:00
-- url     : https://prove2.me/submissions/f8869bc4-aa09-47a0-a730-e84b3fd24e7e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OneChartAtlasIndexEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_index_eq_95d208c8cfac
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
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
variable {D : ℕ} {Ω : Set (Fin D → ℂ)}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
theorem _root_.solution (hΩ : IsOpen Ω) [Nonempty Ω] (Φ : Fin D → LocPot Ω) (g : Ω → ℝ) :
    mInt (oneChartAtlas hΩ) Φ g =
      ∫ y in Ω, g ((inclChart hΩ).symm y) * locDens (oneChartAtlas hΩ) Φ (j0 hΩ) y := by
  have hne : Nonempty (ChartPartition (oneChartAtlas hΩ)) :=
    ⟨{ χ := fun _ _ => 1
       smooth := fun _ _ => contDiffOn_const
       nonneg := fun _ _ => zero_le_one
       tsupport_subset := fun _ => by
         show _ ⊆ (inclChart hΩ).source
         rw [inclChart_source]; exact Set.subset_univ _
       sum_eq_one := fun _ => by show ∑ _j : Fin 1, (1 : ℝ) = 1; simp }⟩
  rw [mInt, dif_pos hne, integralWith]
  have hχ : ∀ j x, hne.some.χ j x = 1 := by
    intro j x
    have h := hne.some.sum_eq_one x
    rwa [Finset.sum_eq_single j (fun b _ hb => absurd ((oneChartAtlas_index_eq hΩ b).trans (oneChartAtlas_index_eq hΩ j).symm) hb)
      (by simp)] at h
  have hterm : ∀ j : Fin (oneChartAtlas hΩ).n,
      (∫ y in ((oneChartAtlas hΩ).chart j).target,
        hne.some.χ j (((oneChartAtlas hΩ).chart j).symm y) * g (((oneChartAtlas hΩ).chart j).symm y) *
          locDens (oneChartAtlas hΩ) Φ j y) =
      ∫ y in Ω, g ((inclChart hΩ).symm y) * locDens (oneChartAtlas hΩ) Φ (j0 hΩ) y := by
    intro j
    rw [oneChartAtlas_index_eq hΩ j]
    simp only [hχ, one_mul]
    show (∫ y in (inclChart hΩ).target, _) = _
    rw [inclChart_target]
    rfl
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  exact one_smul _ _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
