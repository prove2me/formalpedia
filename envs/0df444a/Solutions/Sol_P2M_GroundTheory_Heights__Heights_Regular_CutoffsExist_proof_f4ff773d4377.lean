-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_CutoffsExist_proof_f4ff773d4377
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:21.428352+00:00
-- url     : https://prove2.me/submissions/2a5db7a5-fa3d-406e-a3f8-feb588830901

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PCutoffs
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_exists_smooth_bump_of_isCompact_d659e4202a0f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_levi_lower_bound_of_isCompact_bb98515e5025
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_isOpen_inter_preimage
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_chartPush_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_contDiffOn_compat
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_isCompact_symm_image
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_smooth_chartPush


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Set Filter Topology
open scoped ContDiff Manifold
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (chartPush chartPush_eq_zero isCompact_symm_image smooth_chartPush
  contDiffOn_compat)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace CutoffsExist
theorem _root_.solution : CutoffsExist.Statement := by
  intro X _ _ _ D A P
  have hb : ∀ j, ∃ g : (Fin D → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ (∀ y, 0 ≤ g y ∧ g y ≤ 1) ∧
      (∀ y ∈ P.chart j '' closure (P.inner j), g y = 1) ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ P.chartMid j := by
    intro j
    have hcl : closure (P.inner j) ⊆ (P.chart j).source :=
      (P.closure_inner j).trans (P.mid_subset_source j)
    refine exists_smooth_bump_of_isCompact
      (isClosed_closure.isCompact.image_of_continuousOn ((P.chart j).continuousOn.mono hcl))
      ((P.chart j).continuousOn_symm.isOpen_inter_preimage (P.chart j).open_target
        (P.isOpen_mid j)) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(P.chart j).map_source (hcl hx), by
      rw [mem_preimage, (P.chart j).left_inv (hcl hx)]; exact P.closure_inner j hx⟩
  choose g hgs hg01 hg1 hgc hgt using hb
  have hgt' : ∀ j, tsupport (g j) ⊆ (P.chart j).target := fun j => (hgt j).trans inter_subset_left
  have hcp : ∀ j x, 0 ≤ chartPush (P.chart j) (g j) x ∧ chartPush (P.chart j) (g j) x ≤ 1 := by
    intro j x
    unfold chartPush
    by_cases hx : x ∈ (P.chart j).source
    · rw [indicator_of_mem hx]; exact hg01 j _
    · rw [indicator_of_notMem hx]; exact ⟨le_rfl, zero_le_one⟩
  have hsm : ∀ j, A.Smooth (fun x => chartPush (P.chart j) (g j) x - 1) := by
    intro j a
    exact ContDiffOn.sub (f := chartPush (P.chart j) (g j) ∘ (A.chart a).symm)
      (smooth_chartPush (P.compat j) (hgs j) (hgc j) (hgt' j) a) contDiffOn_const
  have hC : ∀ j k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ P.chart k '' closure (P.mid k), ∀ w,
      -C * ‖w‖ ^ 2 ≤ levi ((fun x => chartPush (P.chart j) (g j) x - 1) ∘ (P.chart k).symm) y w := by
    intro j k
    have h := contDiffOn_compat (P.compat k) isOpen_univ (hsm j)
    rw [preimage_univ, inter_univ] at h
    refine levi_lower_bound_of_isCompact (P.chart k).open_target (h.of_le (WithTop.coe_le_coe.2 le_top))
      (isClosed_closure.isCompact.image_of_continuousOn
        ((P.chart k).continuousOn.mono (P.closure_mid k))) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (P.chart k).map_source (P.closure_mid k hx)
  choose C hC0 hC using hC
  refine ⟨fun j x => chartPush (P.chart j) (g j) x - 1, ∑ j, ∑ k, C j k, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j a
    exact (hsm j a).mono (inter_subset_inter_right _ (preimage_mono (subset_univ _)))
  · intro j x _
    constructor <;> linarith [hcp j x]
  · intro j x hx
    have hs : x ∈ (P.chart j).source := P.mid_subset_source j (P.inner_subset_mid j hx)
    have h1 : chartPush (P.chart j) (g j) x = 1 := by
      unfold chartPush
      rw [indicator_of_mem hs]
      exact hg1 j _ ⟨x, subset_closure hx, rfl⟩
    simp [h1]
  · intro j
    refine ⟨(P.chart j).symm '' tsupport (g j), (isCompact_symm_image (hgc j) (hgt' j)).isClosed,
      ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (hgt j hy).2
    · intro x hx
      simp [chartPush_eq_zero (P.chart j) hx.2]
  · intro j k x hx w
    have h := hC j k (P.chart k x) ⟨x, subset_closure hx.2, rfl⟩ w
    have hle : C j k ≤ ∑ j, ∑ k, C j k :=
      (Finset.single_le_sum (fun k _ => hC0 j k) (Finset.mem_univ k)).trans
        (Finset.single_le_sum (f := fun j => ∑ k, C j k)
          (fun j _ => Finset.sum_nonneg fun k _ => hC0 j k) (Finset.mem_univ j))
    have h2 : 0 ≤ ‖w‖ ^ 2 := by positivity
    nlinarith
end CutoffsExist
end GroundTheory.Heights₂.Heights.Regular
