-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_smoothGenericFibreM_yLine_0ebdec44e278
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:24.950283+00:00
-- url     : https://prove2.me/submissions/b38fb2b8-96ca-44db-99a7-f7290ce64045

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_gen_ne_zero_c3a5b642e033
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_transcendental_gen_d9ebbc5ee0fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_transcendental_gen_inv_3c156d1276af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_yLine_zero_ca6e34684267
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_yLine_one_da595b259ab5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_smooth_adjoin_of_transcendental_1b0cb7f0067d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution : SmoothGenericFibreM yLine := by
  intro c _
  obtain ⟨a, ha⟩ : ∃ a, c () = a := ⟨_, rfl⟩
  fin_cases a
  · refine smooth_adjoin_of_transcendental transcendental_gen _ (le_antisymm ?_ ?_)
    · rw [Algebra.adjoin_le_iff]
      rintro _ ⟨⟨⟨⟩, i⟩, rfl⟩
      simp only [Fin.zero_eta, Fin.isValue] at ha
      simp only [ha]
      fin_cases i
      · simp [yLine_zero]
      · simp only [Fin.mk_one, yLine_one, yLine_zero, div_one]
        exact Algebra.subset_adjoin rfl
    · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      refine Algebra.subset_adjoin ⟨⟨(), 1⟩, ?_⟩
      simp only [Fin.zero_eta, Fin.isValue] at ha
      simp [ha, yLine_one, yLine_zero]
  · refine smooth_adjoin_of_transcendental transcendental_gen_inv _ (le_antisymm ?_ ?_)
    · rw [Algebra.adjoin_le_iff]
      rintro _ ⟨⟨⟨⟩, i⟩, rfl⟩
      simp only [Fin.mk_one, Fin.isValue] at ha
      simp only [ha]
      fin_cases i
      · simp only [Fin.zero_eta, yLine_one, yLine_zero, one_div]
        exact Algebra.subset_adjoin rfl
      · simp [yLine_one, div_self gen_ne_zero]
    · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      refine Algebra.subset_adjoin ⟨⟨(), 0⟩, ?_⟩
      simp only [Fin.mk_one, Fin.isValue] at ha
      simp [ha, yLine_one, yLine_zero]
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
