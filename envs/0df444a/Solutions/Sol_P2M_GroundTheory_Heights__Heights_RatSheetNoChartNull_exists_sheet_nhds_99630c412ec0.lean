-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_sheet_nhds_99630c412ec0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:42:22.266925+00:00
-- url     : https://prove2.me/submissions/a55392bc-7ac1-46ef-8e87-da1caa57e774

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetNoChartNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_isOpen_ratPreimage_0d182ed088fb

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
open GroundTheory.Heights₂.Heights.RatSheetNoChartNull
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatSheetNoChartNull
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ DifferentiableOn ℂ s U ∧
      (∀ x' ∈ zeroSet J ∩ W, RatChart.ratMap p q x' ∈ U ∧ RatChart.IsRatSheetAt J p q x' s) ∧
      ((∃ s, RatChart.IsRatSheetAt J p q x s) → x ∈ W) := by
  by_cases hx : ∃ s, RatChart.IsRatSheetAt J p q x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hqx : eval x q ≠ 0 := hsx ▸ (hsec _ hxU).2.1
    refine ⟨s, U, interior V ∩ ({x | eval x q ≠ 0} ∩ RatChart.ratMap p q ⁻¹' U), hU,
      isOpen_interior.inter (isOpen_ratPreimage p q hU), hsd, ?_, fun _ =>
        ⟨mem_interior_iff_mem_nhds.2 hV, hqx, hxU⟩⟩
    rintro x' ⟨hx'Z, hx'V, hx'q, hx'U⟩
    have hx's : s (RatChart.ratMap p q x') = x' := (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'q hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hq'' hR'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hq'' hR''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, differentiableOn_empty,
      by simp, fun h => absurd h hx⟩
end GroundTheory.Heights₂.Heights.RatSheetNoChartNull
