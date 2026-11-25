-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_exists_sheet_nhds_f03ddba59d7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:36.008049+00:00
-- url     : https://prove2.me/submissions/e6c329dd-a4cf-46cb-bbde-b7ca945903f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetSumMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_continuousOn_ratMap_d6c7d6ac1671

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ComplexSets
open GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ ContinuousOn s U ∧
      (∀ y ∈ U, s y ∈ zeroSet J ∧ eval (s y) q ≠ 0 ∧ RatChart.ratMap p q (s y) = y) ∧
      (∀ x' ∈ zeroSet J ∩ W, RatChart.ratMap p q x' ∈ U ∧ RatChart.IsRatSheetAt J p q x' s) ∧
      ((∃ s, RatChart.IsRatSheetAt J p q x s) → x ∈ W) := by
  by_cases hx : ∃ s, RatChart.IsRatSheetAt J p q x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hQ : IsOpen {z : Fin n → ℂ | eval z q ≠ 0} :=
      isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const
    have hxq : eval x q ≠ 0 := by
      have := (hsec _ hxU).2.1
      rwa [hsx] at this
    refine ⟨s, U, ({z | eval z q ≠ 0} ∩ RatChart.ratMap p q ⁻¹' U) ∩ interior V, hU,
      ((continuousOn_ratMap p q).isOpen_inter_preimage hQ hU).inter isOpen_interior,
      hsd.continuousOn, hsec, ?_, fun _ => ⟨⟨hxq, hxU⟩, mem_interior_iff_mem_nhds.2 hV⟩⟩
    rintro x' ⟨hx'Z, ⟨hx'q, hx'U⟩, hx'V⟩
    have hx's : s (RatChart.ratMap p q x') = x' :=
      (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'q hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hq'' hU'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hq'' hU''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, continuousOn_empty _, by simp,
      by simp, fun h => absurd h hx⟩
end GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
