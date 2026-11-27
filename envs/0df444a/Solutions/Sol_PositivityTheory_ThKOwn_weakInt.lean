-- Prove2me | solution 1 for PositivityTheory.ThKOwn.weakInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:22:35.592967+00:00
-- url     : https://prove2.me/submissions/091cbced-45db-408b-965f-4bbfd91cdec1

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_JetApply
import Theorems.Thm_PositivityTheory_ThKOwn_SchI_int_J
import Theorems.Thm_PositivityTheory_ThKOwn_SchI_exists_int
import Theorems.Thm_PositivityTheory_ThKOwn_SchI_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKOwn
open MeasureTheory
namespace PositivityTheory.ThKOwn
theorem _root_.solution :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (α : Type) [TopologicalSpace α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] (μ : Measure α) (G : α → SchwartzMap V ℂ), Continuous G →
    (∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ) →
    ∃ f : SchwartzMap V ℂ, ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, Integrable (fun a => T (G a)) μ ∧ T f = ∫ a, T (G a) ∂μ := by
  intro V _ _ _ α _ _ _ _ μ G hG hI
  obtain ⟨f, hf⟩ := SchI.exists_int hG hI
  refine ⟨f, fun T => ?_⟩
  obtain ⟨s, T', hT'⟩ := SchI.factor T
  have hsplit : ∀ g : SchwartzMap V ℂ, T g = ∑ i : s, T' (Pi.single i (SchI.J i.1.1 i.1.2 g)) := by
    intro g
    rw [hT', ← map_sum, Finset.univ_sum_single]
  have hint : ∀ i : s, Integrable (fun a => T' (Pi.single i (SchI.J i.1.1 i.1.2 (G a)))) μ := fun i =>
    (T'.comp (ContinuousLinearMap.single ℂ _ i)).integrable_comp
      (SchI.int_J hG hI _ _)
  have hTG : (fun a => T (G a)) = fun a => ∑ i : s, T' (Pi.single i (SchI.J i.1.1 i.1.2 (G a))) :=
    funext fun a => hsplit (G a)
  refine ⟨by rw [hTG]; exact integrable_finsetSum _ fun i _ => hint i, ?_⟩
  rw [hTG, integral_finsetSum _ fun i _ => hint i, hsplit f]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf]
  exact ((T'.comp (ContinuousLinearMap.single ℂ _ i)).integral_comp_comm
    (SchI.int_J hG hI _ _)).symm
end PositivityTheory.ThKOwn
