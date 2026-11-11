-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.master_selected_scan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:59:56.197928+00:00
-- url     : https://prove2.me/submissions/80062540-e755-482c-ac60-57765449fc4c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventToMaster_scan_priority
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_masterBad_original
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_select_map_of_enabled


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : Vertex P → Space) :
    (select (localEvent (eventSupport P J r) (eventBad P J r lambda K)) u).map
        (eventToMaster P J r) =
      select (localEvent (masterSupport P) (masterBad P r lambda K J)) u := by
  apply select_map_of_enabled
  · exact eventToMaster_scan_priority P J r
  · intro e u
    exact masterBad_original P J r lambda K e _
  · intro e u hu
    have he : Eligible P J r e.val := hu.1
    exact ⟨⟨e.val,he⟩,Subtype.ext rfl⟩
end QEC.Coding.BDL26RandomPerturbation
