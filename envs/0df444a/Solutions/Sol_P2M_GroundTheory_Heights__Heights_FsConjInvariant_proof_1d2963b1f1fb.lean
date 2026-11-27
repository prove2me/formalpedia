-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FsConjInvariant_proof_1d2963b1f1fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:55:06.016774+00:00
-- url     : https://prove2.me/submissions/a53c5334-c458-46db-a425-b268c7bc515f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PFsConjInvariant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyConjugationInvariant_fsMetric_conj_c938287a366d

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
open ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights
namespace FsConjInvariant
theorem _root_.solution : FsConjInvariant.Statement := by
  intro K _ ι _ z
  simp only [fsMulti, HermLine.ofMetrics]
  exact Finset.prod_congr rfl fun k _ => by
    rw [FubiniStudyConjugationInvariant.fsMetric_conj (fun i => z ⟨k, i⟩)]
end FsConjInvariant
end GroundTheory.Heights₂.Heights
