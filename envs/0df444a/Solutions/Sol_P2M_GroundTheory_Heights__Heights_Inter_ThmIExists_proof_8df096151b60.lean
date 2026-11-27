-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_proof_8df096151b60
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:01:24.437222+00:00
-- url     : https://prove2.me/submissions/61ab8ea3-bb75-4e82-a635-f00f869fdcd4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isRFamily_famI_4b4e744fcce2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ThmIExists
namespace GroundTheory.Heights₂.Heights.Inter
namespace ThmIExists
theorem _root_.solution (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement) (hWD : WellDefined.Statement)
    (hSymm : ThmISymm.Statement) : ThmIExists.Statement := by
  refine ⟨fun K _ ι _ => famI (K := K) (ι := ι), fun K _ ι _ => ?_⟩
  have hRF : IsRFamily (famI (K := K) (ι := ι)) :=
    isRFamily_famI hD1 hMul fun n hR hA P L B s t hP hL hB hs ht =>
      hWD K ι famI P n L B s t hR hA hP hL hB hs ht
  exact ⟨hSymm K ι _ hRF, hRF.1, hRF.2⟩
end ThmIExists
end GroundTheory.Heights₂.Heights.Inter
