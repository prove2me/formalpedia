-- Prove2me | solution 1 for QEC.Coding.BDL26SeedCohomology.equivalence_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:33:21.151813+00:00
-- url     : https://prove2.me/submissions/f746ccab-a8fc-4f49-8a07-592936dc55f9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26SeedCohomology
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance
namespace QEC.Coding.BDL26SeedCohomology
theorem _root_.solution (c : Field) :
    equivalence.symm c = classOf (c • seedElement) := rfl
end QEC.Coding.BDL26SeedCohomology
