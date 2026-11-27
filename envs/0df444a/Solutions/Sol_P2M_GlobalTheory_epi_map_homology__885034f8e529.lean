-- Prove2me | solution 1 for P2M_GlobalTheory_epi_map_homology__885034f8e529
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:53:03.291124+00:00
-- url     : https://prove2.me/submissions/be3d2798-0887-4968-8084-6a8a1c77898e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
open GlobalTheory
open CategoryTheory Category Limits
set_option backward.isDefEq.respectTransparency false
variable {C D : Type*} [Category* C] [Category* D]
variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
variable [PreservesColimitsOfShape WalkingParallelPair F]
namespace GlobalTheory
theorem _root_.solution (S : ShortComplex C) [S.HasHomology] : Epi (F.map S.homologyπ) :=
  epi_of_isColimit_cofork (CokernelCofork.mapIsColimit _ S.homologyIsCokernel F)
end GlobalTheory
