-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_map_one__0ae7550c3513
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:47.721035+00:00
-- url     : https://prove2.me/submissions/2758eb8c-c0c7-4acf-94e5-c126bf79062e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsSkewOfDiagonal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
variable {A : Type} [CommRing A] {σ : A →+* A} {β : Type} [Fintype β] [DecidableEq β]
namespace GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
theorem _root_.solution : (1 : Matrix β β A).map σ = 1 := Matrix.map_one _ (map_zero σ) (map_one σ)
end GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
