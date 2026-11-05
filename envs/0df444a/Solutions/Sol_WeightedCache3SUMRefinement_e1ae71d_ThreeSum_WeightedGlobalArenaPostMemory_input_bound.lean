-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostMemory.input_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:24:08.810351+00:00
-- url     : https://prove2.me/submissions/ab187e87-9ae8-4cce-8707-8aae778410af

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCleanupLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostMemory

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostMemory
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 4000000
variable {p m F r J : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostMemory
theorem _root_.solution (v : Fin r→ZMod p) :
    |(coefficientCode v : ℤ)|≤(p*(p+1)^r : ℕ) := by
  rw [abs_of_nonneg (Int.natCast_nonneg _)]
  apply Int.ofNat_le.mpr
  have hp : 1≤p := (Fact.out : p.Prime).one_lt.le
  exact (coefficientCode_lt v).le.trans
    ((Nat.pow_le_pow_left (by omega : p≤p+1) r).trans (Nat.le_mul_of_pos_left _ (by omega)))
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostMemory
