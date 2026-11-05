-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostMemory.Metadata.after_preparation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:23:46.749918+00:00
-- url     : https://prove2.me/submissions/f22910db-be20-4b1d-bbe2-9b80816e20f5

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCleanupLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostMemory
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaCleanupLayout_preparation_bank


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
namespace Metadata
theorem _root_.solution {maps : Fin F→Weight m p} {τ : ℕ} {I : Input}
    {L q : ℕ} {μ ν : ℕ→ℤ} (M : Metadata (r := r) maps τ I μ)
    (hL : L+1≤I.capacity) (hq : q≤I.capacity)
    (hlo : addr I.free I.capacity 9≤I.prefixFree)
    (h : ∀x, LightTernaryFinalPreparation.Unwritten (addr I.free I.capacity 6) L
      (addr I.free I.capacity 7) (addr I.free I.capacity 8) q x→ν x=μ x) :
    Metadata (r := r) maps τ I ν := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [WeightedGlobalArenaCleanupLayout.preparation_bank hL hq h (by omega)]
    exact M.codes i hi
  · intro i hi
    rw [WeightedGlobalArenaCleanupLayout.preparation_bank hL hq h (hlo.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))]
    exact M.powers i hi
  · intro i hi
    rw [WeightedGlobalArenaCleanupLayout.preparation_bank hL hq h
      (show addr I.free I.capacity 9≤addr I.free I.capacity 19+i by unfold addr; omega)]
    exact M.wanted i hi
end Metadata
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostMemory
