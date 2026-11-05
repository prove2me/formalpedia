-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget.field_sizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:06:36.537895+00:00
-- url     : https://prove2.me/submissions/26d856f5-8683-4168-9159-c8b9f4a9cfb6

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_menu_field_lower
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryExtensionEncoding
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget
theorem _root_.solution (J K : ℕ) (hK : 0<K)
    (hcard : Fintype.card E=p^(menuDegree p (J+2) K)) :
    8*(J+2)*p^2≤Fintype.card E ∧ 8*(J+2)*p^(2*(K+K))≤Fintype.card E := by
  have hlow := menu_field_lower (p := p) (J+2) K
  have hpow : p^2≤p^(4*K) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  have hΛ : 8*(J+2)*p^(4*K)≤8*((J+2)+1)*p^(4*K) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 (Nat.le_succ (J+2)))
  rw [hcard]
  constructor
  · calc
      _≤8*(J+2)*p^(4*K) := Nat.mul_le_mul_left _ hpow
      _≤8*((J+2)+1)*p^(4*K) := hΛ
      _≤_ := hlow
  · have he : 2*(K+K)=4*K := by omega
    rw [he]
    exact hΛ.trans hlow
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget
