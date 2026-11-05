-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInitial.actual_initializer_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:07:12.967476+00:00
-- url     : https://prove2.me/submissions/b1c1c380-7737-4fce-b7ae-6996a6cd14b8

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitialBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixInitial
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPrefixInitial_initial_bound
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_TernaryPairedInitial_initial_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInitial
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPrefixPairs WeightedGlobalArenaPrefixPotential
open TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInitial
theorem _root_.solution (K b n : ℕ)
    (hL : ∀ i j, (L i j).natAbs≤b) (hR : ∀ i j, (R i j).natAbs≤b)
    (hB : I.nB≤n) (hC : I.nC≤n) :
    value maps τ cap I L R row root Q 0 K≤
      I.requesterCount*n^(2*K)*Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by
  have hh := initial_bound maps τ cap I L R row root Q K b hL hR
  have hc : (I.nB*I.nC)^K≤n^(2*K) := by
    calc
      _ ≤ (n*n)^K := Nat.pow_le_pow_left (Nat.mul_le_mul hB hC) K
      _ = _ := by rw [←pow_two,←pow_mul]
  have he : K+K=2*K := by omega
  rw [he] at hh
  exact hh.trans (by gcongr)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInitial
