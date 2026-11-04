-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixInitial.actual_initializer_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T19:04:37.890324+00:00
-- url     : https://prove2.me/submissions/0f665456-e2cf-4872-b8e0-de8e7c2d2bfb

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitialBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixInitial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixInitial_initial_bound
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_TernaryPairedInitial_initial_bound
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixInitial
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
namespace ThreeSum.WeightedGlobalArenaPrefixInitial
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
end ThreeSum.WeightedGlobalArenaPrefixInitial
