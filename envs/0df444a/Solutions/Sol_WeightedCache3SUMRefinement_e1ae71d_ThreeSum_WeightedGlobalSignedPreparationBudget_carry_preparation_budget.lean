-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPreparationBudget.carry_preparation_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:48:12.256491+00:00
-- url     : https://prove2.me/submissions/de4a2bc4-39a5-40ec-b592-5e2a4d019793

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryApply
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPreparationBudget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedPreparationBudget_polynomial_digit_budget
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedPadding_padded_carry_eventually


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPreparationBudget
open Filter Real Asymptotics WeightedGlobalSignedPadding WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalLocalParameters WeightedGlobalParameters
open scoped Topology
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPreparationBudget
theorem _root_.solution {m b : ℕ} (hm : 0<m) (hb : 1<b)
    {κ δ ε : ℝ} (hκ : 0≤κ) (hδ : carryExponent m b κ<δ) (hε : 0<ε)
    (A : ℝ) (hA : 0≤A) (d : ℕ) (U : ℕ→ℕ)
    (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      A*(n : ℝ)*(2 : ℝ)^paddedLength b (U n) (radixLength m n)*
        ((paddedLength b (U n) (radixLength m n) : ℝ)+1)^d*
        ((Nat.log 2 (3*U n+1) : ℝ)+2)^d≤(n : ℝ)^(1+δ+ε) := by
  filter_upwards [padded_carry_eventually hm hb hκ hδ U hU,
    polynomial_digit_budget hm hb hκ hε A hA d U hU,
    eventually_gt_atTop (1 : ℕ)] with n hc hp hn
  have hnp : (0 : ℝ)<n := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hh := mul_le_mul_of_nonneg_left hc hnp.le
  have hhh := mul_le_mul hp hh (by positivity) (by positivity)
  calc
    _ = (A*((paddedLength b (U n) (radixLength m n) : ℝ)+1)^d*
        ((Nat.log 2 (3*U n+1) : ℝ)+2)^d)*
        ((n : ℝ)*(2 : ℝ)^paddedLength b (U n) (radixLength m n)) := by ring
    _ ≤ (n : ℝ)^ε*((n : ℝ)*(n : ℝ)^δ) := hhh
    _ = (n : ℝ)^ε*((n : ℝ)^(1 : ℝ)*(n : ℝ)^δ) := by rw [Real.rpow_one]
    _ = (n : ℝ)^(ε+(1+δ)) := by rw [← Real.rpow_add hnp,← Real.rpow_add hnp]
    _ = _ := by congr 1; ring
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPreparationBudget
