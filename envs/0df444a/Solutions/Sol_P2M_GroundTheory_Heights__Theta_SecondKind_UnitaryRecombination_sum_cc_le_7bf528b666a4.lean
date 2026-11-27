-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_sum_cc_le_7bf528b666a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:13:05.307123+00:00
-- url     : https://prove2.me/submissions/e9d3f207-8eeb-4698-9f3e-3b3d20dc1c91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_card_place_2ef5794d3fc9
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_cc_nonneg_87c80e7e3807

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
variable (F : OrthoFrame)
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution (y : Fin F.dim → ℝ) (τ : Fin F.f) {a : ℝ} (hy : ∀ l, |y l| ≤ a) {k : ℕ}
    (hk : k ≤ F.dim) : ∑ m ∈ Finset.range k, cc F y τ m ≤ (F.r : ℝ) ^ 2 * a := by
  classical
  calc ∑ m ∈ Finset.range k, cc F y τ m ≤ ∑ m ∈ Finset.range F.dim, cc F y τ m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk)
          (fun i _ _ => cc_nonneg F y τ i)
    _ = ∑ l : Fin F.dim, (if F.place l = τ then |y l| else 0) := by
        rw [Finset.sum_range]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp [cc, l.2]
    _ = ∑ l ∈ Finset.univ.filter (fun l => F.place l = τ), |y l| := by
        rw [Finset.sum_filter]
    _ ≤ (Finset.univ.filter (fun l => F.place l = τ)).card • a :=
        Finset.sum_le_card_nsmul _ _ _ fun l _ => hy l
    _ = (F.r : ℝ) ^ 2 * a := by
        rw [nsmul_eq_mul, ← Fintype.card_subtype, card_place]; push_cast; ring
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
