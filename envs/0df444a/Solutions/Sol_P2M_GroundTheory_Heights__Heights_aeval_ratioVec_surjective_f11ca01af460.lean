-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_aeval_ratioVec_surjective_f11ca01af460
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:40.568968+00:00
-- url     : https://prove2.me/submissions/f4575e65-f834-4f6d-be70-b97c2356fb79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatio
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_val_aeval_ratioVec_1b40d5b88b4d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) :
    Function.Surjective (aeval (ratioVec x c) : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ratioField x) := by
  set S := Set.range fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)
  have hL : ratioField x = IntermediateField.adjoin ℚ S := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
      (IntermediateField.adjoin_le_iff.mpr ?_)
    · rintro _ ⟨⟨k, i, j⟩, rfl⟩
      dsimp only
      rw [← div_div_div_cancel_right₀ (hc k) (x k i) (x k j)]
      exact div_mem (IntermediateField.subset_adjoin ℚ S ⟨⟨k, i⟩, rfl⟩)
        (IntermediateField.subset_adjoin ℚ S ⟨⟨k, j⟩, rfl⟩)
    · rintro _ ⟨p, rfl⟩
      exact div_mem_ratioField x _ _ _
  intro a
  have ha : (a : AlgebraicClosure ℚ) ∈
      (aeval (R := ℚ) fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)).range := by
    have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    rw [aeval_range, ← IntermediateField.adjoin_toSubalgebra, ← hL]
    exact a.2
  obtain ⟨f, hf⟩ := ha
  exact ⟨f, Subtype.ext ((val_aeval_ratioVec x c f).trans hf)⟩
end GroundTheory.Heights₂.Heights
