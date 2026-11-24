-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormCycleAdd_proof_cb4af45dc0ff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:26.460959+00:00
-- url     : https://prove2.me/submissions/752d6530-2863-4288-a829-eefe7e4d0781

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormCycleAdd

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace ChowFormCycleAdd
theorem _root_.solution (h1 : ChowFormAssoc.Statement) : ChowFormCycleAdd.Statement := by
  classical
  intro F _ n k Z₁ Z₂ f₁ f₂ ⟨c₁, hc₁, g₁, hg₁, hf₁⟩ ⟨c₂, hc₂, g₂, hg₂, hf₂⟩
  subst hf₁ hf₂
  let g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F :=
    fun W => if W ∈ Z₁.support then g₁ W else g₂ W
  have hd : ∀ W, ∃ d : F, d ≠ 0 ∧ (W ∈ Z₂.support → g₂ W = C d * g W) := by
    intro W
    by_cases hW1 : W ∈ Z₁.support
    · by_cases hW2 : W ∈ Z₂.support
      · obtain ⟨d, hd, he⟩ := h1 F n k W (g₁ W) (g₂ W) (hg₁ W hW1) (hg₂ W hW2)
        exact ⟨d, hd, fun _ => by simp only [g, if_pos hW1, he]⟩
      · exact ⟨1, one_ne_zero, fun h => absurd h hW2⟩
    · exact ⟨1, one_ne_zero, fun _ => by simp only [g, if_neg hW1, map_one, one_mul]⟩
  choose d hd0 hdg using hd
  have hsupp : (Z₁ + Z₂).support = Z₁.support ∪ Z₂.support := by
    ext W
    simp only [Finsupp.mem_support_iff, Finset.mem_union, Finsupp.coe_add, Pi.add_apply, ne_eq,
      Nat.add_eq_zero_iff, not_and_or]
  refine ⟨c₁ * c₂ * ∏ W ∈ Z₂.support, d W ^ Z₂ W, ?_, g, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero hc₁ hc₂)
      (Finset.prod_ne_zero_iff.mpr fun W _ => pow_ne_zero _ (hd0 W))
  · intro W hW
    rw [hsupp, Finset.mem_union] at hW
    by_cases hW1 : W ∈ Z₁.support
    · simpa only [g, if_pos hW1] using hg₁ W hW1
    · simpa only [g, if_neg hW1] using hg₂ W (hW.resolve_left hW1)
  · have e1 : ∏ W ∈ Z₁.support, g₁ W ^ Z₁ W =
        ∏ W ∈ Z₁.support ∪ Z₂.support, g W ^ Z₁ W := by
      rw [← Finset.prod_subset Finset.subset_union_left (f := fun W => g W ^ Z₁ W)]
      · exact Finset.prod_congr rfl fun W hW => by simp only [g, if_pos hW]
      · intro W _ hW
        rw [Finsupp.mem_support_iff, not_not] at hW
        simp [hW]
    have e2 : ∏ W ∈ Z₂.support, g₂ W ^ Z₂ W =
        C (∏ W ∈ Z₂.support, d W ^ Z₂ W) * ∏ W ∈ Z₁.support ∪ Z₂.support, g W ^ Z₂ W := by
      rw [← Finset.prod_subset Finset.subset_union_right (f := fun W => g W ^ Z₂ W)]
      · rw [map_prod, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun W hW => by rw [hdg W hW, mul_pow, map_pow]
      · intro W _ hW
        rw [Finsupp.mem_support_iff, not_not] at hW
        simp [hW]
    rw [hsupp, e1, e2]
    simp only [Finsupp.coe_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib, map_mul]
    ring
end ChowFormCycleAdd
end GroundTheory.Heights₂.Heights
