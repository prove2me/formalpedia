-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockTrdeg_exists_nat_mul_mem_range_finset_287ad278de3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:48:11.161158+00:00
-- url     : https://prove2.me/submissions/b02a2e6c-488d-49f5-a781-f09db80c731a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PBlockTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_exists_nat_mul_mem_range_0c268acf36e9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Algebra Cardinal
open GroundTheory.Heights₂.Heights.BlockTrdeg
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open scoped Classical
variable {σ : Type} {L : Type} [Field L] [Algebra ℚ L]
namespace GroundTheory.Heights₂.Heights.BlockTrdeg
theorem _root_.solution (ψ : MvPolynomial σ ℤ →+* L) (s : Finset L)
    (hs : ∀ y ∈ s, y ∈ adjoin ℚ (Set.range fun p ↦ ψ (X p))) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ y ∈ s, (n : L) * y ∈ ψ.range := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨n, hn, hns⟩ := ih fun y hy ↦ hs y (Finset.mem_insert_of_mem hy)
    obtain ⟨m, hm, hma⟩ := exists_nat_mul_mem_range ψ (hs a (Finset.mem_insert_self a s))
    refine ⟨n * m, mul_ne_zero hn hm, fun y hy ↦ ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · rw [Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ _) hma
    · rw [Nat.cast_mul, mul_comm (n : L), mul_assoc]
      exact mul_mem (natCast_mem _ _) (hns y hy)
end GroundTheory.Heights₂.Heights.BlockTrdeg
