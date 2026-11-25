-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_joinBlock_sepBlock_1ead804a3c0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:31.986788+00:00
-- url     : https://prove2.me/submissions/8085f51f-5296-4c41-8891-d0fb40fe1446

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock

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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution (k₀ : ι) (q : MvPolynomial (Coord n) ℤ) :
    joinBlock k₀ (sepBlock k₀ q) = q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [sepBlock, joinBlock]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, hp]
    congr 1
    rcases v with ⟨k, i⟩
    by_cases h : k = k₀
    · subst h
      simp [sepBlock, joinBlock, blockIncl]
    · simp [sepBlock, joinBlock, h]
end GroundTheory.Heights₂.Heights.BlockSurjectivity
