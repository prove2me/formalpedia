-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.RankA.rank_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:58:07.063475+00:00
-- url     : https://prove2.me/submissions/ab025386-e392-4328-8387-f8bf4e02d2bc

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RankMapLeRank
import Theorems.Thm_ReciprocityTheory_PGsh_Up_RankA_col_mem_range
import Theorems.Thm_ReciprocityTheory_PGsh_Up_RankA_factor_of_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.RankA
variable {S : Type} [CommRing S]
namespace ReciprocityTheory.PGsh.Up.RankA
theorem _root_.solution [StrongRankCondition S] {K : Type} [Field K] (f : S →+* K) {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n S) [Module.Free S (LinearMap.range A.mulVecLin)]
    [Module.Finite S (LinearMap.range A.mulVecLin)] :
    (A.map f).rank ≤ Module.finrank S (LinearMap.range A.mulVecLin) := by
  obtain ⟨N, hN, P, Q, hPQ⟩ : ∃ N, N = Module.finrank S (LinearMap.range A.mulVecLin) ∧
      ∃ (P : Matrix m (Fin N) S) (Q : Matrix (Fin N) n S), A = P * Q :=
    ⟨_, rfl, _, _, factor_of_basis A _ (Module.finBasis S _) (col_mem_range A)⟩
  rw [← hN]
  have h : A.map f = P.map f * Q.map f := by rw [hPQ, Matrix.map_mul]
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
end ReciprocityTheory.PGsh.Up.RankA
