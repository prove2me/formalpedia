-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.ccb_inG_cpart1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:41.982805+00:00
-- url     : https://prove2.me/submissions/b3d5b6c1-631e-4f2a-8ede-374c7e893f22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ccb_JJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart1 ε Z) := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hJH : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a = true <;> simp [h]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  unfold inG cpart1
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJH,
    Matrix.conjTranspose_conjTranspose, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc, hJ, ccb_JJ, Matrix.mul_one, smul_add, smul_sub, smul_neg,
    neg_one_smul, Matrix.neg_mul, Matrix.mul_neg]
  abel
end ReciprocityTheory.ChartRestriction.DS.S7
