-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.ccb_inG_cpart2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:47.767643+00:00
-- url     : https://prove2.me/submissions/a7fcb6e8-7aba-423c-9a1e-9e72b1479c7c

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
theorem _root_.solution (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart2 ε Z) := by
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
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    first
    | (simp [Complex.conj_I]; ring)
    | (rw [star_div', star_one, star_mul', Complex.star_def, Complex.conj_I]; field_simp; ring)
    | (apply Complex.ext <;> simp [Complex.div_re, Complex.div_im])
  unfold inG cpart2
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJH,
    Matrix.conjTranspose_conjTranspose, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_assoc, hJ, ccb_JJ, Matrix.mul_one, neg_smul, smul_add, smul_neg,
    neg_one_smul, Matrix.neg_mul, Matrix.mul_neg, neg_add]
  abel
end ReciprocityTheory.ChartRestriction.DS.S7
