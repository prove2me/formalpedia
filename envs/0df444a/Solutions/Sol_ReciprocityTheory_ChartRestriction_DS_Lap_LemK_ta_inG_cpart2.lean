-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.ta_inG_cpart2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:16.607452+00:00
-- url     : https://prove2.me/submissions/cf38e979-3c0b-42b8-a7bd-8e5f135de5fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_ta_Jm_Jm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
section CurveL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end CurveL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
private lemma jm_sq_lemma (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
private lemma Jm_conjTranspose_eq_selfKType (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1
  funext a
  split_ifs <;> simp [*]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart2 ε Z) := by
  unfold inG cpart2
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose_eq_selfKType,
    conjTranspose_conjTranspose]
  simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, mul_assoc, jm_sq_lemma, ta_Jm_Jm, mul_one]
  have h2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I]
    rw [map_ofNat]
    rw [mul_neg, div_neg]
  rw [h2]
  module
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
