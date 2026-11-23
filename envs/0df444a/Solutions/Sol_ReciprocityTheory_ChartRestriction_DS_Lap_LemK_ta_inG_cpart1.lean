-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.ta_inG_cpart1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:16.710544+00:00
-- url     : https://prove2.me/submissions/537e8673-579f-4eb3-a9c5-5090a5e3f3b9

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
theorem _root_.solution (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart1 ε Z) := by
  unfold inG cpart1
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose_eq_selfKType,
    conjTranspose_conjTranspose]
  simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, mul_assoc, jm_sq_lemma, ta_Jm_Jm, mul_one]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2]
  module
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
