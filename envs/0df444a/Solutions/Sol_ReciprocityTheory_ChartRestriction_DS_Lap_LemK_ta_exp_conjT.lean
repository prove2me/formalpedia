-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.ta_exp_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:34.659091+00:00
-- url     : https://prove2.me/submissions/54c4fa62-8fbc-4673-b5e6-4a55b3e5eb64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferA
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
theorem _root_.solution (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • X))ᴴ = Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε := by
  have hJ : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, jm_sq_lemma ε, jm_sq_lemma ε⟩, rfl⟩
  have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (jm_sq_lemma ε)
  have hXc : Xᴴ = Jm ε * (-X) * Jm ε := by
    have h1 : Xᴴ * Jm ε * Jm ε + Jm ε * X * Jm ε = 0 := by
      rw [← add_mul, hX, zero_mul]
    rw [mul_assoc Xᴴ, jm_sq_lemma, mul_one] at h1
    rw [mul_neg, neg_mul, ← sub_eq_zero, sub_neg_eq_add, h1]
  have hs : (t : ℂ) • (Jm ε * (-X) * Jm ε) = Jm ε * ((t : ℂ) • -X) * (Jm ε)⁻¹ := by
    rw [hJi, mul_smul_comm, smul_mul_assoc]
  rw [← Matrix.exp_conjTranspose, conjTranspose_smul, hXc, Complex.star_def, Complex.conj_ofReal, hs,
    Matrix.exp_conj _ _ hJ, hJi, smul_neg]
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
