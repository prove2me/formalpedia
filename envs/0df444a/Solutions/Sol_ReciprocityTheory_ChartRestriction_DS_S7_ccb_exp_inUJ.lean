-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.ccb_exp_inUJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:21:35.123588+00:00
-- url     : https://prove2.me/submissions/9d93f568-658d-45b6-bf5f-dcc966cbd5fc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ccb_exp_neg_mul

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
theorem _root_.solution (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv hJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJ, hJ⟩, rfl⟩
  have hXh : Xᴴ = -(Jm ε * X * Jm ε) := by
    have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left (show Xᴴ * Jm ε + Jm ε * X = 0 from hX)
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = -(Jm ε * X * Jm ε) := by rw [h1, Matrix.neg_mul]
  have hs : star ((t : ℂ)) = (t : ℂ) := Complex.conj_ofReal t
  have e2 : (t : ℂ) • -(Jm ε * X * Jm ε) = Jm ε * (-((t : ℂ) • X)) * (Jm ε)⁻¹ := by
    rw [hJinv]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hs, hXh, e2, Matrix.exp_conj _ _ hJu, hJinv]
  calc Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε * Jm ε * NormedSpace.exp ((t : ℂ) • X)
      = Jm ε * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
        rw [Matrix.mul_assoc (Jm ε * _) (Jm ε) (Jm ε), hJ, Matrix.mul_one, Matrix.mul_assoc]
    _ = Jm ε := by rw [ccb_exp_neg_mul, Matrix.mul_one]
end ReciprocityTheory.ChartRestriction.DS.S7
