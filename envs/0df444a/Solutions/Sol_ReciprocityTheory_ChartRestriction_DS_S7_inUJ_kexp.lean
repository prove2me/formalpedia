-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.inUJ_kexp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:23.843946+00:00
-- url     : https://prove2.me/submissions/ac667b85-c655-4c09-8135-12597ed044ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_isHermitian_of_mem_noncompactPart__f516412af8b5
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_inP_JXJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_toMK_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool}
open PolarDecomposition
private lemma Jm_mul_self_eq_one' : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool}
open PolarDecomposition
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : inUJ ε (toMK k * NormedSpace.exp X) := by
  have hJ := Jm_mul_self_eq_one' (ε := ε)
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJ, hJ⟩, rfl⟩
  have hconj : Jm ε * NormedSpace.exp X * Jm ε = NormedSpace.exp (-X) := by
    have h := Matrix.exp_conj (Jm ε) X hJu
    rw [hJinv, inP_JXJ hX] at h
    exact h.symm
  have hf := toMK_facts k
  unfold inUJ
  rw [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose, isHermitian_of_mem_noncompactPart' hX]
  calc NormedSpace.exp X * (toMK k)ᴴ * Jm ε * (toMK k * NormedSpace.exp X)
      = NormedSpace.exp X * ((toMK k)ᴴ * (Jm ε * toMK k)) * NormedSpace.exp X := by
        simp only [mul_assoc]
    _ = NormedSpace.exp X * ((toMK k)ᴴ * (toMK k * Jm ε)) * NormedSpace.exp X := by
        rw [← hf.2.2]
    _ = NormedSpace.exp X * Jm ε * NormedSpace.exp X := by
        rw [← mul_assoc (toMK k)ᴴ, hf.1, one_mul]
    _ = Jm ε * (Jm ε * NormedSpace.exp X * Jm ε) * NormedSpace.exp X := by
        simp only [← mul_assoc, hJ, one_mul]
    _ = Jm ε * NormedSpace.exp (-X) * NormedSpace.exp X := by rw [hconj]
    _ = Jm ε := by
        rw [mul_assoc, ← Matrix.exp_add_of_commute _ _ ((Commute.refl X).neg_left), neg_add_cancel,
          NormedSpace.exp_zero, mul_one]
end ReciprocityTheory.ChartRestriction.DS.S7
