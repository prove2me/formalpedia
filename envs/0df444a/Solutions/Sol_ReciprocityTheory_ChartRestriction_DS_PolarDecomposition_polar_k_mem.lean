-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_k_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:01.5146+00:00
-- url     : https://prove2.me/submissions/2ac42a2a-4790-4b4d-919f-53e8f9ef3d70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_Jm_mul_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_Jconj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_herm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_neg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_mul_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_L_herm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_LL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_JLJ

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
open scoped Matrix.Norms.L2Operator ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
namespace ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    g * NormedSpace.exp (-polar_L g) ∈ Kset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hJJ := polar_Jm_mul_self ε
  have hEiE := polar_exp_neg_mul (polar_L g)
  have hEEi := polar_exp_mul_neg (polar_L g)
  have hgg : gᴴ * g = NormedSpace.exp (polar_L g) * NormedSpace.exp (polar_L g) := by
    rw [← polar_exp_two, polar_exp_LL hg]
  have hEih : (NormedSpace.exp (-polar_L g))ᴴ = NormedSpace.exp (-polar_L g) :=
    polar_exp_herm (by rw [Matrix.conjTranspose_neg, polar_L_herm])
  have hEiJ : NormedSpace.exp (-polar_L g) * Jm ε = Jm ε * NormedSpace.exp (polar_L g) := by
    have h := polar_exp_Jconj ε (polar_L g)
    rw [polar_JLJ hg] at h
    rw [h, Matrix.mul_assoc (Jm ε * NormedSpace.exp (polar_L g)), hJJ, Matrix.mul_one]
  have hkk : (g * NormedSpace.exp (-polar_L g))ᴴ * (g * NormedSpace.exp (-polar_L g)) = 1 := by
    calc (g * NormedSpace.exp (-polar_L g))ᴴ * (g * NormedSpace.exp (-polar_L g))
        = NormedSpace.exp (-polar_L g) * (gᴴ * g) * NormedSpace.exp (-polar_L g) := by
          rw [Matrix.conjTranspose_mul, hEih]; simp only [Matrix.mul_assoc]
      _ = (NormedSpace.exp (-polar_L g) * NormedSpace.exp (polar_L g)) *
          (NormedSpace.exp (polar_L g) * NormedSpace.exp (-polar_L g)) := by
          rw [hgg]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hEiE, hEEi, Matrix.mul_one]
  have hkJ : (g * NormedSpace.exp (-polar_L g))ᴴ * Jm ε * (g * NormedSpace.exp (-polar_L g)) = Jm ε := by
    calc (g * NormedSpace.exp (-polar_L g))ᴴ * Jm ε * (g * NormedSpace.exp (-polar_L g))
        = NormedSpace.exp (-polar_L g) * (gᴴ * Jm ε * g) * NormedSpace.exp (-polar_L g) := by
          rw [Matrix.conjTranspose_mul, hEih]; simp only [Matrix.mul_assoc]
      _ = NormedSpace.exp (-polar_L g) * Jm ε * NormedSpace.exp (-polar_L g) := by rw [hg']
      _ = Jm ε * NormedSpace.exp (polar_L g) * NormedSpace.exp (-polar_L g) := by rw [hEiJ]
      _ = Jm ε := by rw [Matrix.mul_assoc, hEEi, Matrix.mul_one]
  have hkk' : (g * NormedSpace.exp (-polar_L g)) * (g * NormedSpace.exp (-polar_L g))ᴴ = 1 :=
    mul_eq_one_comm.1 hkk
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 hkk, ?_⟩
  calc (g * NormedSpace.exp (-polar_L g)) * Jm ε
      = (g * NormedSpace.exp (-polar_L g)) *
        ((g * NormedSpace.exp (-polar_L g))ᴴ * Jm ε * (g * NormedSpace.exp (-polar_L g))) := by
        rw [hkJ]
    _ = ((g * NormedSpace.exp (-polar_L g)) * (g * NormedSpace.exp (-polar_L g))ᴴ) * Jm ε *
        (g * NormedSpace.exp (-polar_L g)) := by simp only [Matrix.mul_assoc]
    _ = Jm ε * (g * NormedSpace.exp (-polar_L g)) := by rw [hkk', Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
