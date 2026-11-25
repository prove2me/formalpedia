-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_JLJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:01.303458+00:00
-- url     : https://prove2.me/submissions/76ba212c-d300-4b7d-bd2d-98a29bcbe128

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_Jm_mul_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_Jm_conjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_Jconj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_neg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_half
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_gJgH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_L_herm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_LL

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
    Jm ε * polar_L g * Jm ε = -polar_L g := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hLh := polar_L_herm g
  have hJh := polar_Jm_conjTranspose ε
  have hJJ := polar_Jm_mul_self ε
  have hgJ := (polar_gJgH hg).1
  have hA : (Jm ε * polar_L g * Jm ε + Jm ε * polar_L g * Jm ε)ᴴ =
      Jm ε * polar_L g * Jm ε + Jm ε * polar_L g * Jm ε := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hLh, hJh, Matrix.mul_assoc]
  have hB : (-polar_L g + -polar_L g)ᴴ = -polar_L g + -polar_L g := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_neg, hLh]
  have hsplit : Jm ε * polar_L g * Jm ε + Jm ε * polar_L g * Jm ε =
      Jm ε * (polar_L g + polar_L g) * Jm ε := by
    rw [Matrix.mul_add, Matrix.add_mul]
  have h1 : NormedSpace.exp (Jm ε * polar_L g * Jm ε + Jm ε * polar_L g * Jm ε) =
      Jm ε * (gᴴ * g) * Jm ε := by
    rw [hsplit, polar_exp_Jconj, polar_exp_LL hg]
  have hM : (Jm ε * (gᴴ * g) * Jm ε) * (gᴴ * g) = 1 := by
    calc (Jm ε * (gᴴ * g) * Jm ε) * (gᴴ * g) = Jm ε * gᴴ * (g * Jm ε * gᴴ) * g := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε * (gᴴ * Jm ε * g) := by rw [hgJ]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hJJ]
  have hN : NormedSpace.exp (-polar_L g + -polar_L g) * (gᴴ * g) = 1 := by
    rw [← polar_exp_LL hg, show -polar_L g + -polar_L g = -(polar_L g + polar_L g) by abel]
    exact polar_exp_neg_mul _
  have h2 : NormedSpace.exp (-polar_L g + -polar_L g) = Jm ε * (gᴴ * g) * Jm ε := by
    rw [← Matrix.inv_eq_left_inv hN, Matrix.inv_eq_left_inv hM]
  exact polar_half (polar_exp_inj hA hB (h1.trans h2.symm))
end ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
