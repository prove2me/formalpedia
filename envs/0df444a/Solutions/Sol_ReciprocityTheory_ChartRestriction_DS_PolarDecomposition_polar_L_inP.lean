-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L_inP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:40.672991+00:00
-- url     : https://prove2.me/submissions/a7506034-28fb-4c2b-bf72-d04f90f97ce5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_Jm_mul_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_L_herm
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
    inP ε (polar_L g) := by
  have h := polar_JLJ hg
  have hJJ := polar_Jm_mul_self ε
  have h2 : Jm ε * polar_L g = -(polar_L g * Jm ε) := by
    calc Jm ε * polar_L g = Jm ε * polar_L g * Jm ε * Jm ε := by
          rw [Matrix.mul_assoc (Jm ε * polar_L g) (Jm ε) (Jm ε), hJJ, Matrix.mul_one]
      _ = -polar_L g * Jm ε := by rw [h]
      _ = -(polar_L g * Jm ε) := Matrix.neg_mul _ _
  refine ⟨?_, by rw [h2, neg_neg]⟩
  show (polar_L g)ᴴ * Jm ε + Jm ε * polar_L g = 0
  rw [polar_L_herm, h2, add_neg_cancel]
end ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
