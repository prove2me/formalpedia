-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_gJgH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:28.448936+00:00
-- url     : https://prove2.me/submissions/9bd24a79-ea62-4174-9f56-4f361f5bb58c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_Jm_mul_self

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
    g * Jm ε * gᴴ = Jm ε ∧ IsUnit g := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hJJ := polar_Jm_mul_self ε
  have hleft : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hJJ]
  have hright : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.1 hleft
  refine ⟨?_, ⟨⟨g, _, hright, hleft⟩, rfl⟩⟩
  calc g * Jm ε * gᴴ = g * (Jm ε * gᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
    _ = Jm ε := by rw [hright, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
