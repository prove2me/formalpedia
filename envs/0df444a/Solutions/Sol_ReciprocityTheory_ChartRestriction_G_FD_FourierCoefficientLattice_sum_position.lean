-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.sum_position
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:03.098874+00:00
-- url     : https://prove2.me/submissions/d1db2bda-4ad3-49fb-b3b6-72bb18c6dde7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientLattice_position_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
theorem _root_.solution (y : ι → Fin 2 → Fin 2 → ℝ) :
    y = ∑ i0, ∑ k0, intersection_update_fsHerm_neg_one i0 k0 (fun τ => y τ i0 k0) := by
  funext τ i k
  simp only [Finset.sum_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases k <;> simp [position_apply]
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
