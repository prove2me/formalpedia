-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_isSelfAdjoint_isUnit_spectrum_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:36.540529+00:00
-- url     : https://prove2.me/submissions/55ada578-1317-4472-9b5e-35502cd33f8c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_spec_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_gJgH

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
    IsSelfAdjoint (gᴴ * g) ∧ IsUnit (gᴴ * g) ∧ ∀ x ∈ spectrum ℝ (gᴴ * g), 0 < x := by
  have hu : IsUnit g := (polar_gJgH hg).2
  have hu2 : IsUnit (gᴴ * g) := hu.star.mul hu
  exact ⟨Matrix.isHermitian_conjTranspose_mul_self g, hu2,
    polar_spec_pos (Matrix.posSemidef_conjTranspose_mul_self g) hu2⟩
end ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
