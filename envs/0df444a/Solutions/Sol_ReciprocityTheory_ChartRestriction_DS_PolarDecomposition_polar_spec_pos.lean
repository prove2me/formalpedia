-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_spec_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:49.139831+00:00
-- url     : https://prove2.me/submissions/0fe605a7-ce3c-4e6d-b411-0b953f635789

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose

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
theorem _root_.solution {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef) (hu : IsUnit P) :
    ∀ x ∈ spectrum ℝ P, 0 < x := by
  intro x hx
  rw [hP.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  have h0 := hP.eigenvalues_nonneg i
  have hne : hP.isHermitian.eigenvalues i ≠ 0 := by
    intro h
    have hmem := hP.isHermitian.eigenvalues_mem_spectrum_real i
    rw [h, spectrum.zero_mem_iff] at hmem
    exact hmem hu
  exact lt_of_le_of_ne h0 (Ne.symm hne)
end ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
