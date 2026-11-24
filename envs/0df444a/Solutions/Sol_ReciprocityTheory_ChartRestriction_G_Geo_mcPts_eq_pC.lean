-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.mcPts_eq_pC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:54.064523+00:00
-- url     : https://prove2.me/submissions/0e17a2d3-1a18-4876-b223-4c231e7fc282

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (P : Ideal (MRing ι)) :
    mcPts P = {z | (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ pC P, eval z f = 0} := by
  ext z
  simp only [mcPts, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun f hf => ?_⟩
    have hle : pC P ≤ RingHom.ker (MvPolynomial.eval z) :=
      Ideal.span_le.2 (by rintro _ ⟨g, hg, rfl⟩; exact h2 g hg)
    exact RingHom.mem_ker.1 (hle hf)
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun f hf => h2 _ (Ideal.subset_span ⟨f, hf, rfl⟩)⟩
end ReciprocityTheory.ChartRestriction.G.Geo
