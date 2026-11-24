-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.mul_mem_SU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:50.058344+00:00
-- url     : https://prove2.me/submissions/63e7ceb0-a632-45a6-bd83-34bb89aa548f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] (σ : R →+* R)
  (J : Matrix ι ι R)
variable {σ J}
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {g h : Matrix ι ι R} (hg : g ∈ SU σ J) (hh : h ∈ SU σ J) : g * h ∈ SU σ J := by
  refine ⟨by rw [det_mul, hg.1, hh.1, one_mul], ?_⟩
  rw [transpose_mul, Matrix.map_mul,
    show hᵀ * gᵀ * J * (g.map σ * h.map σ) = hᵀ * (gᵀ * J * g.map σ) * h.map σ by
      simp only [Matrix.mul_assoc],
    hg.2, hh.2]
end ReciprocityTheory.ChartRestriction.G.SA
