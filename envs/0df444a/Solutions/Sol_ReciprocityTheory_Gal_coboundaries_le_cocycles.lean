-- Prove2me | solution 1 for ReciprocityTheory.Gal.coboundaries_le_cocycles
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:00.017532+00:00
-- url     : https://prove2.me/submissions/4bd64561-3727-4a3f-a2be-78a9d9c37204

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_SeparatedDvrSecondCohomologyMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Gal
set_option linter.unusedVariables false
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)
namespace ReciprocityTheory.Gal
theorem _root_.solution (h : ContAction rho) : B1 rho ≤ Z1 rho := by
  intro f hf
  obtain ⟨m, hm⟩ := (mem_coboundaries1 rho f).1 hf
  obtain rfl : f = fun g => rho g m - m := funext hm
  refine ⟨(h.comp (continuous_id.prodMk continuous_const)).sub continuous_const, fun g k => ?_⟩
  simp only [map_mul, Module.End.mul_apply, map_sub]
  abel
end ReciprocityTheory.Gal
