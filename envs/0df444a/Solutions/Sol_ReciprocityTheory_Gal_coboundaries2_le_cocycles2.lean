-- Prove2me | solution 1 for ReciprocityTheory.Gal.coboundaries2_le_cocycles2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:00.047219+00:00
-- url     : https://prove2.me/submissions/06e2ed52-072e-423f-805a-93a2c0a89a8d

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
theorem _root_.solution [ContinuousMul G] (h : ContAction rho) : B2 rho ≤ Z2 rho := by
  intro f hf
  obtain ⟨c, hc, rfl⟩ := (separated_dvr_second_cohomology_mem rho f).1 hf
  refine ⟨?_, fun g k l => ?_⟩
  · have h1 : Continuous fun p : G × G => rho p.1 (c p.2) :=
      h.comp (continuous_fst.prodMk (hc.comp continuous_snd))
    have h2 : Continuous fun p : G × G => c (p.1 * p.2) := hc.comp continuous_mul
    have h3 : Continuous fun p : G × G => c p.1 := hc.comp continuous_fst
    exact (h1.sub h2).add h3
  · simp only [d1_apply, map_mul, Module.End.mul_apply, map_sub, map_add, mul_assoc]
    abel
end ReciprocityTheory.Gal
