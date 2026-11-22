-- Prove2me | solution 1 for ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:53.375161+00:00
-- url     : https://prove2.me/submissions/5777ab32-551e-4ea2-b776-8f16263a9076

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
theorem _root_.solution (m : M) : m ∈ H0 rho ↔ ∀ g, rho g m = m := Iff.rfl
end ReciprocityTheory.Gal
