-- Prove2me | solution 1 for UpperTheory.V.Base.mk_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:29.619799+00:00
-- url     : https://prove2.me/submissions/89670157-917b-4a5e-9033-927b1f34cee3

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.Gal
open UpperTheory UpperTheory.V UpperTheory.V.Base
variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
namespace UpperTheory.V.Base
theorem _root_.solution (ρ : Representation R G M) (U : Subgroup G) (z z' : Z1U ρ U) :
    (Submodule.Quotient.mk z : H1U ρ U) = Submodule.Quotient.mk z' ↔
      ∃ m, ∀ u : U, z.1 u - z'.1 u = ρ u m - m := by
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
  exact Iff.rfl
end UpperTheory.V.Base
