-- Prove2me | solution 1 for UpperTheory.V.Base.resU_conjRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:10:11.54436+00:00
-- url     : https://prove2.me/submissions/4ee8049f-6b17-4af8-bd32-51ba52e4a12e

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
variable [IsTopologicalGroup G] [DiscreteTopology M]
namespace UpperTheory.V.Base
theorem _root_.solution (ρ : Representation R G M) {U' U : Subgroup G} [U.Normal] [U'.Normal] (h : U' ≤ U) (g : G)
    (x : H1U ρ U) : resU ρ h (conjRep ρ U g x) = conjRep ρ U' g (resU ρ h x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := conjU_mk ρ U g z
  obtain ⟨z₂, e₂, f₂⟩ := resU_mk ρ h z₁
  obtain ⟨z₃, e₃, f₃⟩ := resU_mk ρ h z
  obtain ⟨z₄, e₄, f₄⟩ := conjU_mk ρ U' g z₃
  rw [conjRep_apply, conjRep_apply, e₁, e₂, e₃, e₄]
  congr 1
  refine Subtype.ext (funext fun u => ?_)
  rw [f₂, f₁, f₄, f₃]
  exact congrArg (fun t => ρ g (z.1 t)) (Subtype.ext (by simp [conjHom]))
end UpperTheory.V.Base
