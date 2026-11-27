-- Prove2me | solution 1 for UpperTheory.V.Base.restriction_mem_invariant_H1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:34:50.065133+00:00
-- url     : https://prove2.me/submissions/d766a9e3-a4e0-4b64-8920-1bacd0b17cfc

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
import Theorems.Thm_UpperTheory_V_Base_mk_eq_mk
import Theorems.Thm_ReciprocityTheory_Gal_mem_Z1_iff_cocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open ReciprocityTheory.Gal
namespace UpperTheory.V.Base
section Eig
variable {R Q N : Type} [CommRing R] [Group Q] [AddCommGroup N] [Module R N]
end Eig
variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
section Conj
variable [IsTopologicalGroup G] [DiscreteTopology M]
private theorem cocycle_conj_identity (ρ : Representation R G M) (U : Subgroup G) (z : Z1U ρ U) (γ v : U) :
    ρ γ (z.1 (γ⁻¹ * (v * γ))) - z.1 v = ρ v (z.1 γ) - z.1 γ := by
  have hz : ∀ a b : U, z.1 (a * b) = z.1 a + ρ a (z.1 b) := ((mem_Z1_iff_cocycle _ _).mp z.2).2
  have h1 : z.1 1 = 0 := by simpa using hz 1 1
  have hinv : ρ γ (z.1 γ⁻¹) = - z.1 γ := by
    have := hz γ γ⁻¹
    rw [mul_inv_cancel, h1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hmul : ∀ w : M, ρ γ (ρ (γ⁻¹ : U) w) = w := by
    intro w
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  rw [hz, hz, map_add, hmul, hinv]
  abel
end Conj
end UpperTheory.V.Base
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.Gal
open UpperTheory UpperTheory.V UpperTheory.V.Base
variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable [IsTopologicalGroup G] [DiscreteTopology M]
namespace UpperTheory.V.Base
theorem _root_.solution (ρ : Representation R G M) {U' U : Subgroup G} [U'.Normal] (h : U' ≤ U) (x : H1U ρ U) :
    resU ρ h x ∈ invariantsUnderSubgroupH1 ρ U U' := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := resU_mk ρ h z
  rw [e₁, Representation.mem_invariants]
  intro u
  show conjRep ρ U' (u : G) (Submodule.Quotient.mk z₁) = Submodule.Quotient.mk z₁
  obtain ⟨z₂, e₂, f₂⟩ := conjU_mk ρ U' (u : G) z₁
  rw [conjRep_apply, e₂, mk_eq_mk]
  refine ⟨z.1 u, fun v => ?_⟩
  have hc : (⟨(conjHom U' (u : G) v).1, h (conjHom U' (u : G) v).2⟩ : U) =
      u⁻¹ * (⟨v.1, h v.2⟩ * u) := Subtype.ext (by simp [conjHom, mul_assoc])
  have key := cocycle_conj_identity ρ U z u ⟨v.1, h v.2⟩
  rw [← hc] at key
  rw [f₂ v, f₁, f₁ v]
  exact key
end UpperTheory.V.Base
