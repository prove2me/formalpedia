-- Prove2me | solution 1 for ReciprocityTheory.Gal.isClosed_Ine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:47.809748+00:00
-- url     : https://prove2.me/submissions/df1028f4-64f4-41e4-b0e3-1ff24292460f

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Theorems.Thm_ReciprocityTheory_Gal_isClosed_Dec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain Pointwise
namespace ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
section unram
variable (S : Set (HeightOneSpectrum (𝓞 F)))
end unram
section Basic₃
private theorem isClosed_setOf_apply_lemma [IsAlgClosure F Ω] (x : Ω) (P : Ω → Prop) :
    IsClosed {τ : G F Ω | P (τ x)} := by
  have hal : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hfd : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hH : IsOpen ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (G F Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ : G F Ω => σ⁻¹ * τ) ⁻¹' ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (G F Ω)),
    ?_, hH.preimage (continuous_const.mul continuous_id), ?_⟩
  · intro τ hτ hPτ
    have h1 : (σ⁻¹ * τ) x = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x (IntermediateField.mem_adjoin_simple_self F x)
    have h2 : τ x = σ x := by
      have h3 := congrArg σ h1
      rwa [AlgEquiv.mul_apply, mul_inv_apply] at h3
    exact hσ (by simpa only [Set.mem_setOf_eq, h2] using hPτ)
  · show σ⁻¹ * σ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _
end Basic₃
end ReciprocityTheory.Gal
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution [IsAlgClosure F Ω] (A : ValuationSubring (Ω)) : IsClosed (Ine (F := F) A : Set (G F Ω)) := by
  have e : (Ine (F := F) A : Set (G F Ω)) = (Dec (F := F) A : Set (G F Ω)) ∩
      ⋂ x : Ω, {τ : G F Ω | A.valuation x ≤ 1 → A.valuation (τ x - x) < 1} := by
    ext τ
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [e]
  exact (isClosed_Dec A).inter (isClosed_iInter fun x =>
    isClosed_setOf_apply_lemma x (fun y => A.valuation x ≤ 1 → A.valuation (y - x) < 1))
end ReciprocityTheory.Gal
