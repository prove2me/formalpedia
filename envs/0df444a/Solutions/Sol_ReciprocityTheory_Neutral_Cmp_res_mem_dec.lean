-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.res_mem_dec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:30.552151+00:00
-- url     : https://prove2.me/submissions/1f5d2d93-d3f3-4ea7-a81b-c9e1e6dbf4dc

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ContinuousGK
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_res_spec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Pointwise
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
private theorem norm_GK_lemma (ι : Ω →+* PadicAlgCl p) (σ : GK F ι) (y : PadicAlgCl p) : ‖σ y‖ = ‖y‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  unfold spectralNorm
  exact congrArg _ (minpoly.algEquiv_eq (σ.restrictScalars ℚ_[p]) y)
end ReciprocityTheory.Neutral.Cmp
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Pointwise
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) (σ : GK F ι) :
    res ι σ ∈ Dec (F := F) A := by
  have hτ : ∀ x, res ι σ x ∈ A ↔ x ∈ A := fun x => by rw [h, h, res_spec, norm_GK_lemma]
  rw [Dec, ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (hτ s).2 hs
  · intro hx
    refine ⟨(res ι σ).symm x, (hτ _).1 ?_, ?_⟩
    · rwa [AlgEquiv.apply_symm_apply]
    · exact AlgEquiv.apply_symm_apply _ _
end ReciprocityTheory.Neutral.Cmp
