-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.continuous_GK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:33:13.086619+00:00
-- url     : https://prove2.me/submissions/119e129e-23ce-486b-986d-c87c04635c99

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ContinuousGK
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
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) (σ : GK F ι) : Continuous σ :=
  (AddMonoidHomClass.isometry_of_norm σ (norm_GK_lemma ι σ)).continuous
end ReciprocityTheory.Neutral.Cmp
