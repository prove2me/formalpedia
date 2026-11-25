-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.res_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:28:17.723975+00:00
-- url     : https://prove2.me/submissions/56648c20-d7aa-46ca-8210-f7b312e4bfb4

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ContinuousGK
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_res_spec
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_continuous_GK
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_denseRange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Pointwise
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) : Function.Injective (res (F := F) ι) := by
  intro σ τ h
  have h2 : (σ : PadicAlgCl p → PadicAlgCl p) ∘ ι = (τ : PadicAlgCl p → PadicAlgCl p) ∘ ι := by
    funext x
    simp only [Function.comp_apply]
    rw [← res_spec ι σ x, ← res_spec ι τ x, h]
  exact AlgEquiv.ext (congrFun
    ((denseRange (F := F) ι).equalizer (continuous_GK ι σ) (continuous_GK ι τ) h2))
end ReciprocityTheory.Neutral.Cmp
