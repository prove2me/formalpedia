-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.isIntegralClosure_Kloc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:02:26.666798+00:00
-- url     : https://prove2.me/submissions/99fee1df-aafa-47e8-bffe-63e8da540780

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_isIntegral_zp_Kloc_iff
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_mem_integer_Kloc
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_norm_le_one_iff_isIntegral


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
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
attribute [local instance] locRel
attribute [local instance] zpAlgInteger
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) :
    IsIntegralClosure 𝒪[Kloc F ι] ℤ_[p] (Kloc F ι) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    rw [isIntegral_zp_Kloc_iff, ← norm_le_one_iff_isIntegral, ← mem_integer_Kloc]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
end ReciprocityTheory.Neutral.Cmp
