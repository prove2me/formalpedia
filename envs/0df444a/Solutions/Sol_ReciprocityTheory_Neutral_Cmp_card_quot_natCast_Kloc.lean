-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.card_quot_natCast_Kloc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:32:08.523889+00:00
-- url     : https://prove2.me/submissions/adcae678-42a0-4860-8ef8-0c6f7849e2cc

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_card_quot_natCast_padicInt
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_card_quot_span_algebraMap
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_isScalarTower_zp_integer
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_isTorsionFree_zp_Kloc
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_isIntegralClosure_Kloc
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_finiteDimensional_Kloc


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
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) {n : ℕ} (hn : n ≠ 0) :
    Nat.card (𝒪[Kloc F ι] ⧸ Ideal.span {(n : 𝒪[Kloc F ι])}) =
      p ^ (padicValNat p n * Module.finrank ℚ_[p] (Kloc F ι)) := by
  have := finiteDimensional_Kloc (F := F) ι
  have := isScalarTower_zp_integer (F := F) ι
  have := isIntegralClosure_Kloc (F := F) ι
  have := isTorsionFree_zp_Kloc (F := F) ι
  have : Module.Free ℤ_[p] 𝒪[Kloc F ι] := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] (Kloc F ι) _
  have : Module.Finite ℤ_[p] 𝒪[Kloc F ι] := IsIntegralClosure.finite ℤ_[p] ℚ_[p] (Kloc F ι) _
  have hr := IsIntegralClosure.rank ℤ_[p] ℚ_[p] (Kloc F ι) 𝒪[Kloc F ι]
  have hn' : (n : 𝒪[Kloc F ι]) = algebraMap ℤ_[p] 𝒪[Kloc F ι] n := (map_natCast _ _).symm
  rw [hn', card_quot_span_algebraMap (Module.finBasis ℤ_[p] 𝒪[Kloc F ι]), card_quot_natCast_padicInt p hn,
    Fintype.card_fin, hr, pow_mul]
end ReciprocityTheory.Neutral.Cmp
