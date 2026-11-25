-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.isScalarTower_zp_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:34:55.82061+00:00
-- url     : https://prove2.me/submissions/450f4526-398f-491f-bec7-61995c35e785

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF

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
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) : IsScalarTower ℤ_[p] 𝒪[Kloc F ι] (Kloc F ι) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
end ReciprocityTheory.Neutral.Cmp
