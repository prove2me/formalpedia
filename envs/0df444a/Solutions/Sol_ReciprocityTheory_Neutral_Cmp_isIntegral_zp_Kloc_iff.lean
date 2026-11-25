-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.isIntegral_zp_Kloc_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:46:31.898348+00:00
-- url     : https://prove2.me/submissions/a37dc22c-1c29-4fba-b470-ef2b64c7c73e

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_isScalarTower_zp_Kloc_alg

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
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) :
    IsIntegral ℤ_[p] x ↔ IsIntegral (PadicInt.subring p) (x : PadicAlgCl p) := by
  have := isScalarTower_zp_Kloc_alg (F := F) ι
  rw [← isIntegral_algebraMap_iff (A := Kloc F ι) (B := PadicAlgCl p) (algebraMap (Kloc F ι) (PadicAlgCl p)).injective]
  exact Iff.rfl
end ReciprocityTheory.Neutral.Cmp
