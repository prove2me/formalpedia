-- Prove2me | solution 1 for UpperTheory.V.conjGal_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:51.376554+00:00
-- url     : https://prove2.me/submissions/a1e00c9e-86a0-463c-ae3a-0cce910641cf

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
open UpperTheory UpperTheory.V
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable {τ : F ≃+* F} {σ : Ω ≃+* Ω}
omit [NumberField F]
namespace UpperTheory.V
theorem _root_.solution (h : IsLift τ σ) (g : G F Ω) (x : Ω) : conjGal h g x = σ.symm (g (σ x)) := rfl
end UpperTheory.V
