-- Prove2me | solution 1 for P2M_UpperTheory_V_Chr_V__le_V_2b4a0b8d1ec7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:59.651164+00:00
-- url     : https://prove2.me/submissions/a07551bd-4558-4c22-9f39-35f3e87d64b4

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CharacterLevelBounds_ShaFamMono
import Theorems.Thm_UpperTheory_V_Chr_VS_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base
open UpperTheory UpperTheory.V UpperTheory.V.Chr
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ) [Fact l.Prime]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O]
namespace UpperTheory.V.Chr
theorem _root_.solution (N e : ℕ) (ψ : G k Ω →* Oˣ) : V' l N e ψ ≤ V l e ψ := by
  exact VS_anti l (Dvd.intro N rfl) e ψ
end UpperTheory.V.Chr
