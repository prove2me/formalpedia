-- Prove2me | solution 1 for UpperTheory.V.Chr.Psi_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:14:21.472779+00:00
-- url     : https://prove2.me/submissions/911d0604-852d-4697-85c5-764e67d223f5

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CharacterLevelBounds_ShaFamMono

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
theorem _root_.solution (e : ℕ) (ψ : G k Ω →* Oˣ) : (Psi l e ψ)⁻¹ = ψ⁻¹ * chiO k Ω l O ^ (-(e : ℤ)) := by
  rw [Psi, mul_inv_rev, zpow_neg]
end UpperTheory.V.Chr
