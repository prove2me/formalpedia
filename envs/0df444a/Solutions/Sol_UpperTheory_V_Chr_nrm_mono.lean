-- Prove2me | solution 1 for UpperTheory.V.Chr.nrm_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:01:58.856053+00:00
-- url     : https://prove2.me/submissions/903c0bf9-0554-4441-88a8-aebfbf5c0be6

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CharacterLevelBounds_ShaFamMono
import Theorems.Thm_UpperTheory_V_ThmBab_a
import Theorems.Thm_UpperTheory_V_ThmBab_b


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
theorem _root_.solution {a b : ℕ∞} (h : a ≤ b) (hb : b ≠ ⊤) : nrm l O a ≤ nrm l O b :=
  div_le_div_of_nonneg_right (by exact_mod_cast ENat.toNat_le_toNat h hb) (Nat.cast_nonneg _)
end UpperTheory.V.Chr
