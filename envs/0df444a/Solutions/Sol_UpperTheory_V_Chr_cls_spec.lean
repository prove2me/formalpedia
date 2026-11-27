-- Prove2me | solution 1 for UpperTheory.V.Chr.cls_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:50.309369+00:00
-- url     : https://prove2.me/submissions/cee136a2-dac7-439c-8ddd-27973a65b429

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CharacterLevelBounds_ShaFamMono
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base
open UpperTheory UpperTheory.V UpperTheory.V.Chr
variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {k Ω}
namespace UpperTheory.V.Chr
theorem _root_.solution (N : ℕ) [NeZero N] (σ : G k Ω) (ζ : Ω) (hζ : ζ ^ N = 1) : σ ζ = ζ ^ ((cls k Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp [zero_pow (NeZero.ne N)] at hζ
  have hu : Units.mk0 ζ h0 ∈ rootsOfUnity N Ω := by
    rw [mem_rootsOfUnity]
    ext
    simp [hζ]
  have := modularCyclotomicCharacter.spec Ω (card_roots k Ω N) (MulSemiringAction.toRingAut (G k Ω) Ω σ) hu
  simpa [cls] using this
end UpperTheory.V.Chr
