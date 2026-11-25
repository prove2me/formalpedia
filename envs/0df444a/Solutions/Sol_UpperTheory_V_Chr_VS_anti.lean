-- Prove2me | solution 1 for UpperTheory.V.Chr.VS_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:12:21.100721+00:00
-- url     : https://prove2.me/submissions/a0a5e68e-f992-4bf7-9897-f735352bd358

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CharacterLevelBounds_ShaFamMono
import Theorems.Thm_UpperTheory_V_Chr_shaFam_mono
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
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ) [Fact l.Prime]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O]
namespace UpperTheory.V.Chr
theorem _root_.solution {m n : ℕ} (h : m ∣ n) (e : ℕ) (ψ : G k Ω →* Oˣ) : VS l n e ψ ≤ VS l m e ψ := by
  have hle : ShaU (rho l e ψ) n ⊤ ≤ ShaU (rho l e ψ) m ⊤ := by
    intro x hx
    simp only [ShaU, LocSel, Submodule.mem_iInf] at hx ⊢
    intro D hD
    exact hx D (shaFam_mono h hD)
  exact Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
end UpperTheory.V.Chr
