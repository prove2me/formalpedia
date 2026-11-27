-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_conj_mem_KE_b1f417f21d69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:50:54.78463+00:00
-- url     : https://prove2.me/submissions/d6df403f-3884-4e5d-b60e-691dcdc01c9c

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocG
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_phi_mem_26f23f35fb3f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime]
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (φ : F →+* PadicAlgCl l) (τ : ↥(Kphi φ) →ₐ[ℚ_[l]] PadicAlgCl l) (y : ↥(Kphi φ)) :
    τ y ∈ KE l F := by
  let ψ : F →+* PadicAlgCl l := τ.toRingHom.comp (φ.codRestrict (Kphi φ) (phi_mem φ))
  have hle : Kphi φ ≤ ((Kphi ψ).comap τ).map (Kphi φ).val := by
    show IntermediateField.adjoin ℚ_[l] _ ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro s ⟨i, rfl⟩
    first
    | exact ⟨⟨φ (Module.finBasis ℚ F i), phi_mem φ _⟩, phi_mem ψ (Module.finBasis ℚ F i), rfl⟩
    | exact IntermediateField.mem_map.mpr
        ⟨⟨φ (Module.finBasis ℚ F i), phi_mem φ _⟩, phi_mem ψ (Module.finBasis ℚ F i), rfl⟩
  obtain ⟨z, hz, hzy⟩ := hle y.2
  have hzy' : z = y := Subtype.ext hzy
  have key : τ y ∈ Kphi ψ := by
    rw [← hzy']
    exact hz
  exact (le_iSup (fun ψ' : F →+* PadicAlgCl l => Kphi ψ') ψ) key
end Formalism.BasicNotions.Examples₂.LB
