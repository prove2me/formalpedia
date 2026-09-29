-- Prove2me | solution 1 for ResidualGaloisRep.isEquiv_baseChangeAlong_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f3140fb0-114a-52d7-974f-5d4e354fcdae

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_isEquiv_baseChangeAlong_id

open scoped TensorProduct

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "IsEquiv baseChangeAlong V ρ"
namespace D5Sol
p2m_open "ResidualGaloisRep"

variable {k : Type} [Field k]

theorem isEquiv_baseChangeAlong_of_apply_eq (ρ : ResidualGaloisRep k) (φ : k →+* k)
    (hφ : ∀ x, φ x = x) : ρ.IsEquiv (ρ.baseChangeAlong φ) := by
  obtain rfl : φ = RingHom.id k := RingHom.ext hφ
  exact ⟨⟨((TensorProduct.lid k ρ.V).symm : ρ.V ≃ₗ[k] (ρ.baseChangeAlong (RingHom.id k)).V),
    fun σ x => rfl⟩⟩

theorem residueFieldMap_algebraMap_self_apply {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    (x : IsLocalRing.ResidueField 𝒪) : IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪) x = x := by
  induction x using Quotient.inductionOn' with
  | h a => rfl

end ResidualGaloisRep.D5Sol

theorem solution {k : Type} [Field k] (ρ : ResidualGaloisRep k) :
    ρ.IsEquiv (ρ.baseChangeAlong (RingHom.id k)) :=
  ResidualGaloisRep.D5Sol.isEquiv_baseChangeAlong_of_apply_eq ρ _ fun _ => rfl

end S_ResidualGaloisRep_isEquiv_baseChangeAlong_id
end P2MW
export P2MW.S_ResidualGaloisRep_isEquiv_baseChangeAlong_id (solution)
