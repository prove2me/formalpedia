-- Prove2me | solution 1 for ResidualGaloisRep.baseChangeAlong_residueFieldMap_algebraMap_self_isEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/468a414b-0d25-589b-a42e-d017c204f967

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_baseChangeAlong_residueFieldMap_algebraMap_self_isEquiv

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

theorem solution {𝒪 : Type}
    [CommRing 𝒪] [IsLocalRing 𝒪] (ρ : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)) :
    (ρ.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪))).IsEquiv ρ :=
  ⟨(Classical.choice (ResidualGaloisRep.D5Sol.isEquiv_baseChangeAlong_of_apply_eq ρ _
    ResidualGaloisRep.D5Sol.residueFieldMap_algebraMap_self_apply)).symm⟩

end S_ResidualGaloisRep_baseChangeAlong_residueFieldMap_algebraMap_self_isEquiv
end P2MW
export P2MW.S_ResidualGaloisRep_baseChangeAlong_residueFieldMap_algebraMap_self_isEquiv (solution)
