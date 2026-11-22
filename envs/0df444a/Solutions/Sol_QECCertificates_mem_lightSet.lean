-- Prove2me | solution 1 for QECCertificates.mem_lightSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:34.501741+00:00
-- url     : https://prove2.me/submissions/a2f75e60-67fa-48c2-bae1-d37d5feca4c4

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {m₁ m₂ : ℕ}
    {M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)}
    {d : ℕ} {v : Vec n} :
    v ∈ lightSet M₁ M₂ d ↔ v ∈ lightCand M₁ M₂ d :=
  List.mem_toFinset
end QECCertificates
