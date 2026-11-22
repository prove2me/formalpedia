-- Prove2me | solution 1 for QECCertificates.eq_minWeight_of_lightCand_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:38.884607+00:00
-- url     : https://prove2.me/submissions/03c25879-2f8e-431c-9a1b-d2ff40e74e77

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
public import Theorems.Thm_QECCertificates_lowerHyp_of_lightCand_nil
public import Theorems.Thm_QECCertificates_eq_minWeight_of_bounds


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : d ≤ n) (hlow : lightCand M₁ M₂ d = []) {E : Vec n}
    (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.certificateRowSpace) (hw : hammingNorm E =
      d) :
    minWeightKernelOutsideRowSpace M₁ M₂ = d :=
  eq_minWeight_of_bounds M₁ M₂ hd hker hnot hw (lowerHyp_of_lightCand_nil M₁ M₂ hlow)
end QECCertificates
