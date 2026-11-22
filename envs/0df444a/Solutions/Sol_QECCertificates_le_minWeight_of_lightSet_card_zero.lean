-- Prove2me | solution 1 for QECCertificates.le_minWeight_of_lightSet_card_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:33.415164+00:00
-- url     : https://prove2.me/submissions/f9dd8420-0cb6-4014-ad34-abe1328c90a0

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
public import Theorems.Thm_QECCertificates_lowerHyp_of_lightSet_card_zero
public import Theorems.Thm_QECCertificates_le_minWeight_of_lower


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : d ≤ n) (h : (lightSet M₁ M₂ d).card = 0) :
    d ≤ minWeightKernelOutsideRowSpace M₁ M₂ :=
  le_minWeight_of_lower M₁ M₂ hd (lowerHyp_of_lightSet_card_zero M₁ M₂ h)
end QECCertificates
