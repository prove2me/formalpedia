-- Prove2me | solution 1 for QECCertificates.le_minWeight_of_lightCand_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:38.462427+00:00
-- url     : https://prove2.me/submissions/9b806c6c-7613-4878-aeb2-a96746fb0acb

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
public import Theorems.Thm_QECCertificates_lowerHyp_of_lightCand_nil
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
    {d₀ : ℕ} (hd : d₀ ≤ n) (h : lightCand M₁ M₂ d₀ = []) :
    d₀ ≤ minWeightKernelOutsideRowSpace M₁ M₂ :=
  le_minWeight_of_lower M₁ M₂ hd (lowerHyp_of_lightCand_nil M₁ M₂ h)
end QECCertificates
