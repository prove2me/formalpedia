-- Prove2me | solution 1 for QECCertificates.lightCand_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:12.78382+00:00
-- url     : https://prove2.me/submissions/79586a51-f035-4ea1-946d-8e989c665b14

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
public import Theorems.Thm_QECCertificates_length_lightVecs


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : 1 ≤ d) :
    (lightCand M₁ M₂ d).length ≤ ∑ k ∈ Finset.range d, n.choose k := by
  refine (List.length_filter_le _ _).trans ?_
  rw [length_lightVecs, show d - 1 + 1 = d from by omega]
end QECCertificates
