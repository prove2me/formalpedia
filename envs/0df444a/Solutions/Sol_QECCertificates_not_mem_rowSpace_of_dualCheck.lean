-- Prove2me | solution 1 for QECCertificates.not_mem_rowSpace_of_dualCheck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:54.387277+00:00
-- url     : https://prove2.me/submissions/f3d04c7a-bf87-44f2-8db7-1d56ae831b65

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
public import Theorems.Thm_QECCertificates_DualWitness_not_mem_rowSpace
public import Theorems.Thm_QECCertificates_inKerB_iff


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    {E w : Vec n} (hk : inKerB H w = true) (hp : w ⬝ᵥ E = 1) : E ∉ H.certificateRowSpace :=
  DualWitness.not_mem_rowSpace ⟨w, (inKerB_iff H w).mp hk, hp⟩
end QECCertificates
