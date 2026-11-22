-- Prove2me | solution 1 for QECCertificates.mem_ker_of_inKerB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:48.281433+00:00
-- url     : https://prove2.me/submissions/4ab9e05a-81f8-4ff2-9daf-13b60b1dd76c

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
public import Theorems.Thm_QECCertificates_inKerB_iff


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) {v : Vec n}
    (h : inKerB M v = true) : v ∈ LinearMap.ker M.toLin' :=
  (inKerB_iff M v).mp h
end QECCertificates
