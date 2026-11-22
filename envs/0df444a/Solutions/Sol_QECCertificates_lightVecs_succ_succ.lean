-- Prove2me | solution 1 for QECCertificates.lightVecs_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:49:38.795406+00:00
-- url     : https://prove2.me/submissions/bea5eee2-a09c-4c11-b8b0-8bb28305dad1

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (n w : ℕ) :
    lightVecs (n + 1) (w + 1) = (lightVecs n (w + 1)).map (fun u => snocV u 0)
      ++ (lightVecs n w).map (fun u => snocV u 1) := by
  rw [lightVecs.eq_3]
end QECCertificates
