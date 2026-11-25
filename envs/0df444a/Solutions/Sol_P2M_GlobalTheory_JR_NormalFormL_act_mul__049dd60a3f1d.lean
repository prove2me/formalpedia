-- Prove2me | solution 1 for P2M_GlobalTheory_JR_NormalFormL_act_mul__049dd60a3f1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:31:16.169188+00:00
-- url     : https://prove2.me/submissions/1b15059e-f014-47dd-981d-cda2c6d96b09

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.NormalFormL
theorem _root_.solution (g h : GL (Fin r) k) (Y : Gl r k) : act (g * h) Y = act g (act h Y) := by
  obtain ⟨A, b, c, l⟩ := Y
  simp only [act, _root_.mul_inv_rev, Units.val_mul, mulVec_mulVec, vecMul_vecMul, Prod.mk.injEq, and_true]
  try simp [mul_assoc]
end GlobalTheory.JR.NormalFormL
