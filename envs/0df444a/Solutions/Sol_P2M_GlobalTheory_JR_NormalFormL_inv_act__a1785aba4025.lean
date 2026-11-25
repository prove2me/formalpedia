-- Prove2me | solution 1 for P2M_GlobalTheory_JR_NormalFormL_inv_act__a1785aba4025
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:31:19.118199+00:00
-- url     : https://prove2.me/submissions/8acd36c1-a1c1-463d-8bc2-f25bba3aa829

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
theorem _root_.solution (g : GL (Fin r) k) (Y : Gl r k) : inv (act g Y) = inv Y := by
  obtain ⟨A, b, c, l⟩ := Y
  simp only [inv, act, mom, Prod.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · funext i
    rw [Matrix.coe_units_inv, charpoly_units_conj]
  · funext i
    rw [Units.conj_pow, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
    congr 2
    simp [mul_assoc]
end GlobalTheory.JR.NormalFormL
