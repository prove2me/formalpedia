-- Prove2me | solution 1 for P2M_Formalism_YangianSpanCharacter_P_y1__alg_62a8488f9a3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:49:07.40473+00:00
-- url     : https://prove2.me/submissions/9ee9e418-5d2e-4487-8100-92d8ea1be9cd

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Theorems.Thm_Formalism_YangianSpanCharacter_P_comm_of_inv
import Theorems.Thm_Formalism_YangianSpanCharacter_P_smul_cancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution {a b ai bi X Y : A} {c : 𝕜} (hc : c ≠ 0)
    (hR1 : c • (a * Y - Y * a) = X * b - Y * a) (hR2 : (-c) • (b * X - X * b) = Y * a - X * b)
    (hb1 : b * bi = 1) (hb2 : bi * b = 1) (ha1 : a * ai = 1) (hab : a * b = b * a) :
    a * (bi * Y) - bi * Y * a = a * (c⁻¹ • (ai * X - bi * Y)) := by
  have hc' : a * bi = bi * a := comm_of_inv hb1 hb2 hab
  have hc'' : a * (bi * Y) = bi * (a * Y) := by rw [← mul_assoc, hc', mul_assoc]
  have hD : a * Y - Y * a = b * X - X * b := by
    apply smul_cancel hc
    rw [hR1, ← neg_sub (Y * a) (X * b), ← hR2, neg_smul, neg_neg]
  have hXb : X * b = b * X - (a * Y - Y * a) := by rw [hD]; abel
  have hbX : bi * (b * X) = X := by rw [← mul_assoc, hb2, one_mul]
  have haX : a * (ai * X) = X := by rw [← mul_assoc, ha1, one_mul]
  have hL : a * (bi * Y) - bi * Y * a = bi * (a * Y - Y * a) := by
    rw [hc'', mul_sub, mul_assoc]
  apply smul_cancel hc
  rw [hL, mul_smul_comm, smul_smul, mul_inv_cancel₀ hc, one_smul, ← mul_smul_comm, hR1]
  rw [hXb]
  simp only [mul_sub]
  rw [hbX, haX, hc'']
  abel
end Formalism.YangianSpanCharacter.P
