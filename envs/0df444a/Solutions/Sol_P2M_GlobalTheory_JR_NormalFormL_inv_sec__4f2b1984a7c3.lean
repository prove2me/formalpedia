-- Prove2me | solution 1 for P2M_GlobalTheory_JR_NormalFormL_inv_sec__4f2b1984a7c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:19:34.418112+00:00
-- url     : https://prove2.me/submissions/d4a3a02d-51de-4776-b1c3-15922bdbd635

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Theorems.Thm_GlobalTheory_JR_NormalFormL_ev_eq_single
import Theorems.Thm_GlobalTheory_JR_NormalFormL_companion_pow_ev
import Theorems.Thm_GlobalTheory_JR_NormalFormL_charpoly_companion_coeff

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
theorem _root_.solution (a : Inv r k) : inv (sec a) = a := by
  obtain ⟨p, m, l⟩ := a
  simp only [inv, sec, Prod.mk.injEq, and_true]
  refine ⟨funext fun i => charpoly_companion_coeff p i, funext fun i => ?_⟩
  have he : (fun i : Fin r => if (i : ℕ) = 0 then (1 : k) else 0) = ev r k 0 := rfl
  simp only [mom, he, companion_pow_ev p i i.2, ev_eq_single (i : ℕ) i.2, dotProduct_single, mul_one]
end GlobalTheory.JR.NormalFormL
