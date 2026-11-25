-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_evUV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:03:49.31313+00:00
-- url     : https://prove2.me/submissions/c67bce61-0200-42af-a872-9fb58b5697f1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_evUV_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_ent
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_ent
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_eval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (k l : Fin n) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    dirC (evUV s R) (vkl k l) y = evUV s (∑ e, MvPolynomial.pderiv e R * dEnt s k l e) y := by
  rw [show evUV s R = fun y => MvPolynomial.eval (fun e => ent s e y) R from rfl,
    dirC_eval (fun e y => ent s e y) (contDiff_ent hs) (vkl k l) y R, evUV_eq]
  simp only [map_sum, map_mul]
  exact Finset.sum_congr rfl fun e _ => by rw [dirC_ent hs]
end PositivityTheory.Rg.Sw.WR.B
