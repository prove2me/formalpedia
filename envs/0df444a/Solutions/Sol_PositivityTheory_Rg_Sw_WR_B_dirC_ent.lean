-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_ent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:02.623546+00:00
-- url     : https://prove2.me/submissions/c0f18344-29c4-41fe-b59e-be6ab5acb333

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_uM
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_vM


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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (k l : Fin n) (e : Bool × Fin n × Fin n) :
    dirC (ent s e) (vkl k l) y = MvPolynomial.eval (fun e => ent s e y) (dEnt s k l e) := by
  obtain ⟨b, a, c⟩ := e
  cases b
  · have e1 : ent (n := n) s (false, a, c) = fun y => uM s y a c := by funext y; simp [ent]
    rw [e1, dirC_uM hs]
    simp [dEnt, ent] <;> ring
  · have e1 : ent (n := n) s (true, a, c) = fun y => vM s y a c := by funext y; simp [ent]
    rw [e1, dirC_vM hs]
    simp [dEnt, ent] <;> ring
end PositivityTheory.Rg.Sw.WR.B
