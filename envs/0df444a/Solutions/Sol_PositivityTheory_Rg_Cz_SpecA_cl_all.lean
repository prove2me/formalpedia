-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.cl_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:39.099044+00:00
-- url     : https://prove2.me/submissions/0c237eee-3ce1-4f51-ba47-44ed2b324b4f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_cl_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SpecA
variable {n : ℕ}
namespace PositivityTheory.Rg.Cz.SpecA
theorem _root_.solution (h1 : TensorGl) (h3 : Curry) (h5 : StepChar) : ∀ m, Cl m := by
  intro m
  induction m with
  | zero =>
    intro n M _ _ E hE l s hl hls j
    exact j.elim0
  | succ m ih =>
    rw [Nat.add_comm]
    exact cl_step h1 h3 h5 m ih
end PositivityTheory.Rg.Cz.SpecA
