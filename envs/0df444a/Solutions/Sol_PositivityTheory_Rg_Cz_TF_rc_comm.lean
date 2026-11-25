-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TF.rc_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:26.589776+00:00
-- url     : https://prove2.me/submissions/51c3e67b-2510-4166-a5c4-ccdda5e70e80

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TF
namespace PositivityTheory.Rg.Cz.TF
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W] (A B : Module.End ℂ W) (h : Commute A B) :
    Commute (rc A) (rc B) := by
  show rc A * rc B = rc B * rc A
  refine LinearMap.ext fun f => LinearMap.ext fun w => ?_
  change f (B (A w)) = f (A (B w))
  exact congrArg f (LinearMap.congr_fun h.eq.symm w)
end PositivityTheory.Rg.Cz.TF
