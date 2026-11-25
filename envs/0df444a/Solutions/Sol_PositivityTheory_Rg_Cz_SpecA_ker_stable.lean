-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.ker_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:41.923801+00:00
-- url     : https://prove2.me/submissions/023f13d5-3b61-4232-a100-ef9c7e7d1b5e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum

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
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (Y X : Module.End ℂ V) (h : Commute Y X) :
    ∀ w ∈ LinearMap.ker Y, X w ∈ LinearMap.ker Y := by
  intro w hw
  rw [LinearMap.mem_ker] at hw ⊢
  rw [← Module.End.mul_apply, h.eq, Module.End.mul_apply, hw, map_zero]
end PositivityTheory.Rg.Cz.SpecA
