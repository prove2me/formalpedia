-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CurryingSwaps.iteApp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:29.012363+00:00
-- url     : https://prove2.me/submissions/218e9fed-b383-475d-97f8-c2f631c4267f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PCurry

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
open PositivityTheory.Rg.Cz.CurryingSwaps
variable {α : Type*} {m k : ℕ}
namespace PositivityTheory.Rg.Cz.CurryingSwaps
theorem _root_.solution {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (p : Prop) [Decidable p]
    (g : V →ₗ[ℂ] W) (x : V) : (if p then g else 0) x = if p then g x else 0 := by
  split_ifs <;> rfl
end PositivityTheory.Rg.Cz.CurryingSwaps
