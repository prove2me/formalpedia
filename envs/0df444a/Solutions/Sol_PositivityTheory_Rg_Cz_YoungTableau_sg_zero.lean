-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.YoungTableau.sg_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:38:19.728045+00:00
-- url     : https://prove2.me/submissions/120e8e31-0eaa-4c38-a9cc-3d551609022f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA

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
open PositivityTheory.Rg.Cz.YoungTableau
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {X : Type} [Fintype X] [DecidableEq X]
  {C : Type} [DecidableEq C]
namespace PositivityTheory.Rg.Cz.YoungTableau
theorem _root_.solution (col : X → C) (b : X → Fin n) (v : X → Fin n) (h : ¬ ∃ π ∈ colG col, b ∘ π = v) :
    sg col b v = 0 := by
  unfold sg
  refine Finset.sum_eq_zero fun π hπ => ?_
  rw [if_neg]
  exact fun h' => h ⟨π, hπ, h'⟩
end PositivityTheory.Rg.Cz.YoungTableau
