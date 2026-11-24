-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.WallAlgP.card_lowS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:52.86035+00:00
-- url     : https://prove2.me/submissions/1f3d710f-d152-4419-be9d-28b057f99bc8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA

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
open PositivityTheory.Rg.Cz.WallAlgP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.WallAlgP
theorem _root_.solution {m k : ℕ} (hk : k ≤ m) :
    (Finset.univ.filter fun j : Fin m => (j : ℕ) < k).card = k := by
  rw [Fin.card_filter_val_lt]; omega
end PositivityTheory.Rg.Cz.WallAlgP
