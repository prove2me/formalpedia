-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TrOf.exists_sort
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:37:00.42319+00:00
-- url     : https://prove2.me/submissions/8e3a3f4d-8650-4215-95ae-04b892a1e364

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransOf

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
open PositivityTheory.Rg.Cz.TrOf
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
omit [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TrOf
theorem _root_.solution {α : Type} [LinearOrder α] (key : P → α) :
    ∃ e : P ≃ Fin (Fintype.card P), Monotone (key ∘ e.symm) :=
  ⟨(Fintype.equivFin P).trans (Tuple.sort (key ∘ (Fintype.equivFin P).symm)).symm,
    Tuple.monotone_sort (key ∘ (Fintype.equivFin P).symm)⟩
end PositivityTheory.Rg.Cz.TrOf
