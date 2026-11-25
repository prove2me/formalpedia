-- Prove2me | solution 1 for PI.Dv.TIW.li_span_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:09.779832+00:00
-- url     : https://prove2.me/submissions/d1748144-39fb-402b-a5bd-fdf4d2311ce8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
namespace PI.Dv.TIW
theorem _root_.solution {n : ℕ} (u : Fin n → V) (hu : LinearIndependent K u) (hn : n = Module.finrank K V) :
    Submodule.span K (Set.range u) = ⊤ := by
  have h := linearIndependent_iff_card_eq_finrank_span.mp hu
  apply Submodule.eq_top_of_finrank_eq
  show Set.finrank K (Set.range u) = _
  rw [← h, Fintype.card_fin, hn]
end PI.Dv.TIW
