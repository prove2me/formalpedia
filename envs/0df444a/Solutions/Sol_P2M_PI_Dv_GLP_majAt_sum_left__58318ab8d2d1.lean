-- Prove2me | solution 1 for P2M_PI_Dv_GLP_majAt_sum_left__58318ab8d2d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:42.396809+00:00
-- url     : https://prove2.me/submissions/62831e17-d268-41ce-af42-7d22f458c5a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_MajAtZeroRight
import Theorems.Thm_P2M_PI_Dv_GLP_majAt_add_left__5d03aae9c39c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Formalism.HermitianLatticesTheory NumberField
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)
namespace PI.Dv.GLP
theorem _root_.solution {α : Type} (s : Finset α) (f : α → V) (y : V) :
    majAt b X v (∑ i ∈ s, f i) y = ∑ i ∈ s, majAt b X v (f i) y := by
  exact map_sum (AddMonoidHom.mk' (fun x => majAt b X v x y) fun x x' => majAt_add_left' b X v x x' y) f s
end PI.Dv.GLP
