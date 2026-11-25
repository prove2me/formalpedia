-- Prove2me | solution 1 for P2M_PI_Dv_GLP_majAt_sum_right__14e5aa179fb6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:01.477527+00:00
-- url     : https://prove2.me/submissions/7c0fcc6b-9eba-4240-9aea-94735a0206a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_MajAtZeroRight
import Theorems.Thm_P2M_PI_Dv_GLP_majAt_add_right__f7ddb772f55e

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
theorem _root_.solution {α : Type} (s : Finset α) (f : α → V) (x : V) :
    majAt b X v x (∑ i ∈ s, f i) = ∑ i ∈ s, majAt b X v x (f i) := by
  exact map_sum (AddMonoidHom.mk' (fun y => majAt b X v x y) fun y y' => majAt_add_right' b X v x y y') f s
end PI.Dv.GLP
