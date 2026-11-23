-- Prove2me | solution 1 for P2M_PI_Dv_GLP_majAt_smul_right__94911536fc59
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:49.242407+00:00
-- url     : https://prove2.me/submissions/c758cf9d-7199-496d-920f-436592aed7f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_MajAtZeroRight
import Theorems.Thm_P2M_PI_Dv_GLP_fcoord_smul__42bb95b005bd
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Formalism.HermitianLatticesTheory NumberField
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)
namespace PI.Dv.GLP
theorem _root_.solution (c : K) (x y : V) :
    majAt b X v x (c • y) = v.embedding c * majAt b X v x y := by
  unfold majAt
  rw [fcoord_smul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end PI.Dv.GLP
