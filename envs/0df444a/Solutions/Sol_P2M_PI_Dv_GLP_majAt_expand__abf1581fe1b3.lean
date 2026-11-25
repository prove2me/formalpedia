-- Prove2me | solution 1 for P2M_PI_Dv_GLP_majAt_expand__abf1581fe1b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:55:31.870287+00:00
-- url     : https://prove2.me/submissions/ca30ba76-c9df-4b45-b6df-d1b8b3b513e3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_MajAtZeroRight
import Theorems.Thm_P2M_PI_Dv_GLP_majAt_add_left__5d03aae9c39c
import Theorems.Thm_P2M_PI_Dv_GLP_majAt_add_right__f7ddb772f55e
import Theorems.Thm_P2M_PI_Dv_GLP_majAt_smul_left__f0d32a8c4a2c
import Theorems.Thm_P2M_PI_Dv_GLP_majAt_smul_right__94911536fc59
import Theorems.Thm_P2M_PI_Dv_GLP_majAt_swap__72bde34d257d
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
theorem _root_.solution (c : K) (u w : V) :
    majAt b X v (u + c • w) (u + c • w) = majAt b X v u u + v.embedding c * majAt b X v u w +
      star (v.embedding c) * star (majAt b X v u w) +
      star (v.embedding c) * v.embedding c * majAt b X v w w := by
  simp only [majAt_add_left', majAt_add_right', majAt_smul_left', majAt_smul_right']
  rw [majAt_swap' b X v u w]
  ring
end PI.Dv.GLP
