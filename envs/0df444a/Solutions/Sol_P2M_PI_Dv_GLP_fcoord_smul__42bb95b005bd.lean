-- Prove2me | solution 1 for P2M_PI_Dv_GLP_fcoord_smul__42bb95b005bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:19.211586+00:00
-- url     : https://prove2.me/submissions/abe9ada7-ac22-4a30-aaef-70f5be7b31c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_MajAtZeroRight
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
theorem _root_.solution (c : K) (x : V) : fcoord b X v (c • x) = v.embedding c • fcoord b X v x := by
  unfold fcoord vecAt
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp
end PI.Dv.GLP
