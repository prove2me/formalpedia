-- Prove2me | solution 1 for P2M_PI_Dv_GLP_majAt_add_left__5d03aae9c39c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:19.409805+00:00
-- url     : https://prove2.me/submissions/3014a2b5-a722-43c0-a43b-864f5bef824e

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


section
noncomputable section
namespace PI.Dv.GLP
open Formalism.HermitianLatticesTheory NumberField
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)
private theorem fcoord_add_projection_lattices (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  unfold fcoord vecAt
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp
end PI.Dv.GLP
end
end

set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Formalism.HermitianLatticesTheory NumberField
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)
namespace PI.Dv.GLP
theorem _root_.solution (x x' y : V) : majAt b X v (x + x') y = majAt b X v x y + majAt b X v x' y := by
  unfold majAt
  rw [fcoord_add_projection_lattices]
  simp [add_mul, Finset.sum_add_distrib]
end PI.Dv.GLP
