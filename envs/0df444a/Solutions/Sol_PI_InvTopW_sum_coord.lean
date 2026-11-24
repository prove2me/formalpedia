-- Prove2me | solution 1 for PI.InvTopW.sum_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:38:46.687025+00:00
-- url     : https://prove2.me/submissions/24fee605-fd60-4424-81f0-b772784bea53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LinearIndependentOneBeta
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
open PI PI.InvTopW
open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
variable (I : AutInst)
namespace PI.InvTopW
theorem _root_.solution (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    ∑ k, coord I k t ⊗ₜ[I.F] basisE I k = t := by
  conv_rhs => rw [← (basisT I).sum_repr t]
  simp [coord, basisT, Module.Basis.coord_apply, Algebra.TensorProduct.basis_apply,
    TensorProduct.smul_tmul']
end PI.InvTopW
