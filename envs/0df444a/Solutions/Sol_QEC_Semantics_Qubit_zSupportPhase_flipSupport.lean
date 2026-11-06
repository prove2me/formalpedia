-- Prove2me | solution 1 for QEC.Semantics.Qubit.zSupportPhase_flipSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:28:10.417272+00:00
-- url     : https://prove2.me/submissions/5b3efcd9-e64d-47c9-84c1-5ea1a2e59375

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace QEC.Semantics.Qubit
theorem _root_.solution (xSupport zSupport : Finset ι)
    (bits : Bitstring ι) :
    zSupportPhase zSupport (flipSupport xSupport bits) =
      supportPhaseSign xSupport zSupport * zSupportPhase zSupport bits := by
  simp only [zSupportPhase, supportPhaseSign]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hix : i ∈ xSupport
  · simp [flipSupport, hix]
  · simp [flipSupport, hix]
end QEC.Semantics.Qubit
