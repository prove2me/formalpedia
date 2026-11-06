-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.pureOfNonzero_supportedOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:13:08.787478+00:00
-- url     : https://prove2.me/submissions/133649b3-2b65-4a48-b047-8f2f0a031641

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution {C : QuantumCode H} {x : H} (hx : x ≠ 0)
    (hxC : x ∈ C.carrier) : SupportedOn C (pureOfNonzero x hx) := by
  intro y
  rw [pureOfNonzero_apply]
  exact C.carrier.smul_mem _ hxC
end QEC.Semantics.DensityOperator
