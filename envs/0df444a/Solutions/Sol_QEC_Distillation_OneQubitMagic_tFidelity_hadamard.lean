-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.tFidelity_hadamard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:18:54.887559+00:00
-- url     : https://prove2.me/submissions/e6f26d36-2279-4759-bf13-71633be154c1

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tDirectionFidelity_hadamard
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Distillation
namespace OneQubitMagic
open Semantics Semantics.Qubit
private theorem univ_sup'_comp_equiv
    {α : Type*} [Fintype α]
    (reference : α) (f : α → Real) (e : α ≃ α) :
    Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨reference⟩) (f ∘ e) =
      Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨reference⟩) f := by
  simpa only [Finset.map_univ_equiv, Equiv.coe_toEmbedding] using
    Finset.sup'_comp_eq_map
      (s := Finset.univ) (f := e.toEmbedding) f
      (show (Finset.univ : Finset α).Nonempty from
        (Finset.univ_nonempty_iff.mpr ⟨reference⟩))
end OneQubitMagic
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (rho : DensityOperator QubitSpace) :
    tFidelity (hadamardTransport.conjDensity rho) = tFidelity rho := by
  unfold tFidelity
  calc
    _ = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨tReference⟩)
        (tDirectionFidelity (hadamardTransport.conjDensity rho) ∘
          MulAction.toPerm hadamardClifford) :=
      (univ_sup'_comp_equiv tReference
        (tDirectionFidelity (hadamardTransport.conjDensity rho))
        (MulAction.toPerm hadamardClifford)).symm
    _ = _ := by
      simp only [Function.comp_apply, MulAction.toPerm_apply,
        tDirectionFidelity_hadamard]
end QEC.Distillation.OneQubitMagic
