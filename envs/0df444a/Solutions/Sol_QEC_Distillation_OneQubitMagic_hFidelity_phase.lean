-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hFidelity_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:19:30.577818+00:00
-- url     : https://prove2.me/submissions/a693f6bf-3fd7-4fdb-8216-8d2c7bc5783b

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hDirectionFidelity_phase
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
    hFidelity (phaseTransport.conjDensity rho) = hFidelity rho := by
  unfold hFidelity
  calc
    _ = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨hReference⟩)
        (hDirectionFidelity (phaseTransport.conjDensity rho) ∘
          MulAction.toPerm phaseClifford) :=
      (univ_sup'_comp_equiv hReference
        (hDirectionFidelity (phaseTransport.conjDensity rho))
        (MulAction.toPerm phaseClifford)).symm
    _ = _ := by
      simp only [Function.comp_apply, MulAction.toPerm_apply,
        hDirectionFidelity_phase]
end QEC.Distillation.OneQubitMagic
