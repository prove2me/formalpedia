-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.physicalPartition_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:40:34.305027+00:00
-- url     : https://prove2.me/submissions/6f352c33-9780-41d4-817d-bdc0dc444b4f

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric
import Theorems.Thm_QEC_Semantics_Davies_gibbsPartitionFunction_eq_trace_exp


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics Semantics.Davies Semantics.ThermalEncoding
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_28fb820634_14
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_28fb820634_15
namespace QEC.Coding.CSSGibbs
theorem _root_.solution (β : ℝ) :
    (physicalPartition P Q β : ℂ) =
      LinearMap.trace ℂ (Qubit.QubitRegister ι) (thermalExponential P Q β) := by
  letI : Nonempty (Fin (Module.finrank ℂ (Qubit.QubitRegister ι))) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  apply gibbsPartitionFunction_eq_trace_exp
  intro i
  exact (hamiltonian_symmetric P Q).apply_eigenvectorBasis rfl i
end QEC.Coding.CSSGibbs
