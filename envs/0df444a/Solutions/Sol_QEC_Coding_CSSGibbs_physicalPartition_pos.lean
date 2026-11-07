-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.physicalPartition_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:38:20.759233+00:00
-- url     : https://prove2.me/submissions/fc22f598-5a1c-43ec-b094-1d44d6f2e1ce

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs

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
theorem _root_.solution (β : ℝ) : 0 < physicalPartition P Q β := by
  letI : Nonempty (Fin (Module.finrank ℂ (Qubit.QubitRegister ι))) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  exact gibbsPartitionFunction_pos _ _
end QEC.Coding.CSSGibbs
