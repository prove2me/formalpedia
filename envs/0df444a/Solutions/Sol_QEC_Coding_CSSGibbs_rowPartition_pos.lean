-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.rowPartition_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:27:52.55927+00:00
-- url     : https://prove2.me/submissions/01d4dba5-710d-4c6f-8586-18a528e44b5a

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
theorem _root_.solution (t : ℝ) : 0 < rowPartition P t := by
  apply Finset.sum_pos
  · intro u _; exact Real.exp_pos _
  · exact Finset.univ_nonempty
end QEC.Coding.CSSGibbs
