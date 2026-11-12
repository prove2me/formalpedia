-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.projector_realizable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:49:51.258193+00:00
-- url     : https://prove2.me/submissions/682abc76-5322-4943-a6b3-a9b7b83b385a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_mem_realizableSyndromes_iff
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_ne_zero_iff


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (s : Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n))) :
    projector S n s ≠ 0 ↔
      (fun z => s (.inl z)) ∈ LinearMap.range (zSyndrome S n) ∧
      (fun x => s (.inr x)) ∈ LinearMap.range (xSyndrome S n) := by
  rw [CSSGibbs.projector_ne_zero_iff, CSSGibbs.mem_realizableSyndromes_iff]
end QEC.Coding.BDL26CSSHamiltonian
