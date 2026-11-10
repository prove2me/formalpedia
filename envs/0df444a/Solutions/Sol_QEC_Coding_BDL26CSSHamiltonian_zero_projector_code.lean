-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.zero_projector_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:49:32.714143+00:00
-- url     : https://prove2.me/submissions/e04b1a55-c64f-4a66-83ca-83f2a0894f38

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_zero_sector_code
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_square
attribute [local simp] QEC.Coding.CSSGibbs.projector_square



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (v : Qubit.QubitRegister (Physical S n)) :
    projector S n 0 v = v ↔ v ∈ (complex S n).binaryCSSCode.stabilizer.code.carrier := by
  rw [← zero_sector_code]
  constructor
  · intro h; exact ⟨v, h⟩
  · rintro ⟨w, rfl⟩
    exact congrArg (fun A : Operator (Qubit.QubitRegister (Physical S n)) => A w)
      (CSSGibbs.projector_square _ _ (row_orthogonal S n) 0)
end QEC.Coding.BDL26CSSHamiltonian
