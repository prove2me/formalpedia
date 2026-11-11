-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.normalizer_commutes_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:53:12.277125+00:00
-- url     : https://prove2.me/submissions/b460a00a-d317-442f-b22a-f2cedea608dd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_check_hermitian
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_commute_of_commutes
attribute [local simp] QEC.Coding.BDL26CSSHamiltonian.check_hermitian



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution (E : Binary (Physical S m))
    (hE : (stabilizer S m).InBinaryNormalizer E) (j : Sum (ZLabel S m) (XLabel S m)) :
    Commute (toHermitianQubitOperator E) (toQubitOperator (check S m j)) := by
  have hj : check S m j ∈ (stabilizer S m).stabilizers :=
    binaryCSSParityCheckGenerator_mem_checkSet (zSyndrome S m) (xSyndrome S m) j
  have hc := hE _ (PauliSymplectic.mem_generatedGroup_of_mem_stabilizers (stabilizer S m) hj)
  have hop := toHermitianQubitOperator_commute_of_commutes E (check S m j) hc
  rw [check_hermitian S m j] at hop
  show toHermitianQubitOperator E * toQubitOperator (check S m j) =
    toQubitOperator (check S m j) * toHermitianQubitOperator E
  exact hop
end QEC.Coding.BDL26BareLogicalPair
