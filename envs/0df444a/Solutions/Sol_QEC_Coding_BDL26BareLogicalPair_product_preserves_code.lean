-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.product_preserves_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:35:33.622411+00:00
-- url     : https://prove2.me/submissions/b93b291f-105f-4abe-b963-2ff0f16b4e2f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Xbar_preserves_code
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Zbar_preserves_code

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution (ψ : Qubit.QubitRegister (Physical S m))
    (hψ : ψ ∈ (labelledCode S m).carrier) : (Xbar S m * Zbar S m) ψ ∈ (labelledCode S m).carrier := by
  exact Xbar_preserves_code S m _ (Zbar_preserves_code S m ψ hψ)
end QEC.Coding.BDL26BareLogicalPair
