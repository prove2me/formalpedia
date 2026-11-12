-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.check_rank_sum_plus_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:57:58.252762+00:00
-- url     : https://prove2.me/submissions/865e402b-369c-4b85-9900-98efecf3ce7c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_binary_logical_exponent_one
import Theorems.Thm_QEC_Coding_CSSGibbs_checkRanks_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution :
    CSSGibbs.checkRank (zSyndrome S n) + CSSGibbs.checkRank (xSyndrome S n) + 1 =
      Fintype.card (Physical S n) := by
  have h := binary_logical_exponent_one S n
  have hle := CSSGibbs.checkRanks_le (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)
  omega
end QEC.Coding.BDL26CSSHamiltonian
