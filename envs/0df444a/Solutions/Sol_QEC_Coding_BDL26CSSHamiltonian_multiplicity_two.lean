-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.multiplicity_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:32:58.717402+00:00
-- url     : https://prove2.me/submissions/c9a56d6e-3e8e-4378-bdea-5794e82c88e7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_zero_sector_finrank_two
import Theorems.Thm_QEC_Coding_CSSGibbs_sector_zero_finrank
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution : multiplicity S n = 2 := by
  have h := CSSGibbs.sector_zero_finrank (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)
  exact h.symm.trans (zero_sector_finrank_two S n)
end QEC.Coding.BDL26CSSHamiltonian
