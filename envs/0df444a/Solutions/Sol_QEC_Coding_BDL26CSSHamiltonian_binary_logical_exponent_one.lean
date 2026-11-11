-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.binary_logical_exponent_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:44:20.093497+00:00
-- url     : https://prove2.me/submissions/ad0fe378-3dfb-4f4c-a452-0b139425f209

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_homology_finrank_one
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_xRowCode
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_zRowCode
import Theorems.Thm_QEC_Coding_CSSGibbs_checkRank_eq_rowDimension
import Theorems.Thm_QEC_Coding_ChainComplexData_length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution :
    Fintype.card (Physical S n) - CSSGibbs.checkRank (zSyndrome S n) -
      CSSGibbs.checkRank (xSyndrome S n) = 1 := by
  have h := (complex S n).length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology
  rw [homology_finrank_one S n] at h
  have hz := CSSGibbs.checkRank_eq_rowDimension (zSyndrome S n)
  have hx := CSSGibbs.checkRank_eq_rowDimension (xSyndrome S n)
  rw [zRowCode S n] at hz
  rw [xRowCode S n] at hx
  change Fintype.card (Physical S n) - Dimension (complex S n).firstCoboundaryCheckCode -
    Dimension (complex S n).middleBoundaryCode = 1 at h
  omega
end QEC.Coding.BDL26CSSHamiltonian
