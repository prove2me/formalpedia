-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.zero_projector_range_labelledCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:26:34.923998+00:00
-- url     : https://prove2.me/submissions/4ce2e30f-5b7f-455c-91a1-f8579fb8a3fb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_labelledCode_carrier
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_zero_sector_code


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution :
    LinearMap.range (projector S n 0) = (labelledCode S n).carrier := by
  change sector S n 0 = (labelledCode S n).carrier
  rw [zero_sector_code S n, labelledCode_carrier S n]
end QEC.Coding.BDL26CSSHamiltonian
