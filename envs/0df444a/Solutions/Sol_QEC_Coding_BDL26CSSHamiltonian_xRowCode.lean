-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.xRowCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:01:34.943142+00:00
-- url     : https://prove2.me/submissions/3c2854b8-1290-4ac5-8a7e-030c3dc3873e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26RZMap1CoordinateBridge BDL26LevelTwoDecoder
open PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution : parityCheckRowCode (xSyndrome S n) = (complex S n).firstCoboundaryCheckCode := by
  rw [xSyndrome_matrix]
  rfl
end QEC.Coding.BDL26CSSHamiltonian
