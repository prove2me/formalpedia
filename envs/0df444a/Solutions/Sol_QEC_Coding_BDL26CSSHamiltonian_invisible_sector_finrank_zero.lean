-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.invisible_sector_finrank_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:36:07.191439+00:00
-- url     : https://prove2.me/submissions/b7b632e9-88a7-41cf-b0b9-5af9477c5408

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_CSSGibbs_sector_finrank_zero_of_not_realizable


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_e0d1cb1e0b_118
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_e0d1cb1e0b_119
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution
    (s : Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n)))
    (hs : s ∉ visibleRealizable S n) : Module.finrank ℂ (sector S n s) = 0 :=
  CSSGibbs.sector_finrank_zero_of_not_realizable (zSyndrome S n) (xSyndrome S n)
    (row_orthogonal S n) s hs
end QEC.Coding.BDL26CSSHamiltonian
