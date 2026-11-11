-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.cohomology_finrank_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:30:59.118149+00:00
-- url     : https://prove2.me/submissions/67350a80-c812-4a09-a0a4-e25be1ab4e5a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_finrank_eq_one
import Theorems.Thm_QEC_Coding_BDL26SeedCohomology_finrank_eq_one


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution :
    Module.finrank (ZMod 2) (complex S n).middleCohomology = 1 :=
  BDL26FiniteCohomology.finrank_eq_one S n
end QEC.Coding.BDL26CSSHamiltonian
