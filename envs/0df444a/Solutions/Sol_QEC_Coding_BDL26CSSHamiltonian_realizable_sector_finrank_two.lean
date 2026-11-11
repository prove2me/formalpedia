-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.realizable_sector_finrank_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:39:33.057908+00:00
-- url     : https://prove2.me/submissions/f1e4f6fe-2f66-49ff-b148-d4db4e43e2be

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_multiplicity_two
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_sector_multiplicity
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (u : LinearMap.range (zSyndrome S n))
    (v : LinearMap.range (xSyndrome S n)) :
    Module.finrank ℂ (sector S n (CSSGibbs.joinSyndrome u.val v.val)) = 2 :=
  (sector_multiplicity S n u v).trans (multiplicity_two S n)
end QEC.Coding.BDL26CSSHamiltonian
