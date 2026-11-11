-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.realizable_projector_trace_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:44:34.291413+00:00
-- url     : https://prove2.me/submissions/ecaa34ce-d383-409f-adaf-93b241e6b7d8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_realizable_sector_finrank_two
import Theorems.Thm_QEC_Coding_CSSGibbs_trace_projector


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (u : LinearMap.range (zSyndrome S n))
    (v : LinearMap.range (xSyndrome S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      (projector S n (CSSGibbs.joinSyndrome u.val v.val)) = (2 : ℂ) := by
  rw [CSSGibbs.trace_projector]
  exact_mod_cast realizable_sector_finrank_two S n u v
end QEC.Coding.BDL26CSSHamiltonian
