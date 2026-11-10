-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.sector_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:50:19.921986+00:00
-- url     : https://prove2.me/submissions/a8af8d8f-57e8-4bcc-9121-44bb09442f29

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_sector_realizable_finrank


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (u : LinearMap.range (zSyndrome S n))
    (v : LinearMap.range (xSyndrome S n)) :
    Module.finrank ℂ (sector S n (CSSGibbs.joinSyndrome u.val v.val)) = multiplicity S n :=
  CSSGibbs.sector_realizable_finrank _ _ (row_orthogonal S n) u v
end QEC.Coding.BDL26CSSHamiltonian
