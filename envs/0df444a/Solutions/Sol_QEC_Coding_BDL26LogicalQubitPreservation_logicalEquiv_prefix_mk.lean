-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.logicalEquiv_prefix_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:45:44.880979+00:00
-- url     : https://prove2.me/submissions/10622b59-6b87-4d75-9a00-335ff6514f67

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalEquiv_mk
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_finiteH1Equiv_prefix_mk
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (n : Nat)
    (w : BDL26FiniteCohomology.Cocycle S 0) :
    logicalEquiv S n (logicalClass S n (prefixRepresentative S n w)) =
      BDL26SeedCohomology.coefficient w.1 := by
  rw [logicalEquiv_mk]
  change BDL26FiniteCohomology.finiteH1Equiv S n
    (BDL26FiniteCohomology.classOf S n
      (cocycleEquiv S n ((cocycleEquiv S n).symm
        (BDL26FiniteCohomology.prefixCocycle S n w)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact BDL26FiniteCohomology.finiteH1Equiv_prefix_mk S n w
end QEC.Coding.BDL26LogicalQubitPreservation
