-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.class_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:56:50.239203+00:00
-- url     : https://prove2.me/submissions/a9cfef9e-09a6-4611-bd4f-d8abbcbdf1f7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_finiteH1Equiv_symm_scalar
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26FiniteCohomology
theorem _root_.solution (S : OddScale) (n : Nat) (v : Cocycle S n) :
    classOf S n v = classOf S n (generator S n (finiteH1Equiv S n (classOf S n v))) := by
  change classOf S n v = classOf S n
    (prefixCocycle S n (finiteH1Equiv S n (classOf S n v) • BDL26SeedCohomology.seedElement))
  rw [← finiteH1Equiv_symm_scalar]
  exact ((finiteH1Equiv S n).symm_apply_apply (classOf S n v)).symm
end QEC.Coding.BDL26FiniteCohomology
