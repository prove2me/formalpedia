-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.finiteH1Equiv_symm_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:56:02.273788+00:00
-- url     : https://prove2.me/submissions/1095310c-7e23-4d88-8e76-9bc7f83e076e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_prefixEquiv_mk
import Theorems.Thm_QEC_Coding_BDL26SeedCohomology_equivalence_symm_apply
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.BDL26SeedCohomology.equivalence_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26FiniteCohomology
theorem _root_.solution (S : OddScale) (n : Nat) (c : Field) :
    (finiteH1Equiv S n).symm c = classOf S n
      (prefixCocycle S n (c • BDL26SeedCohomology.seedElement)) := by
  change prefixEquiv S n (BDL26SeedCohomology.equivalence.symm c) = _
  rw [BDL26SeedCohomology.equivalence_symm_apply]
  exact prefixEquiv_mk S n _
end QEC.Coding.BDL26FiniteCohomology
