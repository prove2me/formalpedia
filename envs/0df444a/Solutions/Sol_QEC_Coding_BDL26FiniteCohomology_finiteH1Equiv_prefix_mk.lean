-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.finiteH1Equiv_prefix_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:50:13.683734+00:00
-- url     : https://prove2.me/submissions/c973fbd9-182f-4f32-974d-731add63e091

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_prefixEquiv_mk
import Theorems.Thm_QEC_Coding_BDL26SeedCohomology_stateZeroEquivalence_classOf
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.BDL26SeedCohomology.stateZeroEquivalence_classOf



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26FiniteCohomology
theorem _root_.solution (S : OddScale) (n : Nat) (w : Cocycle S 0) :
    finiteH1Equiv S n (classOf S n (prefixCocycle S n w)) =
      BDL26SeedCohomology.coefficient w.1 := by
  rw [← prefixEquiv_mk]
  change BDL26SeedCohomology.stateZeroEquivalence S
    ((prefixEquiv S n).symm (prefixEquiv S n (classOf S 0 w))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact BDL26SeedCohomology.stateZeroEquivalence_classOf S w
end QEC.Coding.BDL26FiniteCohomology
