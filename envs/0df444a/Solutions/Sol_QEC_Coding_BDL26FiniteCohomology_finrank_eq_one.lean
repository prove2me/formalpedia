-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.finrank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:48:33.547936+00:00
-- url     : https://prove2.me/submissions/6df3f52a-6db7-4651-ad7e-10da2d786087

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26FiniteCohomology
theorem _root_.solution (S : OddScale) (n : Nat) : Module.finrank Field (H1 S n) = 1 := by
  rw [(finiteH1Equiv S n).finrank_eq]
  exact Module.finrank_self Field
end QEC.Coding.BDL26FiniteCohomology
