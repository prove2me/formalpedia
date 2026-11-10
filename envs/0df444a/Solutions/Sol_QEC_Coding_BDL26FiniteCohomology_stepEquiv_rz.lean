-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.stepEquiv_rz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:31:55.318809+00:00
-- url     : https://prove2.me/submissions/442a0f4e-cc10-44cd-8b29-f94610980c41

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
theorem _root_.solution (S : OddScale) (n : Nat) (h : ¬ n % 2 = 0) :
    stepEquiv S n = BDL26RZCohomology.nextEquiv S n (state S n) h := by
  exact @_root_.dif_neg (n % 2 = 0) (Nat.decEq (n % 2) 0) h
    (H1 S n ≃ₗ[Field] H1 S (n+1))
    (fun hp => BDL26RXCohomology.nextEquiv S n (state S n) hp)
    (fun hn => BDL26RZCohomology.nextEquiv S n (state S n) hn)
end QEC.Coding.BDL26FiniteCohomology
