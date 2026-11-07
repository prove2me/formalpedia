-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantPolynomialEval_map_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:49:41.976875+00:00
-- url     : https://prove2.me/submissions/846519b4-834f-4cfc-b464-e3f218bd1b04

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : PolynomialRing P) :
    indexConstantPolynomialEval P r level
        (Polynomial.map (algebraMap (BaseField P)
          (ConstantExtension P r)) f) =
      indexPolynomialEval P r level f := by
  change Polynomial.eval₂
      (indexConstantEmbedding P r level).toRingHom
      (indexPlaceY P r level)
      (Polynomial.map (algebraMap (BaseField P)
        (ConstantExtension P r)) f) =
    Polynomial.eval₂ (algebraMap (BaseField P)
      (ResidueField P r level)) (indexPlaceY P r level) f
  rw [Polynomial.eval₂_map]
  congr 1
  ext a
  exact (indexConstantEmbedding P r level).commutes a
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
