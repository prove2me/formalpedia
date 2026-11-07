-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialLinearToPSL_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:43:08.163342+00:00
-- url     : https://prove2.me/submissions/a4ddf805-4928-4cad-9303-792c4b89e482

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Matrix
open scoped commutatorElement
open scoped Pointwise
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (specialLinearToPSL P r level) := by
  intro g
  obtain ⟨s, hs⟩ := g.property
  refine ⟨s, ?_⟩
  apply Subtype.ext
  exact hs
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
