-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.projectivePrime_eq_alpha_mul_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:34:42.283968+00:00
-- url     : https://prove2.me/submissions/4a40bb30-10ec-49fd-a045-7b85d3ec152a

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    projectivePrime epsilon y hEpsilon hY hOne =
      projectiveAlpha epsilon y hEpsilon * projectiveBase epsilon y hY hOne :=
  (QuotientGroup.mk' _).map_mul _ _
end QEC.Coding.ExpanderCodes.QuaternionGenerators
