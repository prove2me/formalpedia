-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.indexed_total_nonconjugacy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:35:19.591237+00:00
-- url     : https://prove2.me/submissions/82ddddf3-1786-4ef5-bbbb-b2ad1088bb17

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_conjugates_total_nonconjugacy


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a b : TorusIndex epsilon) (g : ProjectiveGroup (f epsilon) y) :
    indexedLeft f epsilon y hTwoF hY hOne hTwo a * g ≠
      g * indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo b :=
  conjugates_total_nonconjugacy (f epsilon) y ((map_ne_zero f).mpr hEpsilon)
    hY hOne hTwo _ _ g
end QEC.Coding.ExpanderCodes.QuaternionGenerators
