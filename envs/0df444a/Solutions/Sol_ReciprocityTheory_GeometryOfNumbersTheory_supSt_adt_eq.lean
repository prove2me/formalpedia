-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.supSt_adt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:30.52205+00:00
-- url     : https://prove2.me/submissions/bb8651ca-141c-479a-92a8-bb36900d230e

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D n : ℕ) :
    Finset.Nat.antidiagonalTuple (D + 1) n = Finset.piAntidiag Finset.univ n := by
  ext a
  simp [Finset.mem_piAntidiag, Finset.Nat.mem_antidiagonalTuple]
end ReciprocityTheory.GeometryOfNumbersTheory
