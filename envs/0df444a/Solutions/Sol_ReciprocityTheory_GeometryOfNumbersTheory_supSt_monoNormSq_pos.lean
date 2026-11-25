-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.supSt_monoNormSq_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:35.410887+00:00
-- url     : https://prove2.me/submissions/a79e39d9-95c0-4844-a0f7-b4538f97efaa

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
theorem _root_.solution {D : ℕ} (a : Fin (D + 1) → ℕ) : 0 < monoNormSq a := by
  unfold monoNormSq
  have : 0 < ∏ i, (a i).factorial := Finset.prod_pos fun i _ => Nat.factorial_pos _
  have h1 : (0 : ℝ) < ((∏ i, (a i).factorial : ℕ) : ℝ) := by exact_mod_cast this
  positivity
end ReciprocityTheory.GeometryOfNumbersTheory
