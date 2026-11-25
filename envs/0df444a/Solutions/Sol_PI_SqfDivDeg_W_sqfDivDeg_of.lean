-- Prove2me | solution 1 for PI.SqfDivDeg.W.sqfDivDeg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:55.334318+00:00
-- url     : https://prove2.me/submissions/9cdbc726-63e2-4226-b137-9e12cc542cf5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_SqfDivDegOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open PI PI.SqfDivDeg PI.SqfDivDeg.W
namespace PI.SqfDivDeg.W
theorem _root_.solution (hA : RootDense) (hB : MainCount) : PI.SqfDivDeg.Claim := by
  intro g r _ hr hg a ha1 ha2 T hT
  have h1 := hA g a ha1
  have h2 := hA g (r - a) (by omega)
  have h3 := hB g r a (by omega) T hT
  have e : (g : ℝ) ^ r = (g : ℝ) ^ a * (g : ℝ) ^ (r - a) := by
    rw [← pow_add]; congr 1; omega
  have h1' : ((g : ℝ) ^ a) ≤ 2 * ((Rt g a).card : ℝ) := by exact_mod_cast h1
  have h2' : ((g : ℝ) ^ (r - a)) ≤ 2 * ((Rt g (r - a)).card : ℝ) := by exact_mod_cast h2
  have p1 : (0 : ℝ) ≤ (g : ℝ) ^ a := by positivity
  have p2 : (0 : ℝ) ≤ (g : ℝ) ^ (r - a) := by positivity
  have hm : (g : ℝ) ^ a * (g : ℝ) ^ (r - a) ≤
      (2 * ((Rt g a).card : ℝ)) * (2 * ((Rt g (r - a)).card : ℝ)) :=
    mul_le_mul h1' h2' p2 (by linarith)
  rw [e] at h3 ⊢
  nlinarith
end PI.SqfDivDeg.W
