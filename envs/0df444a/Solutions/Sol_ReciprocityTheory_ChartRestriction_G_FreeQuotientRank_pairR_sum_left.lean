-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.pairR_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:01:08.801695+00:00
-- url     : https://prove2.me/submissions/b82a2ac6-105e-4511-93c3-076d7afc1c12

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BetaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BetaPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Finset
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution {f : ℕ} {ι : Type*} (s : Finset ι) (v : Fin f → ℝ) (g : ι → ℝ)
    (w : ι → Fin f → ℝ) : pairR (∑ j ∈ s, g j • w j) v = ∑ j ∈ s, g j * pairR (w j) v := by
  simp only [pairR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
