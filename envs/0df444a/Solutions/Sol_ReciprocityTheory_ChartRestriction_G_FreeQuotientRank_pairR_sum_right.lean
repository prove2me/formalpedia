-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.pairR_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:01:13.493418+00:00
-- url     : https://prove2.me/submissions/3e74512b-0d28-4a1e-b03e-52a7fe786509

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
    (w : ι → Fin f → ℝ) : pairR v (∑ j ∈ s, g j • w j) = ∑ j ∈ s, g j * pairR v (w j) := by
  simp only [pairR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
