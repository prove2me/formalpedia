-- Prove2me | solution 1 for P2M_UnipMove_herm_smul_left__6f6c7a1bcd4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:59:40.790894+00:00
-- url     : https://prove2.me/submissions/cba93cd6-c623-4d94-aeb3-1ddb9b372232

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_HermSmulLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace UnipMove
theorem _root_.solution {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end UnipMove
