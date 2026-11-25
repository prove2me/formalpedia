-- Prove2me | solution 1 for UnipMove.final_numerical_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:16.187109+00:00
-- url     : https://prove2.me/submissions/6e5d2b99-bffa-4800-94f8-d3e5062e12a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoNormRelationTamePrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace UnipMove
theorem _root_.solution : UnipotentMoveNumericalInequalities := by
  intro ρ κ hρ hρ1 hκ0 hκ
  set s := ρ / 100 with hs
  set q := (1 - s) / (1 + s) with hqdef
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 / 1000 := by rw [hs]; linarith
  have hq0 : 0 < q := div_pos (by linarith) (by linarith)
  have hq : 998 / 1000 ≤ q := by
    rw [hqdef, le_div_iff₀ (by linarith)]
    linarith
  have hκ' : κ ≤ ρ / 998 :=
    le_trans hκ (div_le_div_of_nonneg_left hρ.le (by norm_num) (by linarith))
  have ha : 3 * κ / q * (1 + s) ≤ ρ / 300 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hq0 (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right hκ' (by linarith : (0 : ℝ) ≤ 1 + s),
      mul_le_mul_of_nonneg_left hq hρ.le]
  have ha0 : 0 ≤ 3 * κ / q * (1 + s) :=
    mul_nonneg (div_nonneg (by linarith) hq0.le) (by linarith)
  have ha1 : 3 * κ / q * (1 + s) ≤ 1 / 3000 := by linarith
  refine ⟨by linarith, by linarith, ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left ha1 hρ.le]
end UnipMove
