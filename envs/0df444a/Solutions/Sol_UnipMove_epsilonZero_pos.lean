-- Prove2me | solution 1 for UnipMove.epsilonZero_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:27.029021+00:00
-- url     : https://prove2.me/submissions/15430c17-781b-4f6e-b31a-f3be793d0f30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoNormRelationTamePrime
import Theorems.Thm_UnipMove_fdeg_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
private lemma add_log_add_pos_of_one_le (w f K : ℝ) (hw : 1 ≤ w) (hf : 1 ≤ f) (hK : 1 ≤ K) :
    0 < w + 4 * f * Real.log (2 * K * (4 * f)) + 4 * f + 2 := by
  have hl : 0 ≤ Real.log (2 * K * (4 * f)) := Real.log_nonneg (by nlinarith)
  nlinarith
end
end UnipMove
end

set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace UnipMove
theorem _root_.solution : EpsilonZeroPos E := by
  intro r X c1 w hc1 hw
  have hf : (1 : ℝ) ≤ fdeg E := by exact_mod_cast fdeg_pos
  have hd : 0 < dE E := by
    unfold dE
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
  have hg : (0 : ℝ) < X.g := by exact_mod_cast X.g_pos
  have hNC : (0 : ℝ) < X.NC := by exact_mod_cast X.NC_pos
  dsimp only [flowEpsilonBound]
  refine lt_min one_pos (div_pos (pow_pos (by linarith) 2) ?_)
  refine mul_pos (mul_pos (mul_pos (pow_pos (mul_pos hg (pow_pos hd 2)) 2) (pow_pos hNC 2)) hc1) ?_
  exact add_log_add_pos_of_one_le w _ _ hw hf (le_add_of_nonneg_right (mul_nonneg (by positivity) (by linarith)))
end UnipMove
