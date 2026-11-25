-- Prove2me | solution 1 for UnipMove.kato_norm_relation_tame_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:18.082652+00:00
-- url     : https://prove2.me/submissions/41e22af3-a4cd-43c6-bc59-8bc74efb67da

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
theorem _root_.solution : KatoClassHeckeEulerFactorRelation := by
  intro r f d rd NA NC ep t hd hrd hNA hep ht ht1
  unfold frameIndexBound
  have hP0 : 0 ≤ (f : ℝ) * ((2 * f * (r - 2) : ℕ) : ℝ) ^ 3 * d * NA :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) 3)) hd) hNA
  have hS : Real.sqrt (NC ^ 2 * rd / (t * ep)) = Real.sqrt (NC ^ 2 * rd / ep) / Real.sqrt t := by
    rw [← Real.sqrt_div' _ ht.le, div_div, mul_comm ep t]
  have htt : t ≤ Real.sqrt t := by
    calc t = Real.sqrt (t ^ 2) := (Real.sqrt_sq ht.le).symm
      _ ≤ Real.sqrt t := Real.sqrt_le_sqrt (by nlinarith)
  refine ⟨?_, mul_nonneg hP0 (Real.sqrt_nonneg _)⟩
  rw [hS]
  exact le_trans (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) ht htt) hP0) (le_of_eq (mul_div_assoc _ _ _).symm)
end UnipMove
