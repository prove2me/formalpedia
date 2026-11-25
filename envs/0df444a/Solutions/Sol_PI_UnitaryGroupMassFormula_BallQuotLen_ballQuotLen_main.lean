-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BallQuotLen.ballQuotLen_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:58.377839+00:00
-- url     : https://prove2.me/submissions/f919f7de-e34e-4743-9b58-77080f07e5ee

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg
import Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_length_ball_quotient_eq_sum_mul_fdeg
import Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_finite_pts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BallQuotLen
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
namespace PI.UnitaryGroupMassFormula.BallQuotLen
theorem _root_.solution : PI.BallQuotLen := by
  intro O _ _ _ K _ _ _ A _ _ _ _ _ _ ϖ hϖ hfin _ V _ _ _ _ _ _ e he c m
  classical
  haveI : Module.Finite O ↥(As O A) := hfin
  haveI : Finite (Pts O A) := PI.UnitaryGroupMassFormula.EfRankSum.finite_pts O A
  letI : Fintype (Pts O A) := Fintype.ofFinite _
  have h : IsUnif A ϖ := by
    refine ⟨hϖ, ?_, ?_⟩
    · rw [IsScalarTower.algebraMap_apply O K A]
      refine IsUnit.map _ (isUnit_iff_ne_zero.mpr ?_)
      intro h0
      exact hϖ.ne_zero ((IsFractionRing.injective O K) (h0.trans (map_zero _).symm))
    · intro x
      have halg : IsAlgebraic O x :=
        (IsFractionRing.isAlgebraic_iff O K A).mpr (Algebra.IsAlgebraic.isAlgebraic x)
      obtain ⟨y, hy0, hyx⟩ := halg.exists_integral_multiple
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
      refine ⟨k, ?_⟩
      have e1 : ϖ ^ k • x = ((u⁻¹ : Oˣ) : O) • (((u : O) * ϖ ^ k) • x) := by
        rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul]
      rw [e1]
      exact IsIntegral.smul _ hyx
  rw [finsum_eq_sum_of_fintype]
  exact length_ball_quotient_eq_sum_mul_fdeg K h hfin he (∑ ζ, m ζ) c m rfl
end PI.UnitaryGroupMassFormula.BallQuotLen
