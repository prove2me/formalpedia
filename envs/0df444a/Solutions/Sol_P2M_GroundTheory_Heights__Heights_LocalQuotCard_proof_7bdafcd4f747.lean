-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalQuotCard_proof_7bdafcd4f747
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:44.483547+00:00
-- url     : https://prove2.me/submissions/a2356e2c-ba7d-4bfd-bdb5-452305a2a95c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightLocalQuotCard
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLength
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PLocalQuotCard
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_card_eq_card_residueField_pow_length_9f7daccf84b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SubringPrimeMaximal_proof_6f25c325f70e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_coker_ne_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField IsLocalRing
namespace GroundTheory.Heights₂.Heights
namespace LocalQuotCard
theorem _root_.solution : LocalQuotCard.Statement := by
  intro L _ _ O hft _ m _ f hf
  have : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing ℤ O
  have hO : Ring.KrullDimLE 1 O := Ring.KrullDimLE.mk₁' fun q hq0 hq ↦
    SubringPrimeMaximal.proof L O q hq hq0
  let R := Localization.AtPrime m
  have : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height m R]
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans (Ring.krullDimLE_iff.mp hO)
  have hf' : algebraMap O R f ≠ 0 := by
    intro h
    apply hf
    exact IsLocalization.injective R m.primeCompl_le_nonZeroDivisors (by simpa using h)
  have hspan : Ideal.span {algebraMap O R f} = LinearMap.range (LinearMap.lsmul R R (algebraMap O R f)) := by
    ext z
    simp [Ideal.mem_span_singleton', LinearMap.mem_range, mul_comm]
  have hfin : Module.length R (R ⧸ Ideal.span {algebraMap O R f}) ≠ ⊤ := by
    rw [hspan]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top R hf'
  unfold localQuotLength
  rw [Inter.card_eq_card_residueField_pow_length _ hfin]
  congr 1
  exact Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal m R).toEquiv.symm
end LocalQuotCard
end GroundTheory.Heights₂.Heights
