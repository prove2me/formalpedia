-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BallQuotLen.length_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:37:16.411736+00:00
-- url     : https://prove2.me/submissions/1e2d661d-acac-420b-830b-62f9d7152719

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_fdeg_eq_inertiaDeg


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
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}
set_option synthInstance.maxHeartbeats 400000
namespace PI.UnitaryGroupMassFormula.BallQuotLen
theorem _root_.solution (hfin : Module.Finite O ↥(As O A)) (ζ : Pts O A) :
    Module.length O (↥(As O A) ⧸ ζ.asIdeal) = (fdeg ζ : ℕ∞) := by
  classical
  haveI : ζ.asIdeal.IsMaximal := ζ.isMaximal
  haveI : Algebra.IsIntegral O ↥(As O A) := Algebra.IsIntegral.of_finite O _
  have hmax : (ζ.asIdeal.comap (algebraMap O ↥(As O A))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ζ.asIdeal
  have hp : ζ.asIdeal.comap (algebraMap O ↥(As O A)) = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal hmax
  haveI : ζ.asIdeal.LiesOver (IsLocalRing.maximalIdeal O) := ⟨hp.symm⟩
  have hf : fdeg ζ = Module.finrank (O ⧸ IsLocalRing.maximalIdeal O) (↥(As O A) ⧸ ζ.asIdeal) := by
    rw [fdeg_eq_inertiaDeg, ← Ideal.inertiaDeg'_eq_inertiaDeg (IsLocalRing.maximalIdeal O) ζ.asIdeal,
      Ideal.inertiaDeg_algebraMap]
  letI : Field (O ⧸ IsLocalRing.maximalIdeal O) := Ideal.Quotient.field _
  haveI : Module.Finite O (↥(As O A) ⧸ ζ.asIdeal) :=
    Module.Finite.of_surjective ((ζ.asIdeal.restrictScalars O).mkQ) (Submodule.mkQ_surjective _)
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (↥(As O A) ⧸ ζ.asIdeal) :=
    Module.Finite.of_restrictScalars_finite O _ _
  let b := Module.finBasis (O ⧸ IsLocalRing.maximalIdeal O) (↥(As O A) ⧸ ζ.asIdeal)
  let eqv := b.equivFun.restrictScalars O
  have h1 : Module.length O (O ⧸ IsLocalRing.maximalIdeal O) = 1 :=
    Module.length_eq_one_iff.mpr (isSimpleModule_iff_isCoatom.mpr
      (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal O)))
  rw [hf, eqv.length_eq, Module.length_pi, h1, mul_one, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
end PI.UnitaryGroupMassFormula.BallQuotLen
