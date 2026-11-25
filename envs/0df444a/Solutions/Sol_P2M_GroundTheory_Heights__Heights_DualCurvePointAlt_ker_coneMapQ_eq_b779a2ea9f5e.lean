-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_ker_coneMapQ_eq_b779a2ea9f5e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:05:13.579522+00:00
-- url     : https://prove2.me/submissions/901605bb-a649-4c36-a927-6d4c17d2a1f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualCurvePoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_horizontal_871a820b28bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_comap_ker_coneMapQ_41c250fb05d2
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_comap_strictMono
import Theorems.Thm_ReciprocityTheory_AnForm_R_extQ_spec


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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualCurvePointAlt
variable {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)]
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.DualCurvePointAlt
theorem _root_.solution {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) :
    RingHom.ker (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.coneMapQ y) = ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) := by
  have : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have hint : ∀ m : ℤ, (C m : MRing ι) ∈ mCoordIdeal y → m = 0 := fun m hm => by
    have h : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := hm
    rwa [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from CoordinateConeArithVar.horizontal y,
      Ideal.mem_bot] at h
  obtain ⟨-, hc, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec (mCoordIdeal y) hint
  have hle : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) ≤ RingHom.ker (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.coneMapQ y) :=
    Ideal.map_le_iff_le_comap.mpr (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.comap_ker_coneMapQ y).ge
  refine (eq_of_le_of_not_lt hle fun hlt => ?_).symm
  have h := ReciprocityTheory.AnForm.R.IntegerToRational.comap_strictMono hlt
  simp only [hc, IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.comap_ker_coneMapQ] at h
  exact lt_irrefl _ h
end GroundTheory.Heights₂.Heights.DualCurvePointAlt
