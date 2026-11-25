-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IntegralSection_noCommonZero_of_nonzeroAt_169afa7037c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:10:07.173491+00:00
-- url     : https://prove2.me/submissions/5e560852-f51b-4124-b0d8-86cf713727ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mem_mcPts_iff_497efdbb0f6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_map_flatCone_f6bc8e6a8518


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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace IntegralSection
theorem _root_.solution (hS : NoCommonZeroComplex.Statement)
    {P : ArithVariety n} {a : ι → ℤ} {J : ℕ} (s : Fin J → IntegralSection P a)
    {Ω : Type*} [Field Ω] {y : Coord n → Ω} (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal)
    (h : ∀ x ∈ P.points (AlgebraicClosure ℚ), ∃ j, (s j).NonzeroAt x) :
    IndefiniteRowSideFullHecke.HeightsSet.NoCommonZero (ι := blockIdx n) P.ideal y a fun j ↦ (s j).valueAt y := by
  intro w hw
  have hz := (P.mem_mcPts_iff w).mp hw
  obtain ⟨j, c, d, e, hce, hc, he⟩ := hS ι n P a (Fin J) s h _ hz
  obtain ⟨δ, hδe, hδ⟩ := hce.1
  refine ⟨j, δ, d, e, chartMonomial c d, (geoMultiHomog_iff e δ).mpr hδe,
    (geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d),
    fun k ↦ by have := hδ k; omega, (s j).aeval_chartForm hy hce, ?_, ?_⟩
  · rw [show eval w (map (Int.castRingHom ℂ) e) = evalCone (unflatCone w) e from
      eval_map_flatCone (unflatCone w) e]
    exact he
  · rw [show eval w (map (Int.castRingHom ℂ) (chartMonomial c d)) =
        evalCone (unflatCone w) (chartMonomial c d) from
      eval_map_flatCone (unflatCone w) (chartMonomial c d), evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
end IntegralSection
end GroundTheory.Heights₂.Heights
