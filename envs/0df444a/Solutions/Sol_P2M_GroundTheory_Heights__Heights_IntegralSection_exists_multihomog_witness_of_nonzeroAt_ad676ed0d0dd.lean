-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IntegralSection_exists_multihomog_witness_of_nonzeroAt_ad676ed0d0dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:00.654859+00:00
-- url     : https://prove2.me/submissions/254fa557-3fa1-4bb0-824e-de3a519d165f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_map_d62ae25f8d4a
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
variable {Ω : Type*} [Field Ω]
open GroundTheory.Heights₂.Heights.IntegralSection
variable {P : ArithVariety n} {a : ι → ℤ}
namespace GroundTheory.Heights₂.Heights.IntegralSection
theorem _root_.solution (s : IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) (τ : AlgebraicClosure ℚ →+* ℂ)
    {x : Cone n (AlgebraicClosure ℚ)} (hxs : s.NonzeroAt x) :
    ∃ (dg dh : ι → ℕ) (g h : MvPolynomial (Coord n) ℤ),
      Geo.IsMultiHomog (ι := blockIdx n) g dg ∧ Geo.IsMultiHomog (ι := blockIdx n) h dh ∧
      (∀ k, (dg k : ℤ) = dh k + a k) ∧ aeval y g = s.valueAt y * aeval y h ∧
      eval (flatCone fun k i ↦ τ (x k i)) (map (Int.castRingHom ℂ) g) ≠ 0 ∧
      eval (flatCone fun k i ↦ τ (x k i)) (map (Int.castRingHom ℂ) h) ≠ 0 := by
  obtain ⟨c, d, e, hce, hc, he⟩ := hxs
  obtain ⟨δ, hδe, hδ⟩ := hce.1
  refine ⟨δ, d, e, chartMonomial c d, (geoMultiHomog_iff e δ).mpr hδe,
    (geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d),
    fun k ↦ by have := hδ k; omega, s.aeval_chartForm hy hce, ?_, ?_⟩
  · rw [eval_map_flatCone, evalCone_map]
    exact (map_ne_zero τ).mpr he
  · rw [eval_map_flatCone, evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ ((map_ne_zero τ).mpr (hc k))
end GroundTheory.Heights₂.Heights.IntegralSection
