-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IntegralSection_nonzeroAt_of_noCommonZero_5dd630099693
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:28:29.437082+00:00
-- url     : https://prove2.me/submissions/5c5ef079-e3ce-431c-a639-1355a70c6618

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_map_103d06bd8f98
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mem_mcPts_iff_497efdbb0f6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_map_d62ae25f8d4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_map_flatCone_f6bc8e6a8518
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e


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
theorem _root_.solution {J : ℕ} (s : Fin J → IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) (τ : AlgebraicClosure ℚ →+* ℂ)
    (h : IndefiniteRowSideFullHecke.HeightsSet.NoCommonZero (ι := blockIdx n) P.ideal y a fun j ↦ (s j).valueAt y) :
    ∀ x ∈ P.points (AlgebraicClosure ℚ), ∃ j, (s j).NonzeroAt x := by
  intro x hx
  have hz := P.mem_points_map τ hx
  obtain ⟨j, dg, dh, g, h, hg, hh, hd, hgh, hg0, -⟩ :=
    h (flatCone fun k i ↦ τ (x k i)) ((P.mem_mcPts_iff _).mpr hz)
  rw [eval_map_flatCone] at hg0
  obtain ⟨c, hc⟩ := exists_chart hx.1
  obtain ⟨d, e, hce⟩ := (s j).regular c (P.X_notMem_of_mem_points hx hc)
  refine ⟨j, c, d, e, hce, hc, fun he0 ↦ ?_⟩
  have hrel := evalCone_rel hz ((s j).sub_mem_of_chartForm hy ((geoMultiHomog_iff g dg).mp hg)
    ((geoMultiHomog_iff h dh).mp hh) hd hgh hce)
  rw [evalCone_map τ x e, he0, map_zero, mul_zero] at hrel
  have hmon : evalCone (fun k i ↦ τ (x k i)) (chartMonomial c d) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ ((map_ne_zero τ).mpr (hc k))
  exact hg0 ((mul_eq_zero.mp hrel).resolve_right hmon)
end GroundTheory.Heights₂.Heights.IntegralSection
