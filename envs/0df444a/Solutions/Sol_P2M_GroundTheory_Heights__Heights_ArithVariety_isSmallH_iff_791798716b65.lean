-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_isSmallH_iff_791798716b65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:53:32.231889+00:00
-- url     : https://prove2.me/submissions/5d330487-c3af-4010-964c-e315704189af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mem_mcPts_iff_497efdbb0f6c
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ArithVariety
theorem _root_.solution {Ω : Type} [Field Ω] {y : Coord n → Ω} (P : ArithVariety n)
    (A : HermLine n) (τ : ℕ) {s : Ω} {t : P.FunField} (hR : P.Reads y (τ • A.deg) s t) :
    Geo.IsSmallH (ι := blockIdx n) P.ideal y A.toGeo τ s ↔ P.IsSmallFor (A.pow τ) t := by
  constructor
  · intro hs p q δp δq hp hq hd hpq z hz
    have hgp := (geoMultiHomog_iff p δp).mpr hp
    have hgq := (geoMultiHomog_iff q δq).mpr hq
    have hd' : ∀ k, (δp k : ℤ) = δq k + (τ • A.deg) k := hd
    have hy := (hR p q δp δq hp hq hd').mpr hpq
    have hzm : flatCone z ∈ Geo.mcPts (ι := blockIdx n) P.ideal := (P.mem_mcPts_iff _).mpr hz
    have := hs δp δq p q (flatCone z) hgp hgq
      (fun k ↦ by have := hd' k; simpa [HermLine.toGeo] using this) hy hzm
    rw [eval_map_flatCone, eval_map_flatCone,
      HermLine.toGeo_h_of_blockNonzero A (show BlockNonzero (unflatCone (flatCone z)) from hz.1)] at this
    simpa [HermLine.pow] using this
  · intro hs δp δq p q z hp hq hd hy hz
    have hp' := (geoMultiHomog_iff p δp).mp hp
    have hq' := (geoMultiHomog_iff q δq).mp hq
    have hd' : ∀ k, (δp k : ℤ) = δq k + (τ • A.deg) k := fun k ↦ by
      have := hd k
      simpa [HermLine.toGeo] using this
    have hF := (hR p q δp δq hp' hq' hd').mp hy
    have hz' := (P.mem_mcPts_iff z).mp hz
    have := hs p q δp δq hp' hq' hd' hF (unflatCone z) hz'
    rw [← eval_map_flatCone, ← eval_map_flatCone] at this
    rw [HermLine.toGeo_h_of_blockNonzero A hz'.1]
    simpa [HermLine.pow] using this
end ArithVariety
end GroundTheory.Heights₂.Heights
