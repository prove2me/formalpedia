-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_recR_congr_da8aa240434b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:09.550816+00:00
-- url     : https://prove2.me/submissions/c651284e-79d5-49f0-8d1d-504caae7dd21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_arInt_congr_e67f32b801d7

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
variable {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
omit [∀ k, Fintype (κ k)]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (Geo.MRing κ) → (m : ℕ) → (Fin m → Geo.HermLine κ) → ℝ)
    (P : Ideal (Geo.MRing κ)) {e : ℕ} (L : Fin e → Geo.HermLine κ) (s : Geo.MRing κ)
    {A A' : Geo.HermLine κ} (hh : ∀ z ∈ Geo.mcPts P, A.h z = A'.h z) :
    Geo.recR I P L A s = Geo.recR I P L A' s := by
  unfold Geo.recR
  rw [arInt_congr P s L hh]
end GroundTheory.Heights₂.Heights
