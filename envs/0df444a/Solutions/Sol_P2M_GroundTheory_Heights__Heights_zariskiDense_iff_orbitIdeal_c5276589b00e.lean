-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_zariskiDense_iff_orbitIdeal_c5276589b00e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:10:28.325731+00:00
-- url     : https://prove2.me/submissions/51017cc2-d314-4ff1-a60e-adf9db6c7301

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_orbitIdeal_iff_of_isWeightedHomogeneous_a8b1cb843d38

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
theorem _root_.solution (P : ArithVariety n) (S : Set (Cone n (AlgebraicClosure ℚ))) :
    P.ZariskiDense S ↔ Geo.IsZariskiDense (ι := blockIdx n) P.ideal (orbitIdeal '' S) := by
  constructor
  · rintro h f ⟨a, ha⟩ hfP
    by_contra hne
    have ha' := (geoMultiHomog_iff f a).mp ha
    refine hfP (h a f ha' fun z hz ↦ ?_)
    refine (mem_orbitIdeal_iff_of_isWeightedHomogeneous z ha').mp ?_
    by_contra hz'
    exact hne ⟨_, ⟨z, hz, rfl⟩, hz'⟩
  · intro h m f hf hvan
    by_contra hfP
    obtain ⟨W, ⟨z, hz, rfl⟩, hfW⟩ := h f ⟨m, (geoMultiHomog_iff f m).mpr hf⟩ hfP
    exact hfW ((mem_orbitIdeal_iff_of_isWeightedHomogeneous z hf).mpr (hvan z hz))
end GroundTheory.Heights₂.Heights
