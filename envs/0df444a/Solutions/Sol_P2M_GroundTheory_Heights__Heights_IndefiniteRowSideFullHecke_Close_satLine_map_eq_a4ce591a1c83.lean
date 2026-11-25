-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_satLine_map_eq_a4ce591a1c83
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:31:33.474176+00:00
-- url     : https://prove2.me/submissions/6a9c7af3-ecfc-4703-a8ba-f3cc40dc9563

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_stdLatticeExt_iff_15805c108319

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)
noncomputable section
variable {K : Type} [Field K] [NumberField K] {K' : Type} [Field K'] [NumberField K'] [Algebra K K']
  {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (v : Fin n → 𝓞 K') :
    (satLine v).map (intoField K' n) =
      stdLatticeExt K K' n ⊓
        (Submodule.span K' (Set.range fun _ : Fin 1 ↦ fun j ↦ (v j : K'))).restrictScalars (𝓞 K') := by
  ext x
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem, Set.range_const,
    Submodule.mem_span_singleton, mem_stdLatticeExt_iff, Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨c, hc⟩, rfl⟩
    refine ⟨fun j ↦ RingOfIntegers.isIntegral_coe (y j), c, ?_⟩
    funext j
    simp [intoField, hc j]
  · rintro ⟨hx, c, rfl⟩
    refine ⟨fun j ↦ ⟨c * v j, hx j⟩, ⟨c, fun j ↦ rfl⟩, ?_⟩
    funext j
    rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
