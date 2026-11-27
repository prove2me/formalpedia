-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ImageCoord_proof_ddd24dd5c8df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:09:12.885384+00:00
-- url     : https://prove2.me/submissions/72d701d6-9795-4573-8bb5-79ae173cbf90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ImageCoord
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ImageCoord_mConeMap_rename_db2afe5839e4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Targets
namespace ImageCoord
theorem _root_.solution : ImageCoordStatement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ y hB
  obtain ⟨hκ, -, hv, -⟩ := hB
  ext f
  simp only [imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, ImageCoord.mConeMap_rename κ v hv y f]
  constructor
  · intro h
    exact rename_injective κ hκ (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]
end ImageCoord
end GroundTheory.Heights₂.Heights.Targets
