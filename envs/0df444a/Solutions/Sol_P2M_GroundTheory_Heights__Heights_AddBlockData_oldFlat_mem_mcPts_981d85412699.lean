-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockData_oldFlat_mem_mcPts_981d85412699
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:40.266525+00:00
-- url     : https://prove2.me/submissions/3f902456-a594-4b03-bb40-f6126a2fa8ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading

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
namespace AddBlockData
theorem _root_.solution {P : ArithVariety n} (D : AddBlockData P) {Ω : Type} [Field Ω]
    (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω) (z : Coord D.extSizes → ℂ)
    (hz : z ∈ Geo.mcPts (ι := blockIdx D.extSizes)
        (Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x'))) :
    D.oldFlat z ∈ Geo.mcPts (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) := by
  refine ⟨fun k ↦ hz.1 (some k), fun f hf ↦ ?_⟩
  have hmem : D.liftOld f ∈ Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x') := by
    have hf0 : Geo.mConeMap (ι := blockIdx n) y f = 0 := RingHom.mem_ker.mp hf
    rw [Geo.mCoordIdeal, RingHom.mem_ker]
    have key : Geo.mConeMap (ι := blockIdx D.extSizes) (D.plusCoord y x') (D.liftOld f) =
        rename some (Geo.mConeMap (ι := blockIdx n) y f) := by
      have h : ((Geo.mConeMap (ι := blockIdx D.extSizes) (D.plusCoord y x')).toRingHom.comp
            (D.liftOld).toRingHom) =
          (rename (R := Ω) (some : ι → Option ι)).toRingHom.comp
            (Geo.mConeMap (ι := blockIdx n) y).toRingHom := by
        refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ ?_)
        simp [Geo.mConeMap, AddBlockData.liftOld, AddBlockData.oldCoord, AddBlockData.plusCoord]
      exact congrArg (fun φ : _ →+* _ ↦ φ f) h
    rw [key, hf0, map_zero]
  have h3 := hz.2 _ hmem
  rw [eval_map] at h3 ⊢
  rw [AddBlockData.liftOld, eval₂_rename] at h3
  exact h3
end AddBlockData
end GroundTheory.Heights₂.Heights
