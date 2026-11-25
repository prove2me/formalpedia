-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_of_homog_159b62054b52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:04.351491+00:00
-- url     : https://prove2.me/submissions/bb83fb5a-4064-4896-aecc-0ef6c19457ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval__scale_of_isWeightedHomogeneous_6a2760d9d5f2


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
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockBridge
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.AddBlockBridge
theorem _root_.solution (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    coneHom y f = constMap ι (aeval y f) * ∏ k, varT k ^ δ k := by
  have h1 : Geo.mConeMap (ι := blockIdx n) y f =
      eval₂ (Int.castRingHom (MvPolynomial ι Ω)) (fun v : Coord n ↦ X v.1 * C (y v)) f := by
    simp only [Geo.mConeMap, aeval_def]
    congr 1
    funext v
    exact mul_comm _ _
  have h2 : (C (aeval y f) : MvPolynomial ι Ω) =
      eval₂ (Int.castRingHom (MvPolynomial ι Ω)) (fun v : Coord n ↦ C (y v)) f := by
    rw [aeval_def, algebraMap_int_eq, eval₂_comp_left]
    congr 1
  rw [coneHom_apply, h1, eval₂_scale_of_isWeightedHomogeneous (fun k ↦ (X k : MvPolynomial ι Ω)) _ hf, ← h2,
    mul_comm, map_mul, map_prod]
  simp only [map_pow]
  rfl
end GroundTheory.Heights₂.Heights.AddBlockBridge
