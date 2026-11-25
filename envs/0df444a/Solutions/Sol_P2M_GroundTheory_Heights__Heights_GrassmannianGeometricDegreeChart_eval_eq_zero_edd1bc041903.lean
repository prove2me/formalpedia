-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_eval_eq_zero_edd1bc041903
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:41.502007+00:00
-- url     : https://prove2.me/submissions/51512172-399c-4e65-898d-b35638f03a46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassGeomDegChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_rootCoord_mul_6501e396c8a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassLeRoot_proof_b73533a30168


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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
theorem _root_.solution {g : MRing (plBlocks 1 1 n)} (hg : g ∈ grassIdeal 1 1 n) (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) :
    MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) = 0 := by
  have key : ∀ z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ, z a0 ≠ 0 →
      MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) = 0 := by
    intro z hz
    have h0 : mConeMap (rootCoord (chartPt z)) g = 0 := GrassLeRoot.proof 1 1 n _ hg
    have h1 := congrArg ((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ) h0
    rw [map_zero, mConeMap] at h1
    rw [show ((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ)
        ((MvPolynomial.aeval fun p => MvPolynomial.C (rootCoord (chartPt z) p) * MvPolynomial.X p.1) g) =
        (((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ).comp
          (MvPolynomial.aeval fun p => MvPolynomial.C (rootCoord (chartPt z) p) * MvPolynomial.X p.1)) g from rfl,
      MvPolynomial.comp_aeval] at h1
    simp only [AlgHom.restrictScalars_apply, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply] at h1
    rw [rootCoord_mul z hz] at h1
    rw [MvPolynomial.eval_map, ← h1, MvPolynomial.aeval_def]
    rfl
  have hq : MvPolynomial.map (Int.castRingHom ℂ) g * MvPolynomial.X a0 = 0 := by
    apply MvPolynomial.funext
    intro z
    rw [map_mul, MvPolynomial.eval_X, map_zero]
    by_cases hz : z a0 = 0
    · rw [hz, mul_zero]
    · rw [key z hz, zero_mul]
  rcases mul_eq_zero.mp hq with h | h
  · rw [h, map_zero]
  · exact absurd h (MvPolynomial.X_ne_zero a0)
end GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
