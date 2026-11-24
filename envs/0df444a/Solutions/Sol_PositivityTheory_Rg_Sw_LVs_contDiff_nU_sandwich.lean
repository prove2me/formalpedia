-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.contDiff_nU_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:30.577823+00:00
-- url     : https://prove2.me/submissions/b35d9851-aa03-469f-ace8-d75917f37b4b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (a b : M2 n) : ContDiff ℂ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n :=
    { toFun := fun H => a * fromBlocks 0 H 0 0 * b
      map_add' := fun H H' => by
        have : (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (H + H') 0 0 : M2 n) = fromBlocks 0 H 0 0 + fromBlocks 0 H' 0 0 := by
          rw [Matrix.fromBlocks_add]; simp
        rw [this, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c H => by
        have : (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • H) 0 0 : M2 n) = c • fromBlocks 0 H 0 0 := by
          rw [Matrix.fromBlocks_smul]; simp
        simp only [RingHom.id_apply]
        rw [this, Matrix.mul_smul, Matrix.smul_mul] }
  have h : (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) = fun H => a * b + L.toContinuousLinearMap H := by
    funext H
    have : nU H = 1 + (fromBlocks 0 H 0 0 : M2 n) := by
      rw [nU, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]; simp
    simp only [L, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  rw [h]
  exact contDiff_const.add L.toContinuousLinearMap.contDiff
end PositivityTheory.Rg.Sw.LVs
