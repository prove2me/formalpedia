-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_det_eq_zero_of_mulVec_eq_zero_6bd628e3069c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:31:58.664803+00:00
-- url     : https://prove2.me/submissions/d2c5d7a9-e5ed-4314-98d9-2fe3cb08408b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_DetEqZeroOfMulVecEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtComp_apply_7f605f1103e2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtEval_apply_40b5f84f59da
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.analyticAtComp_apply
attribute [local simp] GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.analyticAtEval_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {Q : Type*} [CommRing Q] {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (e β : Fin n → Q) (hA : A *ᵥ e = 0) (h1 : ∑ m, β m * e m = 1) : A.det = 0 := by
  have he : (A.adjugate * A) *ᵥ e = 0 := by
    rw [← Matrix.mulVec_mulVec, hA, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at he
  calc A.det = A.det * ∑ m, β m * e m := by rw [h1, mul_one]
    _ = ∑ m, β m * (A.det * e m) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    _ = 0 := Finset.sum_eq_zero fun m _ => by
      have := congrFun he m
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [this, mul_zero]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
