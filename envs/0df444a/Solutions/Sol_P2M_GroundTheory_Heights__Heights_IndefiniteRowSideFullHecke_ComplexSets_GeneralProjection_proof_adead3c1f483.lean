-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GeneralProjection_proof_adead3c1f483
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:32:10.206187+00:00
-- url     : https://prove2.me/submissions/4f9540e7-6295-4c3f-852c-88fee08fc203

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGeneralProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGeneralProjection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_detPoly_db93427849b8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Matrix MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GeneralProjection
theorem _root_.solution : GeneralProjection.Statement := by
  intro n d m L hL
  classical
  set M : Fin m → Matrix (Fin n) (Fin d) ℂ := fun b => LinearMap.toMatrix' (L b) with hM
  have hne : ∀ b, detPoly (M b) ≠ 0 := by
    intro b h
    obtain ⟨g, hg⟩ := (L b).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hL b))
    have h1 : LinearMap.toMatrix' g * M b = 1 := by
      rw [hM]; dsimp only
      rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
    have := congrArg (eval (fun p : Fin d × Fin n => LinearMap.toMatrix' g p.1 p.2)) h
    rw [eval_detPoly, map_zero] at this
    have h2 : Matrix.of (fun i k => LinearMap.toMatrix' g i k) = LinearMap.toMatrix' g := by
      ext i k; rfl
    rw [h2, h1, det_one] at this
    exact one_ne_zero this
  have hprod : (∏ b, detPoly (M b)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun b _ => hne b
  obtain ⟨x, hx⟩ : ∃ x : Fin d × Fin n → ℂ, eval x (∏ b, detPoly (M b)) ≠ 0 := by
    by_contra hcon
    refine hprod (MvPolynomial.funext fun x => ?_)
    rw [map_zero]
    by_contra hx
    exact hcon ⟨x, hx⟩
  refine ⟨Matrix.of fun i k => x (i, k), fun b v w hvw => ?_⟩
  rw [map_prod] at hx
  have hb : (Matrix.of (fun i k => x (i, k)) * M b).det ≠ 0 := by
    rw [← eval_detPoly]
    exact (Finset.prod_ne_zero_iff.mp hx) b (Finset.mem_univ b)
  have key : ∀ u, (Matrix.of fun i k => x (i, k)) *ᵥ L b u = (Matrix.of (fun i k => x (i, k)) * M b) *ᵥ u := by
    intro u
    rw [← Matrix.mulVec_mulVec, hM]
    dsimp only
    rw [LinearMap.toMatrix'_mulVec]
  simp only [key] at hvw
  have h0 : (Matrix.of (fun i k => x (i, k)) * M b) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hb h0)
end GeneralProjection
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
