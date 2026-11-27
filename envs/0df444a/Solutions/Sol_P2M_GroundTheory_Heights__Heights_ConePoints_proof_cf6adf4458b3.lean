-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConePoints_proof_cf6adf4458b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:03.178923+00:00
-- url     : https://prove2.me/submissions/06b17e9f-f155-4ad3-8a08-b434b4cb2e23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExtMapLiftOldOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_liftOld_of_isWeightedHomogeneous_026a3ff1a179
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_evalCone_liftOld_8b80660869f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_liftOld_mem_extIdeal_ea5e70b5cf5c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_IsFormSystem_cross_mem_96329951ee1e

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open AddBlockData
namespace GroundTheory.Heights₂.Heights
namespace ConePoints
theorem _root_.solution (hV : ChartVanishing.Statement) : ConePoints.Statement := by
  intro ι _ _ n P D d g hg
  have hom : ∀ c j, IsWeightedHomogeneous (coordDeg n) (g c j) (fun k ↦ (d k + D.deg k).toNat) := by
    intro c j
    obtain ⟨δ, hδ, hδk⟩ := hg.homog c j
    convert hδ using 1
    funext k
    rw [← hδk k, Int.toNat_natCast]
  have hX : ∀ i, D.extMap (X (D.newCoord i)) = C (D.elt i) * X none := fun i ↦ by
    simp [extMap, newCoord, extVal]
  have part1 : ∀ (c : (k : ι) → Fin (n k + 1)) (i j : Fin (D.size + 1)),
      D.liftOld (g c j) * X (D.newCoord i) - D.liftOld (g c i) * X (D.newCoord j) ∈ D.extIdeal := by
    intro c i j
    rw [extIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, hX, hX,
      D.extMap_liftOld_of_isWeightedHomogeneous (hom c j), D.extMap_liftOld_of_isWeightedHomogeneous (hom c i)]
    by_cases hc : P.IsLive c
    · rw [hg.value c hc j, hg.value c hc i]
      simp only [map_mul]
      ring
    · rw [hg.dead c hc j, hg.dead c hc i]
      simp
  refine ⟨part1, fun w hw ↦ ?_⟩
  set z := D.basePart₂ w with hz
  set z' := D.newPart w with hz'
  have hzP : z ∈ P.points ℂ :=
    ⟨fun k ↦ hw.1 (some k), fun f hf ↦ by
      rw [← D.evalCone_liftOld]
      exact hw.2 _ (D.liftOld_mem_extIdeal hf)⟩

  have rel : ∀ c i j, evalCone z (g c j) * z' i = evalCone z (g c i) * z' j := by
    intro c i j
    have h := hw.2 _ (part1 c i j)
    unfold evalCone at h
    rw [eval₂_sub, eval₂_mul, eval₂_mul, eval₂_X, eval₂_X] at h
    change evalCone w (D.liftOld (g c j)) * _ - evalCone w (D.liftOld (g c i)) * _ = 0 at h
    rw [evalCone_liftOld, evalCone_liftOld] at h
    rw [← sub_eq_zero]
    exact h

  have cross : ∀ c c' j, evalCone z (chartMonomial c' d) * evalCone z (g c j) =
      evalCone z (chartMonomial c d) * evalCone z (g c' j) := by
    intro c c' j
    have h := hzP.2 _ (hg.cross_mem D c c' j)
    rw [← sub_eq_zero]
    simpa [evalCone] using h

  have hne : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hzP.1 k)
  choose c₀ hc₀ using hne
  have hm₀ : evalCone z (chartMonomial c₀ d) ≠ 0 := by
    simp only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc₀ k)
  obtain ⟨j₀, hj₀⟩ : ∃ j, evalCone z (g c₀ j) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hm₀ ((hV ι n P D d g hg z hzP c₀).mp h)
  have hz'₀ : z' j₀ ≠ 0 := by
    intro h0
    apply hw.1 none
    funext i
    have := rel c₀ i j₀
    rw [h0, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hj₀
  refine ⟨hzP, z' j₀ * evalCone z (chartMonomial c₀ d) / evalCone z (g c₀ j₀),
    div_ne_zero (mul_ne_zero hz'₀ hm₀) hj₀, fun c hc j ↦ ?_⟩
  rw [eq_div_iff hc, div_mul_eq_mul_div, eq_div_iff hj₀]
  linear_combination evalCone z (chartMonomial c d) * rel c₀ j j₀ - z' j₀ * cross c c₀ j
end ConePoints
end GroundTheory.Heights₂.Heights
