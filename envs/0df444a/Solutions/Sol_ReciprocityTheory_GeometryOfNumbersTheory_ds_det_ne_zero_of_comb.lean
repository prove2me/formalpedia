-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.ds_det_ne_zero_of_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:02:00.519154+00:00
-- url     : https://prove2.me/submissions/722b692a-1602-44d1-a57b-e9f3af2d5351

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {r : ℕ} {v : Fin r → V} (g : Matrix (Fin r) (Fin r) (𝓞 K))
    (hv' : LinearIndependent K (fun j => ∑ i, g i j • v i)) : g.det ≠ 0 := by
  classical
  intro hdet
  have hG : (g.map (algebraMap (𝓞 K) K)).det = 0 := by
    have h1 := RingHom.map_det (algebraMap (𝓞 K) K) g
    rw [hdet, map_zero] at h1
    exact h1.symm
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hG
  apply hc0
  have hconv : (fun j => ∑ i, g i j • v i) =
      fun j => ∑ i, (g.map (algebraMap (𝓞 K) K)) i j • v i := by
    funext j
    simp only [Matrix.map_apply, algebraMap_smul]
  rw [hconv] at hv'
  have hsum : ∑ j, c j • ∑ i, (g.map (algebraMap (𝓞 K) K)) i j • v i =
      ∑ i, ((g.map (algebraMap (𝓞 K) K)).mulVec c) i • v i := by
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  rw [hc] at hsum
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hsum
  funext j
  exact Fintype.linearIndependent_iff.1 hv' c hsum j
end ReciprocityTheory.GeometryOfNumbersTheory
