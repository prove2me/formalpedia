-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_det_mem_projIdeal_b567b3689f49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:48:05.618126+00:00
-- url     : https://prove2.me/submissions/d2744606-5716-408a-bda6-036a010eb058

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_joinBlock_sepBlock_1ead804a3c0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_mem_offMonos_089e7d3164ba

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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution (P : ArithVariety n) (k₀ : ι) (D : ℕ)
    (q : offMonos n k₀ D → MvPolynomial (Coord n) ℤ) (hq : ∀ i, q i ∈ homogIn n P k₀ D) :
    (Matrix.of fun i (μ : offMonos n k₀ D) ↦ coeff μ.1 (sepBlock k₀ (q i))).det ∈ P.projIdeal k₀ := by
  classical
  let Bm : Matrix (offMonos n k₀ D) (offMonos n k₀ D) (BlockRing n k₀) := Matrix.of fun i μ ↦ coeff μ.1 (sepBlock k₀ (q i))
  have hsupp : ∀ i, (sepBlock k₀ (q i)).support ⊆ offMonos n k₀ D := fun i ν hν ↦
    mem_offMonos.mpr ((hq i).2 (MvPolynomial.mem_support_iff.mp hν))
  have hexp : ∀ i, q i = ∑ μ : offMonos n k₀ D, rename (blockIncl k₀) (Bm i μ) * monomial μ.1 1 := by
    intro i
    conv_lhs => rw [← joinBlock_sepBlock k₀ (q i), (sepBlock k₀ (q i)).as_sum, map_sum]
    rw [Finset.sum_subset (hsupp i) ?_, ← Finset.sum_coe_sort (offMonos n k₀ D)]
    · refine Finset.sum_congr rfl fun μ _ ↦ ?_
      rw [joinBlock, coe_eval₂Hom, eval₂_monomial, monomial_eq, C_1, one_mul]
      rfl
    · intro ν _ hν
      rw [notMem_support_iff.mp hν, monomial_zero, map_zero]
  let f : BlockRing n k₀ →+* MvPolynomial (Coord n) ℤ := (rename (blockIncl (n := n) k₀)).toRingHom
  let rB : Matrix (offMonos n k₀ D) (offMonos n k₀ D) (MvPolynomial (Coord n) ℤ) := f.mapMatrix Bm
  let xv : offMonos n k₀ D → MvPolynomial (Coord n) ℤ := fun μ ↦ monomial μ.1 1
  have hmv : Matrix.mulVec rB xv = q := by
    funext i
    rw [hexp i]
    simp [rB, xv, f, Matrix.mulVec, dotProduct]
  have hcr : ∀ μ : offMonos n k₀ D, rB.det * xv μ ∈ P.ideal := by
    intro μ
    have h1 : Matrix.mulVec rB.adjugate (Matrix.mulVec rB xv) = rB.det • xv := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 := congrFun h1 μ
    rw [hmv, Pi.smul_apply, smul_eq_mul] at h2
    rw [← h2]
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ ↦ P.ideal.mul_mem_left _ (hq j).1
  choose r hr using P.relevant
  let μs : Coord n →₀ ℕ := ∑ k ∈ Finset.univ.erase k₀, Finsupp.single ⟨k, r k⟩ D
  have hμs : μs ∈ offMonos n k₀ D := by
    rw [mem_offMonos, map_sum]
    funext j
    rw [Finset.sum_apply]
    simp only [Finsupp.weight_single, coordDeg, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, offDeg]
    rw [Finset.sum_ite_eq]
    by_cases hj : j = k₀
    · subst hj; simp
    · simp [hj]
  have hxs : xv ⟨μs, hμs⟩ ∉ P.ideal := by
    have := P.isPrime
    simp only [xv, μs]
    rw [monomial_sum_one, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, _, hk⟩
    rw [← X_pow_eq_monomial] at hk
    exact hr k (P.isPrime.mem_of_pow_mem _ hk)
  have hdetP : rB.det ∈ P.ideal := (P.isPrime.mem_or_mem (hcr ⟨μs, hμs⟩)).resolve_right hxs
  have h : f Bm.det = rB.det := RingHom.map_det f Bm
  rw [← h] at hdetP
  exact Ideal.mem_comap.mpr hdetP
end GroundTheory.Heights₂.Heights.BlockSurjectivity
