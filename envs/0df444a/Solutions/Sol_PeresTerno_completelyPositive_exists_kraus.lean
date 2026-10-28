-- Prove2me | solution 1 for PeresTerno.completelyPositive_exists_kraus
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:17:12.402768+00:00
-- url     : https://prove2.me/submissions/56850a7b-e3fc-4e52-88fd-7f07e12c554e

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

theorem solution {d e : Type*} [Fintype d] [Fintype e]
    [DecidableEq d] [DecidableEq e]
    (T : Matrix d d ℂ →ₗ[ℂ] Matrix e e ℂ) (hT : PeresTerno.IsCompletelyPositive T) :
    ∃ (N : ℕ) (A : Fin N → Matrix e d ℂ), ∀ ρ, T ρ = PeresTerno.krausUpdate A ρ := by
  classical
  let σ : d ≃ Fin (Fintype.card d) := Fintype.equivFin d
  let Ω : (d × Fin (Fintype.card d)) → ℂ := fun p => if σ p.1 = p.2 then 1 else 0
  have hR : (vecMulVec Ω (star Ω)).PosSemidef := posSemidef_vecMulVec_self_star Ω
  have hC := hT (Fintype.card d) _ hR
  obtain ⟨N, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  refine ⟨N, fun m => Matrix.of fun k i => v m (k, σ i), fun ρ => ?_⟩
  have hE : ∀ a b : d, (fun i j => vecMulVec Ω (star Ω) (i, σ a) (j, σ b)) = single a b (1 : ℂ) := by
    intro a b
    ext i j
    simp only [vecMulVec_apply, Ω, Pi.star_apply, single_apply, EmbeddingLike.apply_eq_iff_eq]
    by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp_all <;> aesop
  have key : ∀ (a b : d) (k l : e),
      T (single a b 1) k l = ∑ m, v m (k, σ a) * star (v m (l, σ b)) := by
    intro a b k l
    have := congrFun (congrFun hv (k, σ a)) (l, σ b)
    simp only [PeresTerno.ampliate, hE] at this
    rw [this, Matrix.sum_apply]
    simp [vecMulVec_apply]
  have hρ : ρ = ∑ a, ∑ b, ρ a b • single a b (1 : ℂ) := by
    conv_lhs => rw [matrix_eq_sum_single ρ]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [smul_single, smul_eq_mul, mul_one]
  ext k l
  conv_lhs => rw [hρ]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, key, smul_eq_mul,
    PeresTerno.krausUpdate, mul_apply, conjTranspose_apply, of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring
