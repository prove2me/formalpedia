-- Prove2me | solution 1 for OCB2012.exists_kraus_of_cj_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T10:15:07.142119+00:00
-- url     : https://prove2.me/submissions/d09e9309-2b39-45a0-85b6-551612257da6

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Definitions.Def_OCB2012_cj

open Matrix
open scoped Kronecker ComplexOrder

open OCB2012 in
theorem solution {x1 x2 : Type*} [Fintype x1] [Fintype x2]
    [DecidableEq x1] [DecidableEq x2] (Φ : Matrix x1 x1 ℂ →ₗ[ℂ] Matrix x2 x2 ℂ)
    (hJ : (cjMatrix Φ).PosSemidef) :
    ∃ K : x1 × x2 → Matrix x2 x1 ℂ, ∀ ρ, Φ ρ = PeresTerno.krausUpdate K ρ := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hJ.nonneg
  -- the action of `Φ` on matrix units, read off from `J = B⋆B`
  have hentry : ∀ i j k l, Φ (single i j 1) k l = ∑ m, B m (i, k) * star (B m (j, l)) := by
    intro i j k l
    have := congrFun (congrFun hB (j, l)) (i, k)
    simp only [cjMatrix, of_apply, mul_apply, star_apply] at this
    rw [this]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  refine ⟨fun m => Matrix.of fun k i => B m (i, k), fun ρ => ?_⟩
  have hρ : ρ = ∑ i, ∑ j, ρ i j • single i j (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
    simp only [smul_single, smul_eq_mul, mul_one]
  ext k l
  conv_lhs => rw [hρ]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hentry,
    PeresTerno.krausUpdate, mul_apply, conjTranspose_apply, of_apply, Finset.mul_sum,
    Finset.sum_mul]
  calc ∑ i, ∑ j, ∑ m, ρ i j * (B m (i, k) * star (B m (j, l)))
      = ∑ i, ∑ m, ∑ j, ρ i j * (B m (i, k) * star (B m (j, l))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ j, ρ i j * (B m (i, k) * star (B m (j, l))) := Finset.sum_comm
    _ = ∑ m, ∑ j, ∑ i, ρ i j * (B m (i, k) * star (B m (j, l))) :=
        Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun i _ => ?_
        ring
