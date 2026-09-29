-- Prove2me | solution 1 for TeleparallelGravity.torsion_uu_eq_neg_contortion_uu
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T17:44:47.82598+00:00
-- url     : https://prove2.me/submissions/d78ba6a4-2bd2-4d30-9111-73e2999dc2c5

import Mathlib
import Definitions.Def_TeleparallelGravity_Defs

/-! 2ed5bae3 TeleparallelGravity.torsion_uu_eq_neg_contortion_uu.
With `u_l = g_{lα} u^α`, `g` symmetric and invertible (`det g = -(det h)²`), `g⁻¹` symmetric,
`Σ_l g^{lβ} u_l = u^β`, so
`Σ_l K^l_{μρ} u_l = ½(g_{μα} T^α_{βρ} u^β + g_{ρα} T^α_{βμ} u^β - T^l_{μρ} u_l)`.
Contracting with `u^ρ`: the first term vanishes (antisymmetry in `β ρ`), the second equals
`-T^l_{μρ} u_l u^ρ`, the third is `-T^l_{μρ} u_l u^ρ`. -/

set_option autoImplicit false

open scoped ContDiff

namespace TPGBuild

open TeleparallelGravity Matrix

theorem minkowski_symm (a b : Fin 4) : minkowski a b = minkowski b a := by
  unfold minkowski
  by_cases hab : a = b
  · rw [hab]
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]

theorem metric_symm (h : TetradField) (x : Spacetime) (i j : Fin 4) :
    metric h x i j = metric h x j i := by
  unfold metric
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [minkowski_symm b a]
  ring

theorem metric_eq (h : TetradField) (x : Spacetime) :
    Matrix.of (metric h x) = (tetradMatrix h x)ᵀ * minkowski * tetradMatrix h x := by
  ext μ ν
  simp only [Matrix.of_apply, metric, Matrix.mul_apply, Matrix.transpose_apply, tetradMatrix,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem metric_det_ne (h : TetradField) (hh : IsTetrad h) (x : Spacetime) :
    (Matrix.of (metric h x)).det ≠ 0 := by
  rw [metric_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hη : Matrix.det minkowski = -1 := by
    simp [minkowski, Matrix.det_diagonal, Fin.prod_univ_four]
  rw [hη]
  have hd := hh.nondegenerate x
  have e : (tetradMatrix h x).det * -1 * (tetradMatrix h x).det
      = -((tetradMatrix h x).det ^ 2) := by ring
  rw [e]
  exact neg_ne_zero.mpr (pow_ne_zero 2 hd)

theorem invMetric_mul (h : TetradField) (hh : IsTetrad h) (x : Spacetime) :
    invMetric h x * Matrix.of (metric h x) = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (metric_det_ne h hh x))

theorem invMetric_symm (h : TetradField) (x : Spacetime) (i j : Fin 4) :
    invMetric h x i j = invMetric h x j i := by
  have hT : (Matrix.of (metric h x))ᵀ = Matrix.of (metric h x) := by
    ext a b
    rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply, metric_symm h x b a]
  have e : (invMetric h x)ᵀ = invMetric h x := by
    unfold invMetric
    rw [Matrix.transpose_nonsing_inv, hT]
  have := congrFun (congrFun e j) i
  rw [Matrix.transpose_apply] at this
  exact this

theorem pull (Gi : Matrix (Fin 4) (Fin 4) ℝ) (w u : Fin 4 → ℝ)
    (hw : ∀ β, ∑ l, Gi l β * w l = u β) (c : Fin 4 → ℝ) (F : Fin 4 → Fin 4 → ℝ) :
    ∑ l, (∑ α, ∑ β, c α * Gi l β * F α β) * w l = ∑ α, ∑ β, c α * F α β * u β := by
  simp only [Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← hw β, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem tuu_alg (G Gi : Matrix (Fin 4) (Fin 4) ℝ) (hGi : Gi * G = 1)
    (hG : ∀ i j, G i j = G j i) (hGis : ∀ i j, Gi i j = Gi j i)
    (T K : Fin 4 → Fin 4 → Fin 4 → ℝ) (hT : ∀ a b c, T a b c = -T a c b)
    (hK : ∀ ρ μ ν, K ρ μ ν = (1 / 2 : ℝ) *
      ((∑ α, ∑ β, G μ α * Gi ρ β * T α β ν) + (∑ α, ∑ β, G ν α * Gi ρ β * T α β μ)
        - T ρ μ ν))
    (u : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ l, ∑ ρ, T l μ ρ * (∑ α, G l α * u α) * u ρ =
      -∑ l, ∑ ρ, K l μ ρ * (∑ α, G l α * u α) * u ρ := by
  have hc : ∀ (f : Fin 4 → ℝ) (i : Fin 4), ∑ β, Gi i β * ∑ α, G β α * f α = f i := by
    intro f i
    have e : (Gi *ᵥ (G *ᵥ f)) i = ∑ β, Gi i β * ∑ α, G β α * f α := rfl
    rw [← e, Matrix.mulVec_mulVec, hGi, Matrix.one_mulVec]
  have hw : ∀ β, ∑ l, Gi l β * (∑ α, G l α * u α) = u β := by
    intro β
    rw [← hc u β]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hGis l β]
  have hKu : ∀ ρ, (∑ l, K l μ ρ * (∑ α, G l α * u α)) * u ρ =
      (1 / 2 : ℝ) * ((∑ α, ∑ β, G μ α * T α β ρ * u β) * u ρ)
        + (1 / 2 : ℝ) * ((∑ α, ∑ β, G ρ α * T α β μ * u β) * u ρ)
        - (1 / 2 : ℝ) * ((∑ l, T l μ ρ * (∑ α, G l α * u α)) * u ρ) := by
    intro ρ
    have p1 : ∑ l, (∑ α, ∑ β, G μ α * Gi l β * T α β ρ) * (∑ α, G l α * u α)
        = ∑ α, ∑ β, G μ α * T α β ρ * u β :=
      pull Gi (fun l => ∑ α, G l α * u α) u hw (fun α => G μ α) (fun α β => T α β ρ)
    have p2 : ∑ l, (∑ α, ∑ β, G ρ α * Gi l β * T α β μ) * (∑ α, G l α * u α)
        = ∑ α, ∑ β, G ρ α * T α β μ * u β :=
      pull Gi (fun l => ∑ α, G l α * u α) u hw (fun α => G ρ α) (fun α β => T α β μ)
    have e : ∑ l, K l μ ρ * (∑ α, G l α * u α)
        = (1 / 2 : ℝ) * (∑ l, (∑ α, ∑ β, G μ α * Gi l β * T α β ρ) * (∑ α, G l α * u α))
          + (1 / 2 : ℝ) * (∑ l, (∑ α, ∑ β, G ρ α * Gi l β * T α β μ) * (∑ α, G l α * u α))
          - (1 / 2 : ℝ) * (∑ l, T l μ ρ * (∑ α, G l α * u α)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hK]
      ring
    rw [e, p1, p2]
    ring
  have hZ : ∑ ρ, (∑ α, ∑ β, G μ α * T α β ρ * u β) * u ρ = 0 := by
    have anti : ∀ α, ∑ β, ∑ ρ, T α β ρ * u β * u ρ = 0 := by
      intro α
      have e : ∑ β, ∑ ρ, T α β ρ * u β * u ρ = -∑ β, ∑ ρ, T α β ρ * u β * u ρ := by
        conv_rhs => rw [Finset.sum_comm]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [hT α β ρ]
        ring
      linarith
    have e : ∑ ρ, (∑ α, ∑ β, G μ α * T α β ρ * u β) * u ρ
        = ∑ α, G μ α * ∑ β, ∑ ρ, T α β ρ * u β * u ρ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    simp [anti]
  have hQ : ∑ ρ, (∑ α, ∑ β, G ρ α * T α β μ * u β) * u ρ
      = -∑ l, ∑ ρ, T l μ ρ * (∑ α, G l α * u α) * u ρ := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [hT α μ β, hG ρ α]
    ring
  have hL : ∑ ρ, (∑ l, T l μ ρ * (∑ α, G l α * u α)) * u ρ
      = ∑ l, ∑ ρ, T l μ ρ * (∑ α, G l α * u α) * u ρ := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hR : ∑ l, ∑ ρ, K l μ ρ * (∑ α, G l α * u α) * u ρ
      = ∑ ρ, (∑ l, K l μ ρ * (∑ α, G l α * u α)) * u ρ := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hR, Finset.sum_congr rfl fun ρ _ => hKu ρ, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hZ, hQ, hL]
  ring

theorem tuu_main (h : TetradField) (hh : IsTetrad h) (u : Fin 4 → ℝ) (μ : Fin 4)
    (x : Spacetime) :
    ∑ l, ∑ ρ, torsion h l μ ρ x * (∑ α, metric h x l α * u α) * u ρ =
      -∑ l, ∑ ρ, contortion h l μ ρ x * (∑ α, metric h x l α * u α) * u ρ :=
  tuu_alg (Matrix.of (metric h x)) (invMetric h x) (invMetric_mul h hh x)
    (fun i j => metric_symm h x i j) (fun i j => invMetric_symm h x i j)
    (fun a b c => torsion h a b c x) (fun a b c => contortion h a b c x)
    (fun a b c => by simp only [torsion]; ring) (fun _ _ _ => rfl) u μ

end TPGBuild

open TeleparallelGravity in open scoped ContDiff in
theorem solution (h : TetradField) (hh : IsTetrad h)
    (u : Fin 4 → ℝ) (μ : Fin 4) (x : Spacetime) :
    ∑ l, ∑ ρ, torsion h l μ ρ x * (∑ α, metric h x l α * u α) * u ρ =
      -∑ l, ∑ ρ, contortion h l μ ρ x * (∑ α, metric h x l α * u α) * u ρ := by
  exact TPGBuild.tuu_main h hh u μ x
