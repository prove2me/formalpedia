-- Prove2me | solution 1 for TeleparallelGravity.superpotential_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T17:25:45.161339+00:00
-- url     : https://prove2.me/submissions/bcc89591-a2d7-4cae-a22a-003fac7a901a

import Mathlib
import Definitions.Def_TeleparallelGravity_Defs

/-! 67e94fad TeleparallelGravity.superpotential_antisymm.
With `G = g`, `Gi = g⁻¹` (`Gi * G = 1` since `det g = -(det h)² ≠ 0`) and `T` antisymmetric in its
last two indices, contracting the definition of the contortion gives
`K^{μνρ} = ½(A(μ,ν) + C(μ,ν) - A(ν,μ))` with `C(μ,ν) = -C(ν,μ)`, so `K^{μνρ} = -K^{νμρ}`;
the two torsion-vector terms of `S^{ρμν}` swap into each other with a sign. -/

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

theorem kup_antisymm (G Gi : Matrix (Fin 4) (Fin 4) ℝ) (hGi : Gi * G = 1)
    (T K : Fin 4 → Fin 4 → Fin 4 → ℝ) (hT : ∀ a b c, T a b c = -T a c b)
    (hK : ∀ ρ μ ν, K ρ μ ν = (1 / 2 : ℝ) *
      ((∑ α, ∑ β, G μ α * Gi ρ β * T α β ν) + (∑ α, ∑ β, G ν α * Gi ρ β * T α β μ)
        - T ρ μ ν))
    (μ ν ρ : Fin 4) :
    ∑ β, ∑ γ, Gi ν β * Gi ρ γ * K μ β γ = -∑ β, ∑ γ, Gi μ β * Gi ρ γ * K ν β γ := by
  have hc : ∀ (f : Fin 4 → ℝ) (i : Fin 4), ∑ β, Gi i β * ∑ α, G β α * f α = f i := by
    intro f i
    have e : (Gi *ᵥ (G *ᵥ f)) i = ∑ β, Gi i β * ∑ α, G β α * f α := rfl
    rw [← e, Matrix.mulVec_mulVec, hGi, Matrix.one_mulVec]
  have hexp : ∀ μ ν ρ, ∑ β, ∑ γ, Gi ν β * Gi ρ γ * K μ β γ =
      (1 / 2 : ℝ) * (∑ γ, Gi ρ γ * ∑ δ, Gi μ δ * T ν δ γ)
        + (1 / 2 : ℝ) * (∑ β, Gi ν β * ∑ δ, Gi μ δ * T ρ δ β)
        - (1 / 2 : ℝ) * (∑ β, ∑ γ, Gi ν β * Gi ρ γ * T μ β γ) := by
    intro μ ν ρ
    have h1 : ∑ β, ∑ γ, Gi ν β * Gi ρ γ * (∑ α, ∑ δ, G β α * Gi μ δ * T α δ γ)
        = ∑ γ, Gi ρ γ * ∑ δ, Gi μ δ * T ν δ γ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [← hc (fun α => ∑ δ, Gi μ δ * T α δ γ) ν, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun δ _ => ?_
      ring
    have h2 : ∑ β, ∑ γ, Gi ν β * Gi ρ γ * (∑ α, ∑ δ, G γ α * Gi μ δ * T α δ β)
        = ∑ β, Gi ν β * ∑ δ, Gi μ δ * T ρ δ β := by
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [← hc (fun α => ∑ δ, Gi μ δ * T α δ β) ρ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun δ _ => ?_
      ring
    have e : ∀ β γ, Gi ν β * Gi ρ γ * K μ β γ
        = (1 / 2 : ℝ) * (Gi ν β * Gi ρ γ * (∑ α, ∑ δ, G β α * Gi μ δ * T α δ γ))
          + (1 / 2 : ℝ) * (Gi ν β * Gi ρ γ * (∑ α, ∑ δ, G γ α * Gi μ δ * T α δ β))
          - (1 / 2 : ℝ) * (Gi ν β * Gi ρ γ * T μ β γ) := by
      intro β γ
      rw [hK]
      ring
    rw [← h1, ← h2]
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have e13 : ∀ μ ν, ∑ γ, Gi ρ γ * ∑ δ, Gi μ δ * T ν δ γ
      = ∑ β, ∑ γ, Gi μ β * Gi ρ γ * T ν β γ := by
    intro μ ν
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hA2 : ∑ β, Gi ν β * ∑ δ, Gi μ δ * T ρ δ β
      = -∑ β, Gi μ β * ∑ δ, Gi ν δ * T ρ δ β := by
    simp only [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [hT ρ δ β]
    ring
  rw [hexp μ ν ρ, hexp ν μ ρ, e13 μ ν, e13 ν μ, hA2]
  ring

theorem sp_main (h : TetradField) (hh : IsTetrad h) (ρ μ ν : Fin 4) (x : Spacetime) :
    superpotential h ρ μ ν x = -superpotential h ρ ν μ x := by
  have hk : ∑ β, ∑ γ, invMetric h x ν β * invMetric h x ρ γ * contortion h μ β γ x
      = -∑ β, ∑ γ, invMetric h x μ β * invMetric h x ρ γ * contortion h ν β γ x :=
    kup_antisymm (Matrix.of (metric h x)) (invMetric h x) (invMetric_mul h hh x)
      (fun a b c => torsion h a b c x) (fun a b c => contortion h a b c x)
      (fun a b c => by simp only [torsion]; ring) (fun _ _ _ => rfl) μ ν ρ
  simp only [superpotential, contortionUp]
  rw [hk]
  ring

end TPGBuild

open TeleparallelGravity in open scoped ContDiff in
theorem solution (h : TetradField) (hh : IsTetrad h)
    (ρ μ ν : Fin 4) (x : Spacetime) :
    superpotential h ρ μ ν x = -superpotential h ρ ν μ x := by
  exact TPGBuild.sp_main h hh ρ μ ν x
