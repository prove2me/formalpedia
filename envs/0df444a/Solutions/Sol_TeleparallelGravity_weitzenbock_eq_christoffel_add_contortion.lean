-- Prove2me | solution 1 for TeleparallelGravity.weitzenbock_eq_christoffel_add_contortion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T11:22:25.851427+00:00
-- url     : https://prove2.me/submissions/83a2c104-964b-415d-8445-9f65a475152d

import Mathlib
import Definitions.Def_TeleparallelGravity_Defs

set_option autoImplicit false

open scoped ContDiff

namespace TeleparallelGravity

open Matrix in
theorem p53e_pd_metric (h : TetradField) (hh : IsTetrad h) (ν σ μ : Fin 4) (x : Spacetime) :
    pd ν (fun y => metric h y σ μ) x =
      ∑ a, ∑ b, minkowski a b * (pd ν (h a σ) x * h b μ x + h a σ x * pd ν (h b μ) x) := by
  have hd : ∀ a μ', HasFDerivAt (h a μ') (fderiv ℝ (h a μ') x) x := fun a μ' =>
    (((hh.smooth a μ').differentiable (by simp)) x).hasFDerivAt
  have H : HasFDerivAt (fun y => metric h y σ μ)
      (∑ a, ∑ b, ((minkowski a b * h a σ x) • fderiv ℝ (h b μ) x
        + h b μ x • (minkowski a b • fderiv ℝ (h a σ) x))) x := by
    unfold metric
    refine HasFDerivAt.fun_sum (fun a _ => HasFDerivAt.fun_sum (fun b _ => ?_))
    have h1 := ((hd a σ).const_mul (minkowski a b)).mul (hd b μ)
    exact h1
  unfold pd
  rw [H.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

end TeleparallelGravity

namespace TeleparallelGravity

/-- lowered Weitzenböck connection `W_{λμν} = Σ_b (hᵀ η)_{λ b} ∂_ν h^b_μ`. -/
noncomputable def p53eWl (h : TetradField) (x : Spacetime) (l μ ν : Fin 4) : ℝ :=
  ∑ b, ((tetradMatrix h x).transpose * minkowski) l b * pd ν (h b μ) x

theorem p53e_eta_symm (a b : Fin 4) : minkowski a b = minkowski b a := by
  by_cases hab : a = b
  · subst hab; rfl
  · simp [minkowski, hab, Ne.symm hab]

theorem p53e_G (h : TetradField) (x : Spacetime) :
    Matrix.of (metric h x) = (tetradMatrix h x).transpose * minkowski * tetradMatrix h x := by
  ext i j
  simp only [Matrix.of_apply, metric, Matrix.mul_apply, Matrix.transpose_apply, tetradMatrix]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

theorem p53e_Gdet (h : TetradField) (hh : IsTetrad h) (x : Spacetime) :
    (Matrix.of (metric h x)).det ≠ 0 := by
  have hη : minkowski.det = -1 := by
    simp [minkowski, Matrix.det_diagonal, Fin.prod_univ_four]
  rw [p53e_G, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hη]
  have := mul_ne_zero (hh.nondegenerate x) (hh.nondegenerate x)
  intro h0; apply this; linarith

theorem p53e_Hinv (h : TetradField) (hh : IsTetrad h) (x : Spacetime) :
    invTetrad h x = invMetric h x * ((tetradMatrix h x).transpose * minkowski) := by
  have hGiG : invMetric h x * Matrix.of (metric h x) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (p53e_Gdet h hh x))
  have hHH : tetradMatrix h x * invTetrad h x = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hh.nondegenerate x))
  calc invTetrad h x = invMetric h x * (Matrix.of (metric h x) * invTetrad h x) := by
        rw [← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    _ = _ := by rw [p53e_G, Matrix.mul_assoc, hHH, Matrix.mul_one]

theorem p53e_W (h : TetradField) (hh : IsTetrad h) (x : Spacetime) (ρ μ ν : Fin 4) :
    weitzenbock h ρ μ ν x = ∑ l, invMetric h x ρ l * p53eWl h x l μ ν := by
  unfold weitzenbock p53eWl
  rw [p53e_Hinv h hh]
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun b _ => ?_))
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem p53e_low (h : TetradField) (hh : IsTetrad h) (x : Spacetime) (μ β ν : Fin 4) :
    ∑ α, metric h x μ α * weitzenbock h α β ν x = p53eWl h x μ β ν := by
  have hGG : Matrix.of (metric h x) * invMetric h x = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (p53e_Gdet h hh x))
  have key : ∀ l, ∑ α, metric h x μ α * invMetric h x α l = (1 : Matrix (Fin 4) (Fin 4) ℝ) μ l := by
    intro l; rw [← hGG]; simp [Matrix.mul_apply]
  simp only [p53e_W h hh, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc ∑ l, ∑ α, metric h x μ α * (invMetric h x α l * p53eWl h x l β ν)
      = ∑ l, (∑ α, metric h x μ α * invMetric h x α l) * p53eWl h x l β ν := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun α _ => ?_)
        ring
    _ = ∑ l, (1 : Matrix (Fin 4) (Fin 4) ℝ) μ l * p53eWl h x l β ν := by simp_rw [key]
    _ = _ := by simp [Matrix.one_apply]

theorem p53e_D (h : TetradField) (hh : IsTetrad h) (x : Spacetime) (ν σ μ : Fin 4) :
    pd ν (fun y => metric h y σ μ) x = p53eWl h x σ μ ν + p53eWl h x μ σ ν := by
  rw [p53e_pd_metric h hh]
  simp only [p53eWl, Matrix.mul_apply, Matrix.transpose_apply, tetradMatrix, Matrix.of_apply,
    Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
    ring
  · refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [p53e_eta_symm a b]
    ring

end TeleparallelGravity

open scoped ContDiff in
open TeleparallelGravity in
theorem solution (h : TetradField) (hh : IsTetrad h)
    (ρ μ ν : Fin 4) (x : Spacetime) :
    weitzenbock h ρ μ ν x = christoffel h ρ μ ν x + contortion h ρ μ ν x := by
  have hTl : ∀ μ' β ν', ∑ α, metric h x μ' α * torsion h α β ν' x
      = p53eWl h x μ' ν' β - p53eWl h x μ' β ν' := by
    intro μ' β ν'
    simp only [torsion, mul_sub, Finset.sum_sub_distrib, p53e_low h hh]
  have hC : ∀ μ' ν', ∑ α, ∑ β, metric h x μ' α * invMetric h x ρ β * torsion h α β ν' x
      = ∑ β, invMetric h x ρ β * (p53eWl h x μ' ν' β - p53eWl h x μ' β ν') := by
    intro μ' ν'
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [← hTl, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    ring
  have hT : torsion h ρ μ ν x
      = ∑ β, invMetric h x ρ β * (p53eWl h x β ν μ - p53eWl h x β μ ν) := by
    simp only [torsion, p53e_W h hh, mul_sub, Finset.sum_sub_distrib]
  rw [p53e_W h hh]
  unfold christoffel contortion
  rw [hC, hC, hT]
  simp only [p53e_D h hh]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  ring

