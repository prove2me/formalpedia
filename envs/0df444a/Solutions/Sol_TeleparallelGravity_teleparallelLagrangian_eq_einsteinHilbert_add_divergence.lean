-- Prove2me | solution 1 for TeleparallelGravity.teleparallelLagrangian_eq_einsteinHilbert_add_divergence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:34:24.189848+00:00
-- url     : https://prove2.me/submissions/8ae98cad-e5ce-4a2f-94b5-2ad296f633f9

import Mathlib
import Definitions.Def_TeleparallelGravity_Defs
import Theorems.Thm_TeleparallelGravity_weitzenbock_eq_christoffel_add_contortion
import Theorems.Thm_TeleparallelGravity_curvature_weitzenbock_eq_zero

/-!
Teleparallel Lagrangian = Einstein–Hilbert Lagrangian + explicit divergence.

Structure:
* `TPCore`, `TPAlg3`: purely algebraic identities over arbitrary arrays (symmetric `G`,
  antisymmetric lowered torsion), proved by expansion over `Fin 4`.
* Analytic lemmas: smoothness, Jacobi's formula `∂h = h Γ^σ_{σρ}`,
  `∂g^{θν} = -g^{θα}Γ^ν_{αρ} - g^{να}Γ^θ_{αρ}`.
* `tpx_curv`: curvature of `Γ° = Γ - K` (milestones `weitzenbock_eq_christoffel_add_contortion`,
  `curvature_weitzenbock_eq_zero`).
* `tpx_core`: `S^{ρμν}T_{ρμν} = A - B - C`; `tpx_scalar`, `tpx_div`; final assembly.
-/



set_option linter.all false

namespace TPCore

noncomputable section

variable (G : Fin 4 → Fin 4 → ℝ) (Γ K : Fin 4 → Fin 4 → Fin 4 → ℝ)

def qA : ℝ := ∑ t, ∑ n, G t n * ∑ r, ∑ s,
  (Γ r s r * K s t n + K r s r * Γ s t n - Γ r s n * K s t r - K r s n * Γ s t r)
def qB : ℝ := ∑ t, ∑ n, G t n * ∑ r, ∑ s, (K r s r * K s t n - K r s n * K s t r)
def qdG (t n r : Fin 4) : ℝ := -∑ a, (G t a * Γ n a r + G n a * Γ t a r)
def qtr (r : Fin 4) : ℝ := ∑ s, Γ s s r
def qC : ℝ :=
  ∑ r, (qtr Γ r * ∑ t, ∑ n, G t n * K r t n + ∑ t, ∑ n, qdG G Γ t n r * K r t n)
    - ∑ n, (qtr Γ n * ∑ t, G t n * ∑ r, K r t r + ∑ t, qdG G Γ t n n * ∑ r, K r t r)

set_option maxHeartbeats 0 in
theorem L1 (hG : ∀ i j, G i j = G j i) :
    qA G Γ K - qC G Γ K =
      ∑ t, ∑ a, ∑ r, ∑ n, G t a * K r t n * (Γ n a r - Γ n r a)
      - ∑ s, (∑ t, ∑ n, G t n * K s t n) * ∑ u, (Γ u u s - Γ u s u)
      + ∑ t, ∑ n, G t n * (∑ r, K r t r) * ∑ u, (Γ u u n - Γ u n u) := by
  simp only [qA, qC, qdG, qtr, Fin.sum_univ_four, Fin.isValue, hG 1 0, hG 2 0, hG 2 1, hG 3 0, hG 3 1, hG 3 2]
  ring

set_option maxHeartbeats 0 in
theorem L2 : qB G K = ∑ s, (∑ r, K r s r) * (∑ t, ∑ n, G t n * K s t n)
    - ∑ t, ∑ n, ∑ r, ∑ s, G t n * K r s n * K s t r := by
  simp only [qB, Fin.sum_univ_four, Fin.isValue]
  ring

end

end TPCore

set_option linter.all false

namespace TPAlg3

noncomputable section

variable (G : Fin 4 → Fin 4 → ℝ) (Tl : Fin 4 → Fin 4 → Fin 4 → ℝ)

def T (r m n : Fin 4) : ℝ := ∑ l, G r l * Tl l m n
def K (r m n : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * (∑ b, G r b * (Tl m b n + Tl n b m) - T G Tl r m n)
def Kup (m n r : Fin 4) : ℝ := ∑ b, ∑ c, G n b * G r c * K G Tl m b c
def L : ℝ := (1 / 2 : ℝ) * ∑ r, ∑ m, ∑ n, Kup G Tl m n r * Tl r m n
def KT : ℝ := ∑ t, ∑ a, ∑ r, ∑ n, G t a * K G Tl r t n * T G Tl n r a
def KK : ℝ := ∑ t, ∑ n, ∑ r, ∑ s, G t n * K G Tl r s n * K G Tl s t r
/-- `M^{ρμ}_ν = G^{μα} K^ρ_{αν}`. -/
def M (r m n : Fin 4) : ℝ := ∑ a, G m a * K G Tl r a n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem core2 (hG : ∀ i j, G i j = G j i) (hT : ∀ l m n, Tl l m n = -Tl l n m) :
    L G Tl = KT G Tl + KK G Tl := by
  have hTz : ∀ l m, Tl l m m = 0 := fun l m => by have := hT l m m; linarith
  have hTs : ∀ l m n, Tl l m n = -Tl l n m := hT
  have Tanti : ∀ r m n, T G Tl r n m = -T G Tl r m n := by
    intro r m n; unfold T; rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun l _ => by rw [hT l n m]; ring)
  have hTK : ∀ r m n, T G Tl r m n = K G Tl r n m - K G Tl r m n := by
    intro r m n; simp only [K, Fin.sum_univ_four]; rw [Tanti r m n]; ring
  -- antisymmetry of `M` in its first two indices
  have hM : ∀ ρ μ ν, M G Tl ρ μ ν = -M G Tl μ ρ ν := by
    intro ρ μ ν
    simp only [M, K, T, Fin.sum_univ_four, Fin.isValue, hTs ν 1 0, hTs ν 2 0, hTs ν 2 1, hTs ν 3 0, hTs ν 3 1, hTs ν 3 2, hTz ν 0, hTz ν 1, hTz ν 2, hTz ν 3]
    ring
  have hMa : ∀ ρ μ ν, M G Tl ρ μ ν = -M G Tl μ ρ ν := hM
  have hMz : ∀ ρ ν, M G Tl ρ ρ ν = 0 := fun ρ ν => by have := hM ρ ρ ν; linarith
  -- rewrite the three contractions through `M`
  have eKK : KK G Tl = ∑ r, ∑ s, ∑ n, K G Tl r s n * M G Tl s n r := by
    simp only [KK, M, Fin.sum_univ_four, Fin.isValue, hG 1 0, hG 2 0, hG 3 0, hG 2 1, hG 3 1, hG 3 2]; ring
  have eKT : KT G Tl = ∑ a, ∑ r, ∑ n, M G Tl r a n * (K G Tl n a r - K G Tl n r a) := by
    simp only [KT, hTK]
    simp only [M, Fin.sum_univ_four, Fin.isValue, hG 1 0, hG 2 0, hG 3 0, hG 2 1, hG 3 1, hG 3 2]; ring
  have eL1 : L G Tl = (1 / 2 : ℝ) * ∑ m, ∑ n, ∑ b, ∑ c,
      G n b * K G Tl m b c * T G Tl c m n := by
    simp only [L, Kup, T, Fin.sum_univ_four, Fin.isValue, hG 1 0, hG 2 0, hG 3 0, hG 2 1, hG 3 1,
      hG 3 2]
    ring
  have eL : L G Tl = (1 / 2 : ℝ) * (∑ m, ∑ b, ∑ c, K G Tl m b c * M G Tl c b m
      - ∑ m, ∑ n, ∑ c, M G Tl m n c * K G Tl c m n) := by
    rw [eL1]
    simp only [hTK]
    simp only [M, Fin.sum_univ_four, Fin.isValue, hG 1 0, hG 2 0, hG 3 0, hG 2 1, hG 3 1, hG 3 2]
    ring
  rw [eL, eKT, eKK]
  simp only [Fin.sum_univ_four, Fin.isValue, hMa 1 0 0, hMa 1 0 1, hMa 1 0 2, hMa 1 0 3, hMa 2 0 0, hMa 2 0 1, hMa 2 0 2, hMa 2 0 3, hMa 2 1 0, hMa 2 1 1, hMa 2 1 2, hMa 2 1 3, hMa 3 0 0, hMa 3 0 1, hMa 3 0 2, hMa 3 0 3, hMa 3 1 0, hMa 3 1 1, hMa 3 1 2, hMa 3 1 3, hMa 3 2 0, hMa 3 2 1, hMa 3 2 2, hMa 3 2 3, hMz 0 0, hMz 0 1, hMz 0 2, hMz 0 3, hMz 1 0, hMz 1 1, hMz 1 2, hMz 1 3, hMz 2 0, hMz 2 1, hMz 2 2, hMz 2 3, hMz 3 0, hMz 3 1, hMz 3 2, hMz 3 3]
  ring

end

end TPAlg3

set_option autoImplicit false

open scoped ContDiff

set_option linter.all false

namespace TeleparallelGravity

/-! ### Smoothness of determinants and inverses of smooth matrix fields -/

theorem tpx_contDiff_det {M : Spacetime → Matrix (Fin 4) (Fin 4) ℝ}
    (hM : ∀ i j, ContDiff ℝ ∞ fun y => M y i j) : ContDiff ℝ ∞ fun y => (M y).det := by
  have key : ∀ σ : Equiv.Perm (Fin 4),
      ContDiff ℝ ∞ fun y => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M y (σ i) i :=
    fun σ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)
  have := ContDiff.sum (s := Finset.univ) (fun σ _ => key σ)
  convert this using 1
  funext y
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Units.smul_def, zsmul_eq_mul]

theorem tpx_contDiff_inv {M : Spacetime → Matrix (Fin 4) (Fin 4) ℝ}
    (hM : ∀ i j, ContDiff ℝ ∞ fun y => M y i j) (hdet : ∀ y, (M y).det ≠ 0) (i j : Fin 4) :
    ContDiff ℝ ∞ fun y => (M y)⁻¹ i j := by
  have hadj : ContDiff ℝ ∞ fun y => (M y).adjugate i j := by
    simp only [Matrix.adjugate_apply]
    apply tpx_contDiff_det
    intro a b
    simp only [Matrix.updateRow_apply]
    by_cases hab : a = j
    · simp only [hab, if_true]; exact contDiff_const
    · simp only [hab, if_false]; exact hM a b
  have hd : ContDiff ℝ ∞ fun y => ((M y).det)⁻¹ := (tpx_contDiff_det hM).inv hdet
  have eq : (fun y => (M y)⁻¹ i j) = fun y => ((M y).det)⁻¹ * (M y).adjugate i j := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [eq]; exact hd.mul hadj

theorem tpx_contDiff_pd {f : Spacetime → ℝ} (hf : ContDiff ℝ ∞ f) (ν : Fin 4) :
    ContDiff ℝ ∞ fun y => pd ν f y := by
  unfold pd
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-! ### Partial derivative rules -/

theorem tpx_pd_add {f g : Spacetime → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (ν : Fin 4) :
    pd ν (fun y => f y + g y) x = pd ν f x + pd ν g x := by
  unfold pd; rw [fderiv_fun_add hf hg]; rfl

theorem tpx_pd_sub {f g : Spacetime → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (ν : Fin 4) :
    pd ν (fun y => f y - g y) x = pd ν f x - pd ν g x := by
  unfold pd; rw [fderiv_fun_sub hf hg]; rfl

theorem tpx_pd_mul {f g : Spacetime → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (ν : Fin 4) :
    pd ν (fun y => f y * g y) x = pd ν f x * g x + f x * pd ν g x := by
  unfold pd; rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem tpx_pd_const_mul {f : Spacetime → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (c : ℝ) (ν : Fin 4) :
    pd ν (fun y => c * f y) x = c * pd ν f x := by
  unfold pd; rw [fderiv_const_mul hf]; rfl

theorem tpx_pd_sum {ι : Type} (s : Finset ι) {f : ι → Spacetime → ℝ} {x : Spacetime}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (ν : Fin 4) :
    pd ν (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, pd ν (f i) x := by
  unfold pd; rw [fderiv_fun_sum hf]; simp

/-! ### Basic algebra of the tetrad, metric and Weitzenböck connection -/

/-- Lowered Weitzenböck connection `W_{λμν} = η_ab h^a_λ ∂_ν h^b_μ`. -/
noncomputable def tpxW (h : TetradField) (x : Spacetime) (l μ ν : Fin 4) : ℝ :=
  ∑ a, ∑ b, minkowski a b * h a l x * pd ν (h b μ) x

theorem tpx_eta_symm (a b : Fin 4) : minkowski a b = minkowski b a := by
  by_cases hab : a = b
  · subst hab; rfl
  · simp [minkowski, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]

theorem tpx_metric_mat (h : TetradField) (x : Spacetime) :
    Matrix.of (metric h x) = (tetradMatrix h x).transpose * minkowski * tetradMatrix h x := by
  ext i j
  simp only [Matrix.of_apply, metric, Matrix.mul_apply, Matrix.transpose_apply, tetradMatrix]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

theorem tpx_eta_det : minkowski.det = -1 := by
  simp [minkowski, Matrix.det_diagonal, Fin.prod_univ_four]

theorem tpx_metric_det (h : TetradField) (x : Spacetime) :
    (Matrix.of (metric h x)).det = -(tetradDet h x) ^ 2 := by
  rw [tpx_metric_mat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, tpx_eta_det]
  unfold tetradDet; ring

theorem tpx_metric_det_ne (h : TetradField) (hh : IsTetrad h) (x : Spacetime) :
    (Matrix.of (metric h x)).det ≠ 0 := by
  rw [tpx_metric_det]
  have := hh.nondegenerate x
  unfold tetradDet
  intro h0; apply this; nlinarith [sq_nonneg (tetradMatrix h x).det]

theorem tpx_metric_symm (h : TetradField) (x : Spacetime) (μ ν : Fin 4) :
    metric h x μ ν = metric h x ν μ := by
  unfold metric
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [tpx_eta_symm]; ring

theorem tpx_invMetric_symm (h : TetradField) (x : Spacetime) (μ ν : Fin 4) :
    invMetric h x μ ν = invMetric h x ν μ := by
  have hs : (Matrix.of (metric h x)).transpose = Matrix.of (metric h x) := by
    ext i j; simp [tpx_metric_symm h x j i]
  have : (invMetric h x).transpose = invMetric h x := by
    unfold invMetric; rw [Matrix.transpose_nonsing_inv, hs]
  calc invMetric h x μ ν = (invMetric h x).transpose ν μ := rfl
    _ = invMetric h x ν μ := by rw [this]

theorem tpx_G_g (h : TetradField) (hh : IsTetrad h) (x : Spacetime) (μ ν : Fin 4) :
    ∑ β, invMetric h x μ β * metric h x β ν = if μ = ν then 1 else 0 := by
  have := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (tpx_metric_det_ne h hh x))
  have e := congrFun (congrFun this μ) ν
  simpa [Matrix.mul_apply, Matrix.one_apply, invMetric] using e

theorem tpx_g_G (h : TetradField) (hh : IsTetrad h) (x : Spacetime) (μ ν : Fin 4) :
    ∑ β, metric h x μ β * invMetric h x β ν = if μ = ν then 1 else 0 := by
  have := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (tpx_metric_det_ne h hh x))
  have e := congrFun (congrFun this μ) ν
  simpa [Matrix.mul_apply, Matrix.one_apply, invMetric] using e

theorem tpx_invTetrad_eq (h : TetradField) (hh : IsTetrad h) (x : Spacetime) :
    invTetrad h x = invMetric h x * ((tetradMatrix h x).transpose * minkowski) := by
  have hGiG : invMetric h x * Matrix.of (metric h x) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (tpx_metric_det_ne h hh x))
  have hHH : tetradMatrix h x * invTetrad h x = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hh.nondegenerate x))
  calc invTetrad h x = invMetric h x * (Matrix.of (metric h x) * invTetrad h x) := by
        rw [← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    _ = _ := by rw [tpx_metric_mat, Matrix.mul_assoc, hHH, Matrix.mul_one]

/-- `Γ^ρ_{μν} = g^{ρλ} W_{λμν}`. -/
theorem tpx_weitz_eq (h : TetradField) (hh : IsTetrad h) (x : Spacetime) (ρ μ ν : Fin 4) :
    weitzenbock h ρ μ ν x = ∑ l, invMetric h x ρ l * tpxW h x l μ ν := by
  unfold weitzenbock tpxW
  rw [tpx_invTetrad_eq h hh]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, tetradMatrix, Matrix.of_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [tpx_eta_symm a b]; ring

/-! ### Smoothness of the geometric objects -/

section Smooth
variable (h : TetradField) (hh : IsTetrad h)
include hh

theorem tpx_sm_h (a μ : Fin 4) : ContDiff ℝ ∞ (h a μ) := hh.smooth a μ

theorem tpx_sm_dh (a μ ν : Fin 4) : ContDiff ℝ ∞ fun y => pd ν (h a μ) y :=
  tpx_contDiff_pd (hh.smooth a μ) ν

theorem tpx_sm_metric (σ μ : Fin 4) : ContDiff ℝ ∞ fun y => metric h y σ μ := by
  unfold metric
  have := hh.smooth
  fun_prop

theorem tpx_sm_det : ContDiff ℝ ∞ (tetradDet h) := by
  unfold tetradDet
  exact tpx_contDiff_det (fun i j => by simpa [tetradMatrix] using hh.smooth i j)

theorem tpx_sm_invTetrad (i j : Fin 4) : ContDiff ℝ ∞ fun y => invTetrad h y i j := by
  unfold invTetrad
  exact tpx_contDiff_inv (fun a b => by simpa [tetradMatrix] using hh.smooth a b)
    hh.nondegenerate i j

theorem tpx_sm_invMetric (i j : Fin 4) : ContDiff ℝ ∞ fun y => invMetric h y i j := by
  unfold invMetric
  exact tpx_contDiff_inv (fun a b => by simpa using tpx_sm_metric h hh a b)
    (tpx_metric_det_ne h hh) i j

theorem tpx_sm_weitz (ρ μ ν : Fin 4) : ContDiff ℝ ∞ (weitzenbock h ρ μ ν) := by
  unfold weitzenbock
  have := tpx_sm_invTetrad h hh
  have := tpx_sm_dh h hh
  fun_prop

theorem tpx_sm_torsion (ρ μ ν : Fin 4) : ContDiff ℝ ∞ (torsion h ρ μ ν) := by
  unfold torsion
  exact (tpx_sm_weitz h hh ρ ν μ).sub (tpx_sm_weitz h hh ρ μ ν)

theorem tpx_sm_contortion (ρ μ ν : Fin 4) : ContDiff ℝ ∞ (contortion h ρ μ ν) := by
  unfold contortion
  have := tpx_sm_metric h hh
  have := tpx_sm_invMetric h hh
  have := tpx_sm_torsion h hh
  fun_prop

end Smooth

/-! ### Derivatives of the metric and of the determinant -/

theorem tpx_pd_metric (h : TetradField) (hh : IsTetrad h) (σ μ ρ : Fin 4) (x : Spacetime) :
    pd ρ (fun y => metric h y σ μ) x = tpxW h x σ μ ρ + tpxW h x μ σ ρ := by
  have hd : ∀ a μ, Differentiable ℝ (h a μ) := fun a μ => (hh.smooth a μ).differentiable (by simp)
  have hab : ∀ a b, pd ρ (fun y => minkowski a b * h a σ y * h b μ y) x =
      minkowski b a * h b μ x * pd ρ (h a σ) x + minkowski a b * h a σ x * pd ρ (h b μ) x := by
    intro a b
    rw [tpx_pd_mul (((hd a σ) x).const_mul _) ((hd b μ) x), tpx_pd_const_mul ((hd a σ) x),
      tpx_eta_symm b a]
    ring
  unfold metric tpxW
  rw [tpx_pd_sum (f := fun a y => ∑ b, minkowski a b * h a σ y * h b μ y) Finset.univ (fun a _ =>
    DifferentiableAt.fun_sum (fun b _ => (((hd a σ) x).const_mul _).mul ((hd b μ) x)))]
  have hsum : ∀ a, pd ρ (fun y => ∑ b, minkowski a b * h a σ y * h b μ y) x =
      ∑ b, (minkowski b a * h b μ x * pd ρ (h a σ) x +
        minkowski a b * h a σ x * pd ρ (h b μ) x) := fun a => by
    rw [tpx_pd_sum (f := fun b y => minkowski a b * h a σ y * h b μ y) Finset.univ
      (fun b _ => (((hd a σ) x).const_mul _).mul ((hd b μ) x))]
    exact Finset.sum_congr rfl (fun b _ => hab a b)
  simp_rw [hsum, Finset.sum_add_distrib]
  rw [add_comm, Finset.sum_comm (f := fun a b => minkowski b a * h b μ x * pd ρ (h a σ) x)]

/-- Jacobi's formula: `∂_ρ h = h Γ^σ_{σρ}`. -/
theorem tpx_pd_det (h : TetradField) (hh : IsTetrad h) (ρ : Fin 4) (x : Spacetime) :
    pd ρ (tetradDet h) x = tetradDet h x * ∑ σ, weitzenbock h σ σ ρ x := by
  classical
  let D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin 4 → ℝ) ℝ :=
    { (Matrix.detRowAlternating : (Fin 4 → ℝ) [⋀^Fin 4]→ₗ[ℝ] ℝ).toMultilinearMap with
      cont := by
        change Continuous fun M : Fin 4 → Fin 4 → ℝ => Matrix.det (Matrix.of M)
        exact continuous_id.matrix_det }
  let R : Spacetime → (Fin 4 → Fin 4 → ℝ) := fun y a μ => h a μ y
  have hd : ∀ a μ, Differentiable ℝ (h a μ) := fun a μ => (hh.smooth a μ).differentiable (by simp)
  have hR : HasFDerivAt R (ContinuousLinearMap.pi fun a =>
      ContinuousLinearMap.pi fun μ => fderiv ℝ (h a μ) x) x := by
    refine hasFDerivAt_pi.2 (fun a => hasFDerivAt_pi.2 (fun μ => (hd a μ x).hasFDerivAt))
  have hDR : HasFDerivAt (tetradDet h) _ x := (D.hasFDerivAt (R x)).comp x hR
  unfold pd
  rw [hDR.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousMultilinearMap.linearDeriv_apply, ContinuousLinearMap.pi_apply]
  -- each summand is the determinant with one row replaced by its derivative
  set E := tetradMatrix h x with hE
  set Ei := invTetrad h x with hEi
  have hEiE : Ei * E = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hh.nondegenerate x))
  have hrow : ∀ a, (fun μ => fderiv ℝ (h a μ) x (Pi.single ρ 1)) =
      ∑ k, (∑ ν, pd ρ (h a ν) x * Ei ν k) • E k := by
    intro a; funext μ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    have key : ∀ ν, ∑ k, Ei ν k * E k μ = if ν = μ then 1 else 0 := fun ν => by
      have := congrArg (fun M => M ν μ) hEiE
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, key]
    simp [pd]
  have hterm : ∀ i, D (Function.update (R x) i
      ((ContinuousLinearMap.pi fun μ => fderiv ℝ (h i μ) x) (Pi.single ρ 1))) =
      (∑ ν, pd ρ (h i ν) x * Ei ν i) * tetradDet h x := by
    intro i
    have e1 : (ContinuousLinearMap.pi fun μ => fderiv ℝ (h i μ) x) (Pi.single ρ 1) =
        fun μ => fderiv ℝ (h i μ) x (Pi.single ρ 1) := rfl
    rw [e1, hrow i]
    have hD : ∀ v, D v = Matrix.det (Matrix.of v) := fun v => rfl
    have hU : ∀ w, Function.update (R x) i w = E.updateRow i w := fun w => rfl
    rw [hD, hU]
    have hof : ∀ A : Matrix (Fin 4) (Fin 4) ℝ, Matrix.of (fun a b => A a b) = A := fun A => rfl
    rw [hof, Matrix.det_updateRow_sum, smul_eq_mul]
    rfl
  simp_rw [hterm, ← Finset.sum_mul]
  rw [mul_comm]
  congr 1
  unfold weitzenbock
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun a _ => ?_))
  rw [hEi]; ring

/-- `∂_ρ g^{θν} = -g^{θα} Γ^ν_{αρ} - g^{να} Γ^θ_{αρ}`. -/
theorem tpx_pd_invMetric (h : TetradField) (hh : IsTetrad h) (θ ν ρ : Fin 4) (x : Spacetime) :
    pd ρ (fun y => invMetric h y θ ν) x =
      -∑ α, (invMetric h x θ α * weitzenbock h ν α ρ x +
        invMetric h x ν α * weitzenbock h θ α ρ x) := by
  have hGd : ∀ i j, Differentiable ℝ fun y => invMetric h y i j :=
    fun i j => (tpx_sm_invMetric h hh i j).differentiable (by simp)
  have hgd : ∀ i j, Differentiable ℝ fun y => metric h y i j :=
    fun i j => (tpx_sm_metric h hh i j).differentiable (by simp)
  -- differentiate `g^{θβ} g_{βμ} = δ`
  have E1 : ∀ μ, ∑ β, pd ρ (fun y => invMetric h y θ β) x * metric h x β μ =
      -∑ β, invMetric h x θ β * (tpxW h x β μ ρ + tpxW h x μ β ρ) := by
    intro μ
    have hc : (fun y => ∑ β, invMetric h y θ β * metric h y β μ) =
        fun _ => if θ = μ then (1 : ℝ) else 0 := by
      funext y; exact tpx_G_g h hh y θ μ
    have h0 : pd ρ (fun y => ∑ β, invMetric h y θ β * metric h y β μ) x = 0 := by
      rw [hc]; unfold pd; simp
    rw [tpx_pd_sum (f := fun β y => invMetric h y θ β * metric h y β μ) Finset.univ
      (fun β _ => ((hGd θ β).mul (hgd β μ)) x)] at h0
    simp only [tpx_pd_mul ((hGd _ _) x) ((hgd _ _) x), tpx_pd_metric h hh,
      Finset.sum_add_distrib] at h0
    linarith
  have E2 : pd ρ (fun y => invMetric h y θ ν) x =
      ∑ μ, (∑ β, pd ρ (fun y => invMetric h y θ β) x * metric h x β μ) * invMetric h x μ ν := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, tpx_g_G h hh]
    simp
  have E3 : ∀ μ, invMetric h x μ ν = invMetric h x ν μ := fun μ => tpx_invMetric_symm h x μ ν
  rw [E2]
  simp_rw [E1, E3]
  simp only [tpx_weitz_eq h hh, Fin.sum_univ_four]
  ring

end TeleparallelGravity

set_option autoImplicit false
set_option linter.all false

open scoped ContDiff

namespace TeleparallelGravity

section Rel
variable (h : TetradField) (hh : IsTetrad h) (x : Spacetime)
include hh

theorem tpx_R2 (ρ μ ν : Fin 4) :
    torsion h ρ μ ν x = ∑ l, invMetric h x ρ l * torsionLower h l μ ν x := by
  unfold torsionLower
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, tpx_G_g h hh]
  simp

theorem tpx_R3 (ρ μ ν : Fin 4) :
    contortion h ρ μ ν x = (1 / 2 : ℝ) * (∑ b, invMetric h x ρ b *
      (torsionLower h μ b ν x + torsionLower h ν b μ x) - torsion h ρ μ ν x) := by
  have key : ∀ μ ν, ∑ α, ∑ β, metric h x μ α * invMetric h x ρ β * torsion h α β ν x =
      ∑ b, invMetric h x ρ b * ∑ α, metric h x μ α * torsion h α b ν x := by
    intro μ ν
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => by ring)
  unfold contortion torsionLower
  rw [key, key, ← Finset.sum_add_distrib]
  simp only [mul_add]

end Rel

theorem tpx_Tl_anti (h : TetradField) (x : Spacetime) (l μ ν : Fin 4) :
    torsionLower h l μ ν x = -torsionLower h l ν μ x := by
  unfold torsionLower torsion
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun a _ => by ring)

theorem tpx_Tl_zero (h : TetradField) (x : Spacetime) (l μ : Fin 4) :
    torsionLower h l μ μ x = 0 := by
  have := tpx_Tl_anti h x l μ μ; linarith

section Alg
variable (h : TetradField) (hh : IsTetrad h) (x : Spacetime)
include hh

/-- `K^ρ_{θρ} = -T^ρ_{θρ}`. -/
theorem tpx_k (θ : Fin 4) :
    ∑ ρ, contortion h ρ θ ρ x = -∑ u, torsion h u θ u x := by
  have s := tpx_invMetric_symm h x
  have a := tpx_Tl_anti h x
  have z := tpx_Tl_zero h x
  simp only [tpx_R3 h hh x, tpx_R2 h hh x]
  fin_cases θ <;>
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, s 1 0, s 2 0, s 2 1, s 3 0, s 3 1, s 3 2, a 0 1 0, a 0 2 0, a 0 2 1, a 0 3 0, a 0 3 1, a 0 3 2, a 1 1 0, a 1 2 0, a 1 2 1, a 1 3 0, a 1 3 1, a 1 3 2, a 2 1 0, a 2 2 0, a 2 2 1, a 2 3 0, a 2 3 1, a 2 3 2, a 3 1 0, a 3 2 0, a 3 2 1, a 3 3 0, a 3 3 1, a 3 3 2, z 0 0, z 0 1, z 0 2, z 0 3, z 1 0, z 1 1, z 1 2, z 1 3, z 2 0, z 2 1, z 2 2, z 2 3, z 3 0, z 3 1, z 3 2, z 3 3] <;>
  ring

/-- `g^{θν} K^σ_{θν} = T^{νσ}{}_ν`. -/
theorem tpx_f (σ : Fin 4) :
    ∑ t, ∑ n, invMetric h x t n * contortion h σ t n x = torsionVectorUp h σ x := by
  have s := tpx_invMetric_symm h x
  have a := tpx_Tl_anti h x
  have z := tpx_Tl_zero h x
  unfold torsionVectorUp
  simp only [tpx_R3 h hh x, tpx_R2 h hh x]
  fin_cases σ <;>
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, s 1 0, s 2 0, s 2 1, s 3 0, s 3 1, s 3 2, a 0 1 0, a 0 2 0, a 0 2 1, a 0 3 0, a 0 3 1, a 0 3 2, a 1 1 0, a 1 2 0, a 1 2 1, a 1 3 0, a 1 3 1, a 1 3 2, a 2 1 0, a 2 2 0, a 2 2 1, a 2 3 0, a 2 3 1, a 2 3 2, a 3 1 0, a 3 2 0, a 3 2 1, a 3 3 0, a 3 3 1, a 3 3 2, z 0 0, z 0 1, z 0 2, z 0 3, z 1 0, z 1 1, z 1 2, z 1 3, z 2 0, z 2 1, z 2 2, z 2 3, z 3 0, z 3 1, z 3 2, z 3 3] <;>
  ring

theorem tpx_L3 :
    ∑ ρ, ∑ μ, ∑ ν, superpotential h ρ μ ν x * torsionLower h ρ μ ν x =
      (1 / 2 : ℝ) * ∑ ρ, ∑ μ, ∑ ν, contortionUp h μ ν ρ x * torsionLower h ρ μ ν x
      - ∑ μ, torsionVectorUp h μ x * ∑ u, torsion h u μ u x := by
  have s := tpx_invMetric_symm h x
  have a := tpx_Tl_anti h x
  have z := tpx_Tl_zero h x
  unfold superpotential
  simp only [tpx_R2 h hh x]
  simp only [Fin.sum_univ_four, Fin.isValue, s 1 0, s 2 0, s 2 1, s 3 0, s 3 1, s 3 2, a 0 1 0, a 0 2 0, a 0 2 1, a 0 3 0, a 0 3 1, a 0 3 2, a 1 1 0, a 1 2 0, a 1 2 1, a 1 3 0, a 1 3 1, a 1 3 2, a 2 1 0, a 2 2 0, a 2 2 1, a 2 3 0, a 2 3 1, a 2 3 2, a 3 1 0, a 3 2 0, a 3 2 1, a 3 3 0, a 3 3 1, a 3 3 2, z 0 0, z 0 1, z 0 2, z 0 3, z 1 0, z 1 1, z 1 2, z 1 3, z 2 0, z 2 1, z 2 2, z 2 3, z 3 0, z 3 1, z 3 2, z 3 3]
  ring

theorem tpx_core :
    ∑ ρ, ∑ μ, ∑ ν, superpotential h ρ μ ν x * torsionLower h ρ μ ν x =
      TPCore.qA (fun i j => invMetric h x i j) (fun a b c => weitzenbock h a b c x)
          (fun a b c => contortion h a b c x)
        - TPCore.qB (fun i j => invMetric h x i j) (fun a b c => contortion h a b c x)
        - TPCore.qC (fun i j => invMetric h x i j) (fun a b c => weitzenbock h a b c x)
          (fun a b c => contortion h a b c x) := by
  have e1 := TPCore.L1 (fun i j => invMetric h x i j) (fun a b c => weitzenbock h a b c x)
    (fun a b c => contortion h a b c x) (tpx_invMetric_symm h x)
  have e2 := TPCore.L2 (fun i j => invMetric h x i j) (fun a b c => contortion h a b c x)
  have e3 := TPAlg3.core2 (fun i j => invMetric h x i j) (fun l m n => torsionLower h l m n x)
    (tpx_invMetric_symm h x) (tpx_Tl_anti h x)
  have e4 := tpx_L3 h hh x
  have hT : ∀ r m n, TPAlg3.T (fun i j => invMetric h x i j) (fun l m n => torsionLower h l m n x)
      r m n = torsion h r m n x := fun r m n => (tpx_R2 h hh x r m n).symm
  have hK : ∀ r m n, TPAlg3.K (fun i j => invMetric h x i j)
      (fun l m n => torsionLower h l m n x) r m n = contortion h r m n x := by
    intro r m n
    rw [tpx_R3 h hh x]
    simp only [TPAlg3.K, hT]
  simp only [TPAlg3.L, TPAlg3.KT, TPAlg3.KK, TPAlg3.Kup, hK, hT] at e3
  unfold contortionUp at e4
  have hTor : ∀ n r a, weitzenbock h n a r x - weitzenbock h n r a x = torsion h n r a x :=
    fun _ _ _ => rfl
  simp only [hTor, tpx_f h hh x, tpx_k h hh x] at e1 e2
  have hX : ∑ t, ∑ n, invMetric h x t n * -(∑ u, torsion h u t u x) * ∑ u, torsion h u n u x =
      -∑ μ, torsionVectorUp h μ x * ∑ u, torsion h u μ u x := by
    unfold torsionVectorUp
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    generalize (∑ u, torsion h u t u x) = A
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  have hY : ∑ s, -(∑ u, torsion h u s u x) * torsionVectorUp h s x =
      -∑ μ, torsionVectorUp h μ x * ∑ u, torsion h u μ u x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun t _ => by ring)
  rw [hX] at e1
  rw [hY] at e2
  linarith

end Alg

section Curv
variable (h : TetradField) (hh : IsTetrad h) (x : Spacetime)
include hh

theorem tpx_curv (ρ θ μ ν : Fin 4) :
    curvature (christoffel h) ρ θ μ ν x =
      -(pd μ (contortion h ρ θ ν) x - pd ν (contortion h ρ θ μ) x)
      - ∑ σ, (weitzenbock h ρ σ μ x * contortion h σ θ ν x
          + contortion h ρ σ μ x * weitzenbock h σ θ ν x
          - weitzenbock h ρ σ ν x * contortion h σ θ μ x
          - contortion h ρ σ ν x * weitzenbock h σ θ μ x)
      + ∑ σ, (contortion h ρ σ μ x * contortion h σ θ ν x
          - contortion h ρ σ ν x * contortion h σ θ μ x) := by
  have hc : christoffel h = fun a b c y => weitzenbock h a b c y - contortion h a b c y := by
    funext a b c y
    rw [weitzenbock_eq_christoffel_add_contortion h hh a b c y]; ring
  have h0 := curvature_weitzenbock_eq_zero h hh ρ θ μ ν x
  have hW : ∀ a b c, DifferentiableAt ℝ (weitzenbock h a b c) x :=
    fun a b c => ((tpx_sm_weitz h hh a b c).differentiable (by simp)) x
  have hK : ∀ a b c, DifferentiableAt ℝ (contortion h a b c) x :=
    fun a b c => ((tpx_sm_contortion h hh a b c).differentiable (by simp)) x
  unfold curvature at h0 ⊢
  rw [hc]
  simp only []
  rw [tpx_pd_sub (hW _ _ _) (hK _ _ _), tpx_pd_sub (hW _ _ _) (hK _ _ _)]
  simp only [Fin.sum_univ_four] at h0 ⊢
  linear_combination h0

theorem tpx_scalar :
    scalarCurvature h x =
      -(∑ t, ∑ n, invMetric h x t n *
          ∑ r, (pd r (contortion h r t n) x - pd n (contortion h r t r) x))
      - TPCore.qA (fun i j => invMetric h x i j) (fun a b c => weitzenbock h a b c x)
          (fun a b c => contortion h a b c x)
      + TPCore.qB (fun i j => invMetric h x i j) (fun a b c => contortion h a b c x) := by
  unfold scalarCurvature ricci TPCore.qA TPCore.qB
  simp only [tpx_curv h hh x]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, mul_add, mul_sub,
    mul_neg, Finset.mul_sum]

theorem tpx_e (μ : Fin 4) :
    ∑ t, invMetric h x t μ * ∑ r, contortion h r t r x = -torsionVectorUp h μ x := by
  simp only [tpx_k h hh x]
  unfold torsionVectorUp
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [tpx_invMetric_symm h x t μ]; ring

theorem tpx_div :
    ∑ μ, pd μ (fun y => tetradDet h y * torsionVectorUp h μ y) x =
      tetradDet h x / 2 *
        (TPCore.qC (fun i j => invMetric h x i j) (fun a b c => weitzenbock h a b c x)
            (fun a b c => contortion h a b c x)
          + ∑ r, ∑ t, ∑ n, invMetric h x t n * pd r (contortion h r t n) x
          - ∑ n, ∑ t, invMetric h x t n * ∑ r, pd n (contortion h r t r) x) := by
  have sG := tpx_sm_invMetric h hh
  have sK := tpx_sm_contortion h hh
  have sD := tpx_sm_det h hh
  have dG : ∀ i j, Differentiable ℝ fun y => invMetric h y i j :=
    fun i j => (sG i j).differentiable (by simp)
  have dK : ∀ a b c, Differentiable ℝ (contortion h a b c) :=
    fun a b c => (sK a b c).differentiable (by simp)
  have dD : Differentiable ℝ (tetradDet h) := sD.differentiable (by simp)
  have hV : ∀ μ, (fun y => tetradDet h y * torsionVectorUp h μ y) = fun y => tetradDet h y *
      ((1 / 2 : ℝ) * (∑ t, ∑ n, invMetric h y t n * contortion h μ t n y)
        - (1 / 2 : ℝ) * (∑ t, invMetric h y t μ * ∑ r, contortion h r t r y)) := by
    intro μ; funext y
    rw [tpx_f h hh y, tpx_e h hh y]; ring
  have hf : ∀ μ, pd μ (fun y => ∑ t, ∑ n, invMetric h y t n * contortion h μ t n y) x =
      ∑ t, ∑ n, (pd μ (fun y => invMetric h y t n) x * contortion h μ t n x
        + invMetric h x t n * pd μ (contortion h μ t n) x) := by
    intro μ
    rw [tpx_pd_sum (f := fun t y => ∑ n, invMetric h y t n * contortion h μ t n y) Finset.univ
      (fun t _ => by fun_prop)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [tpx_pd_sum (f := fun n y => invMetric h y t n * contortion h μ t n y) Finset.univ
      (fun n _ => by fun_prop)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [tpx_pd_mul ((dG t n) x) ((dK μ t n) x)]
  have he : ∀ μ, pd μ (fun y => ∑ t, invMetric h y t μ * ∑ r, contortion h r t r y) x =
      ∑ t, (pd μ (fun y => invMetric h y t μ) x * ∑ r, contortion h r t r x
        + invMetric h x t μ * ∑ r, pd μ (contortion h r t r) x) := by
    intro μ
    rw [tpx_pd_sum (f := fun t y => invMetric h y t μ * ∑ r, contortion h r t r y) Finset.univ
      (fun t _ => by fun_prop)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [tpx_pd_mul ((dG t μ) x) (by fun_prop)]
    rw [tpx_pd_sum (f := fun r y => contortion h r t r y) Finset.univ (fun r _ => (dK r t r) x)]
  have hμ : ∀ μ, pd μ (fun y => tetradDet h y * torsionVectorUp h μ y) x =
      pd μ (tetradDet h) x * ((1 / 2 : ℝ) * (∑ t, ∑ n, invMetric h x t n * contortion h μ t n x)
        - (1 / 2 : ℝ) * (∑ t, invMetric h x t μ * ∑ r, contortion h r t r x))
      + tetradDet h x * ((1 / 2 : ℝ) *
          pd μ (fun y => ∑ t, ∑ n, invMetric h y t n * contortion h μ t n y) x
        - (1 / 2 : ℝ) * pd μ (fun y => ∑ t, invMetric h y t μ * ∑ r, contortion h r t r y) x) := by
    intro μ
    rw [hV μ, tpx_pd_mul (dD x) (by fun_prop), tpx_pd_sub (by fun_prop) (by fun_prop),
      tpx_pd_const_mul (by fun_prop), tpx_pd_const_mul (by fun_prop)]
  simp only [hμ, hf, he, tpx_pd_det h hh, tpx_pd_invMetric h hh, TPCore.qC, TPCore.qdG,
    TPCore.qtr]
  have s := tpx_invMetric_symm h x
  simp only [Fin.sum_univ_four, Fin.isValue, s 1 0, s 2 0, s 2 1, s 3 0, s 3 1, s 3 2]
  ring

end Curv

end TeleparallelGravity

open scoped ContDiff in
open TeleparallelGravity in
theorem solution
    (c G : ℝ) (h : TetradField) (hh : IsTetrad h) (hpos : ∀ x, 0 < tetradDet h x)
    (x : Spacetime) :
    teleparallelLagrangian c G h x =
      einsteinHilbertLagrangian c G h x +
        ∑ μ, pd μ (fun y => -(c ^ 4 / (8 * Real.pi * G)) *
          (tetradDet h y * torsionVectorUp h μ y)) x := by
  have hsq : Real.sqrt (-(Matrix.of (metric h x)).det) = tetradDet h x := by
    rw [tpx_metric_det, neg_neg, Real.sqrt_sq (le_of_lt (hpos x))]
  have hdV : ∀ μ, DifferentiableAt ℝ (fun y => tetradDet h y * torsionVectorUp h μ y) x := by
    intro μ
    have sG := tpx_sm_invMetric h hh
    have sT := tpx_sm_torsion h hh
    have sD := tpx_sm_det h hh
    unfold torsionVectorUp
    have : ContDiff ℝ ∞ fun y => tetradDet h y *
        ∑ β, invMetric h y μ β * ∑ σ, torsion h σ β σ y := by fun_prop
    exact (this.differentiable (by simp)) x
  have hsum : ∑ μ, pd μ (fun y => -(c ^ 4 / (8 * Real.pi * G)) *
      (tetradDet h y * torsionVectorUp h μ y)) x =
      -(c ^ 4 / (8 * Real.pi * G)) *
        ∑ μ, pd μ (fun y => tetradDet h y * torsionVectorUp h μ y) x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun μ _ => tpx_pd_const_mul (hdV μ) _ μ)
  have hP : ∑ t, ∑ n, invMetric h x t n *
        ∑ r, (pd r (contortion h r t n) x - pd n (contortion h r t r) x) =
      ∑ r, ∑ t, ∑ n, invMetric h x t n * pd r (contortion h r t n) x
        - ∑ n, ∑ t, invMetric h x t n * ∑ r, pd n (contortion h r t r) x := by
    simp only [Fin.sum_univ_four]; ring
  unfold teleparallelLagrangian einsteinHilbertLagrangian
  rw [hsq, hsum, tpx_div h hh x, tpx_core h hh x, tpx_scalar h hh x, hP]
  ring