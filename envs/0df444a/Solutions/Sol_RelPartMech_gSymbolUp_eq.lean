-- Prove2me | solution 1 for RelPartMech.gSymbolUp_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:41:05.272489+00:00
-- url     : https://prove2.me/submissions/dbb25e49-1a5a-4075-91c6-76b56dab1828

import Mathlib
import Definitions.Def_RelPartMech_coordinates
open scoped ContDiff
open RelPartMech

namespace RPAux

lemma pdp_const {n : ℕ} (f : Coord n → ℝ) (μ : Fin n) (x p : Coord n) :
    pdp μ (fun y _ => f y) x p = 0 := by
  simp [pdp]

lemma pdq_const {n : ℕ} (f : Coord n → ℝ) (μ : Fin n) (x p : Coord n) :
    pdq μ (fun y _ => f y) x p = pd μ f x := rfl

lemma pdp_kin {n : ℕ} (A : CovectorField n) (e : ℝ) (β μ : Fin n) (x p : Coord n) :
    pdp μ (kineticMomentum A e β) x p = (Pi.single μ (1:ℝ) : Coord n) β := by
  unfold pdp kineticMomentum
  have h : HasFDerivAt (fun r : Coord n => r β - e * A β x) (ContinuousLinearMap.proj β) p :=
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) β p).sub_const (e * A β x)
  rw [h.fderiv]; rfl

lemma pdq_kin {n : ℕ} (A : CovectorField n) (e : ℝ) (β μ : Fin n) (x p : Coord n)
    (hA : DifferentiableAt ℝ (A β) x) :
    pdq μ (kineticMomentum A e β) x p = -(e * pd μ (A β) x) := by
  unfold pdq kineticMomentum pd
  have h : HasFDerivAt (fun y : Coord n => p β - e * A β y) (-(e • fderiv ℝ (A β) x)) x := by
    have := (hA.hasFDerivAt.const_mul e).const_sub (p β)
    simpa using this
  rw [h.fderiv]; simp

lemma pdq_pos {n : ℕ} (α μ : Fin n) (x p : Coord n) :
    pdq μ (posFn α) x p = (Pi.single μ (1:ℝ) : Coord n) α := by
  unfold pdq posFn
  rw [(hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) α x).fderiv]; rfl

lemma pdp_pos {n : ℕ} (α μ : Fin n) (x p : Coord n) :
    pdp μ (posFn α) x p = 0 := by
  simp [pdp, posFn]

lemma sum_single {n : ℕ} (β : Fin n) (c : Fin n → ℝ) :
    ∑ μ, c μ * (Pi.single μ (1:ℝ) : Coord n) β = c β := by
  simp [Pi.single_apply]

end RPAux

namespace RPAux

lemma ginv_symm {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (x : Coord n) (i j : Fin n) :
    ginv g x i j = ginv g x j i := by
  have ht : Matrix.transpose (g x) = g x := by ext a b; exact hg.2.1 x b a
  have : Matrix.transpose (ginv g x) = ginv g x := by
    unfold ginv; rw [Matrix.transpose_nonsing_inv, ht]
  have h := congrFun (congrFun this j) i
  rw [Matrix.transpose_apply] at h
  exact h

lemma hasFDeriv_kin_p {n : ℕ} (A : CovectorField n) (e : ℝ) (β : Fin n) (x p : Coord n) :
    HasFDerivAt (fun r => kineticMomentum A e β x r) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) β) p :=
  (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) β p).sub_const (e * A β x)

lemma pdp_ham {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (A : CovectorField n)
    (e m : ℝ) (α : Fin n) (x p : Coord n) :
    pdp α (hamiltonian g A e m) x p = (1 / m) * ∑ β, ginv g x α β * kineticMomentum A e β x p := by
  unfold pdp hamiltonian
  have hK := fun β => hasFDeriv_kin_p A e β x p
  have h : HasFDerivAt (fun r => 1 / (2 * m) * ∑ β, ∑ γ,
      kineticMomentum A e β x r * ginv g x β γ * kineticMomentum A e γ x r) _ p := (HasFDerivAt.fun_sum (u := Finset.univ) (fun β _ => HasFDerivAt.fun_sum (u := Finset.univ)
    (fun γ _ => ((hK β).mul_const (ginv g x β γ)).mul (hK γ)))).const_mul (1 / (2 * m))
  rw [h.fderiv]
  simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_sum', ContinuousLinearMap.add_apply, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul, ContinuousLinearMap.proj_apply]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun x_1 x_2 => if x_1 = α then kineticMomentum A e x_2 x p * ginv g x x_1 x_2 else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have : ∀ β, kineticMomentum A e β x p * ginv g x β α = ginv g x α β * kineticMomentum A e β x p := by
    intro β; rw [ginv_symm g hg x β α]; ring
  simp only [this]
  have e2 : ∀ β, kineticMomentum A e β x p * ginv g x α β = ginv g x α β * kineticMomentum A e β x p :=
    fun β => mul_comm _ _
  simp only [e2]
  by_cases hm : m = 0
  · simp [hm]
  · field_simp; ring

end RPAux

namespace RPAux

lemma poisson_pos {n : ℕ} (α : Fin n) (h : PhaseFn n) (x p : Coord n) :
    poisson (posFn α) h x p = pdp α h x p := by
  unfold poisson
  simp only [pdq_pos, pdp_pos, zero_mul, sub_zero]
  rw [← sum_single α (fun μ => pdp μ h x p)]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma pdp_vel {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (A : CovectorField n)
    (e m : ℝ) (α β : Fin n) (x p : Coord n) :
    pdp α (velocity g A e m β) x p = (1 / m) * ginv g x α β := by
  unfold pdp velocity
  have hK := fun β => hasFDeriv_kin_p A e β x p
  have h : HasFDerivAt (fun r => (1 / m) * ∑ γ, ginv g x β γ * kineticMomentum A e γ x r) _ p :=
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun γ _ => (hK γ).const_mul (ginv g x β γ))).const_mul (1 / m)
  rw [h.fderiv]
  simp [Pi.single_apply, ginv_symm g hg x β α]

end RPAux

namespace RPAux

lemma det_contDiff {n : ℕ} {k : WithTop ℕ∞} (M : Coord n → Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i j, ContDiff ℝ k (fun x => M x i j)) : ContDiff ℝ k (fun x => (M x).det) := by
  simp only [Matrix.det_apply]
  apply ContDiff.sum (fun σ _ => ?_)
  apply ContDiff.const_smul
  exact contDiff_prod (fun i _ => h _ _)

lemma ginv_contDiff {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (i j : Fin n) :
    ContDiff ℝ ∞ (fun x => ginv g x i j) := by
  unfold ginv
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  apply ContDiff.mul
  · apply ContDiff.inv (det_contDiff _ hg.1)
    intro x; exact (hg.2.2 x).ne_zero
  · apply det_contDiff
    intro k l
    simp only [Matrix.updateRow_apply]
    by_cases hk : k = j
    · simp only [hk, if_true]; exact contDiff_const
    · simp only [hk, if_false]; exact hg.1 k l

lemma pd_eq_of_hasFDerivAt {n : ℕ} {f : Coord n → ℝ} {f' : Coord n →L[ℝ] ℝ} {x : Coord n}
    (h : HasFDerivAt f f' x) (α : Fin n) : pd α f x = f' (Pi.single α 1) := by
  unfold pd; rw [h.fderiv]

end RPAux

open RPAux in
theorem inv_metric_deriv' {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (α β γ : Fin n) (x : Coord n) :
    pd α (fun y => ginv g y β γ) x =
      -∑ δ, ∑ ε, ginv g x β δ * ginv g x γ ε * pd α (fun y => g y δ ε) x := by
  set G := g x
  set Gi := ginv g x
  set P : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => pd α (fun y => g y i j) x
  set D : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => pd α (fun y => ginv g y i j) x
  have hgd : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x :=
    fun i j => ((hg.1 i j).differentiable (by simp)) x
  have hid : ∀ i j, DifferentiableAt ℝ (fun y => ginv g y i j) x :=
    fun i j => ((ginv_contDiff g hg i j).differentiable (by simp)) x
  have hPD : P * Gi + G * D = 0 := by
    ext δ γ
    have hconst : ∀ y, ∑ ε, g y δ ε * ginv g y ε γ = (1 : Matrix (Fin n) (Fin n) ℝ) δ γ := by
      intro y
      have := Matrix.mul_nonsing_inv (g y) (hg.2.2 y)
      have h2 := congrFun (congrFun this δ) γ
      rw [Matrix.mul_apply] at h2
      exact h2
    have hder : HasFDerivAt (fun y => ∑ ε, g y δ ε * ginv g y ε γ) _ x := HasFDerivAt.fun_sum (u := Finset.univ)
      (fun ε _ => (hgd δ ε).hasFDerivAt.mul (hid ε γ).hasFDerivAt)
    have h0 := pd_eq_of_hasFDerivAt hder α
    have hc : (fun y => ∑ ε, g y δ ε * ginv g y ε γ) = fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) δ γ :=
      funext hconst
    have hz : pd α (fun y => ∑ ε, g y δ ε * ginv g y ε γ) x = 0 := by
      rw [hc]; simp [pd]
    rw [hz] at h0
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply, P, D, Matrix.of_apply, G, Gi,
      ← Finset.sum_add_distrib]
    rw [h0]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, pd]
    refine Finset.sum_congr rfl (fun ε _ => ?_)
    ring
  have hGiG : Gi * G = 1 := Matrix.nonsing_inv_mul (g x) (hg.2.2 x)
  have hD : D = -(Gi * P * Gi) := by
    have : D = Gi * (G * D) := by rw [← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    rw [this, eq_neg_iff_add_eq_zero, Matrix.mul_assoc, ← Matrix.mul_add, add_comm, hPD, Matrix.mul_zero]
  have h := congrFun (congrFun hD β) γ
  simp only [D, Matrix.of_apply, Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul] at h
  rw [h, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun δ _ => Finset.sum_congr rfl (fun ε _ => ?_))
  simp only [P, Matrix.of_apply, Gi]
  rw [ginv_symm g hg x ε γ]
  ring

theorem solution {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (α β γ : Fin n) (x : Coord n) :
    gSymbolUp g α β γ x =
      pdUp g β (fun y => ginv g y α γ) x - pdUp g α (fun y => ginv g y β γ) x := by
  unfold pdUp gSymbolUp gSymbol
  simp only [inv_metric_deriv' g hg, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add, Finset.mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [neg_add_eq_sub]
  congr 1
  · -- ∑ δ ε ζ, gαδ gβε gγζ ∂δ g εζ  =  ∑ ε, gαε ∑ δ ζ, gβδ gγζ ∂ε gδζ
    refine Finset.sum_congr rfl (fun δ _ => Finset.sum_congr rfl (fun ε _ => Finset.sum_congr rfl (fun ζ _ => ?_)))
    ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun δ _ => ?_)
    refine Finset.sum_congr rfl (fun ε _ => Finset.sum_congr rfl (fun ζ _ => ?_))
    ring
