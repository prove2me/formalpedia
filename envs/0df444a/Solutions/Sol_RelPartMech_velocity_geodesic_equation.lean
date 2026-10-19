-- Prove2me | solution 1 for RelPartMech.velocity_geodesic_equation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:06:17.272807+00:00
-- url     : https://prove2.me/submissions/46dcea93-0076-4627-840f-f73430433abb

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

namespace RPAux

lemma gSymbolUp_eq' {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (α β γ : Fin n) (x : Coord n) :
    gSymbolUp g α β γ x =
      pdUp g β (fun y => ginv g y α γ) x - pdUp g α (fun y => ginv g y β γ) x := by
  unfold pdUp gSymbolUp gSymbol
  simp only [inv_metric_deriv' g hg, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add, Finset.mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [neg_add_eq_sub]
  congr 1
  · refine Finset.sum_congr rfl (fun δ _ => Finset.sum_congr rfl (fun ε _ => Finset.sum_congr rfl (fun ζ _ => ?_)))
    ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun δ _ => ?_)
    refine Finset.sum_congr rfl (fun ε _ => Finset.sum_congr rfl (fun ζ _ => ?_))
    ring

lemma pd_raise {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (A : CovectorField n)
    (hA : ∀ α, ContDiff ℝ ∞ (A α)) (ε β : Fin n) (x : Coord n) :
    pd ε (raise g A β) x = ∑ ζ, (pd ε (fun y => ginv g y β ζ) x * A ζ x + ginv g x β ζ * pd ε (A ζ) x) := by
  have hid : ∀ i j, DifferentiableAt ℝ (fun y => ginv g y i j) x :=
    fun i j => ((ginv_contDiff g hg i j).differentiable (by simp)) x
  have hAd : ∀ ζ, DifferentiableAt ℝ (A ζ) x := fun ζ => ((hA ζ).differentiable (by simp)) x
  have h : HasFDerivAt (raise g A β) _ x := HasFDerivAt.fun_sum (u := Finset.univ)
      (fun ζ _ => (hid β ζ).hasFDerivAt.mul (hAd ζ).hasFDerivAt)
  rw [pd_eq_of_hasFDerivAt h]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, pd]
  refine Finset.sum_congr rfl (fun ζ _ => ?_)
  ring

lemma pdUp_raise {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (A : CovectorField n)
    (hA : ∀ α, ContDiff ℝ ∞ (A α)) (α β : Fin n) (x : Coord n) :
    pdUp g α (raise g A β) x = ∑ ζ, pdUp g α (fun y => ginv g y β ζ) x * A ζ x
      + ∑ ε, ∑ ζ, ginv g x α ε * ginv g x β ζ * pd ε (A ζ) x := by
  unfold pdUp
  simp only [pd_raise g hg A hA, Finset.mul_sum, Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ζ _ => Finset.sum_congr rfl (fun ε _ => ?_))
    ring
  · refine Finset.sum_congr rfl (fun ε _ => Finset.sum_congr rfl (fun ζ _ => ?_))
    ring

end RPAux

open RPAux in
theorem forceTensorUp_eq' {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α)) (α β : Fin n) (x : Coord n) :
    forceTensorUp g A α β x =
      pdUp g α (raise g A β) x - pdUp g β (raise g A α) x
        + ∑ γ, gSymbolUp g α β γ x * A γ x := by
  rw [pdUp_raise g hg A hA, pdUp_raise g hg A hA]
  simp only [gSymbolUp_eq' g hg, sub_mul, Finset.sum_sub_distrib]
  unfold forceTensorUp forceTensor
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hswap : ∑ γ, ∑ δ, ginv g x α γ * ginv g x β δ * pd δ (A γ) x
      = ∑ ε, ∑ ζ, ginv g x β ε * ginv g x α ζ * pd ε (A ζ) x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ε _ => Finset.sum_congr rfl (fun ζ _ => ?_))
    ring
  rw [hswap]
  ring

namespace RPAux

lemma christ_diff {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (γ μ δ : Fin n) (x : Coord n) :
    christoffelFirst g μ δ γ x - christoffelFirst g γ δ μ x
      = pd γ (fun y => g y μ δ) x - pd μ (fun y => g y γ δ) x := by
  have h1 : (fun y => g y δ γ) = (fun y => g y γ δ) := funext fun y => hg.2.1 y δ γ
  have h2 : (fun y => g y γ μ) = (fun y => g y μ γ) := funext fun y => hg.2.1 y γ μ
  have h3 : (fun y => g y δ μ) = (fun y => g y μ δ) := funext fun y => hg.2.1 y δ μ
  simp only [christoffelFirst, h1, h2, h3]
  ring

/-- the connection terms -/
lemma conn_terms {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (A : CovectorField n)
    (α β : Fin n) (x : Coord n) :
    ∑ γ, ginv g x α γ * ∑ δ, christoffel g β δ γ x * raise g A δ x
      - ∑ γ, ginv g x β γ * ∑ δ, christoffel g α δ γ x * raise g A δ x
      = ∑ ζ, gSymbolUp g α β ζ x * A ζ x := by
  -- normal form: ∑ γ μ δ ζ
  have L1 : ∑ γ, ginv g x α γ * ∑ δ, christoffel g β δ γ x * raise g A δ x
      = ∑ γ, ∑ μ, ∑ δ, ∑ ζ, ginv g x α γ * ginv g x β μ * ginv g x δ ζ
          * christoffelFirst g μ δ γ x * A ζ x := by
    unfold christoffel raise
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_lhs => enter [2, γ, 2, δ]; rw [Finset.sum_comm]
    conv_lhs => enter [2, γ]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun γ _ => Finset.sum_congr rfl (fun μ _ =>
      Finset.sum_congr rfl (fun δ _ => Finset.sum_congr rfl (fun ζ _ => ?_))))
    ring
  have L2 : ∑ γ, ginv g x β γ * ∑ δ, christoffel g α δ γ x * raise g A δ x
      = ∑ γ, ∑ μ, ∑ δ, ∑ ζ, ginv g x α γ * ginv g x β μ * ginv g x δ ζ
          * christoffelFirst g γ δ μ x * A ζ x := by
    unfold christoffel raise
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_lhs => enter [2, γ, 2, δ]; rw [Finset.sum_comm]
    conv_lhs => enter [2, γ]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun γ _ => Finset.sum_congr rfl (fun μ _ =>
      Finset.sum_congr rfl (fun δ _ => Finset.sum_congr rfl (fun ζ _ => ?_))))
    ring
  have R : ∑ ζ, gSymbolUp g α β ζ x * A ζ x
      = ∑ γ, ∑ μ, ∑ δ, ∑ ζ, ginv g x α γ * ginv g x β μ * ginv g x δ ζ
          * (pd γ (fun y => g y μ δ) x - pd μ (fun y => g y γ δ) x) * A ζ x := by
    unfold gSymbolUp gSymbol
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun δ _ => Finset.sum_congr rfl (fun ζ _ => ?_))
    rw [ginv_symm g hg x ζ δ]
  rw [L1, L2, R, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun ζ _ => ?_)
  rw [← christ_diff g hg γ μ δ x]
  ring

end RPAux

namespace RPAux

lemma hasFDeriv_kin_q {n : ℕ} (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e : ℝ)
    (β : Fin n) (x p : Coord n) :
    HasFDerivAt (fun y => kineticMomentum A e β y p) (-(e • fderiv ℝ (A β) x)) x := by
  have hAd : DifferentiableAt ℝ (A β) x := ((hA β).differentiable (by simp)) x
  have := (hAd.hasFDerivAt.const_mul e).const_sub (p β)
  simpa [kineticMomentum] using this

/-- `∂H/∂q^α` -/
lemma pdq_ham {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (A : CovectorField n)
    (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e m : ℝ) (α : Fin n) (x p : Coord n) :
    pdq α (hamiltonian g A e m) x p = (1 / (2 * m)) * ∑ β, ∑ γ,
      (-(e * pd α (A β) x) * ginv g x β γ * kineticMomentum A e γ x p
        + kineticMomentum A e β x p * pd α (fun y => ginv g y β γ) x * kineticMomentum A e γ x p
        + kineticMomentum A e β x p * ginv g x β γ * -(e * pd α (A γ) x)) := by
  have hid : ∀ i j, DifferentiableAt ℝ (fun y => ginv g y i j) x :=
    fun i j => ((ginv_contDiff g hg i j).differentiable (by simp)) x
  have hK := fun β => hasFDeriv_kin_q A hA e β x p
  have h : HasFDerivAt (fun y => hamiltonian g A e m y p) _ x :=
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun β _ => HasFDerivAt.fun_sum (u := Finset.univ)
      (fun γ _ => ((hK β).mul (hid β γ).hasFDerivAt).mul (hK γ)))).const_mul (1 / (2 * m))
  unfold pdq
  rw [h.fderiv]
  simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.add_apply, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.neg_apply, pd]
  congr 1
  refine Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun γ _ => ?_))
  simp only [Pi.mul_apply]
  ring

end RPAux

open RPAux in
theorem goal' {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e m : ℝ) (hm : m ≠ 0)
    (α : Fin n) (x p : Coord n) :
    poisson (kineticMomentum A e α) (hamiltonian g A e m) x p
      - ∑ δ, ∑ γ, poisson (posFn δ) (hamiltonian g A e m) x p * christoffel g γ δ α x
          * kineticMomentum A e γ x p =
      (e / m) * ∑ β, ∑ γ, forceTensor A α β x * ginv g x β γ * kineticMomentum A e γ x p := by
  set P : Fin n → ℝ := fun β => kineticMomentum A e β x p with hP
  set u : Fin n → ℝ := fun δ => ∑ β, ginv g x δ β * P β with hu
  set dA : Fin n → Fin n → ℝ := fun μ β => pd μ (A β) x with hdA
  set dg : Fin n → Fin n → ℝ := fun δ ε => pd α (fun y => g y δ ε) x with hdg
  have hAd : ∀ γ, DifferentiableAt ℝ (A γ) x := fun γ => ((hA γ).differentiable (by simp)) x
  -- step 1
  have s1 : poisson (kineticMomentum A e α) (hamiltonian g A e m) x p
      = -(e / m) * ∑ μ, dA μ α * u μ - pdq α (hamiltonian g A e m) x p := by
    unfold poisson
    simp only [pdp_kin, pdq_kin A e _ _ x p (hAd _), pdp_ham g hg, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun μ _ => ?_)
      simp only [hu, hdA, hP]; ring
    · rw [← sum_single α (fun μ => pdq μ (hamiltonian g A e m) x p)]
      exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  -- step 2
  have s2a : ∑ β, ∑ γ, -(e * pd α (A β) x) * ginv g x β γ * P γ = -e * ∑ β, dA α β * u β := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun β _ => ?_)
    simp only [hu, hdA, Finset.mul_sum]; refine Finset.sum_congr rfl (fun γ _ => ?_); ring
  have s2b : ∑ β, ∑ γ, P β * ginv g x β γ * -(e * pd α (A γ) x) = -e * ∑ β, dA α β * u β := by
    rw [Finset.sum_comm, Finset.mul_sum]; refine Finset.sum_congr rfl (fun γ _ => ?_)
    simp only [hu, hdA, Finset.mul_sum]; refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [ginv_symm g hg x β γ]; ring
  have s2c : ∑ β, ∑ γ, P β * pd α (fun y => ginv g y β γ) x * P γ
      = -∑ δ, ∑ ε, u δ * u ε * dg δ ε := by
    simp only [inv_metric_deriv' g hg, hu, hdg, Finset.sum_mul, Finset.mul_sum, mul_neg, neg_mul,
      Finset.sum_neg_distrib]
    congr 1
    conv_lhs => enter [2, β]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => enter [2, δ, 2, β]; rw [Finset.sum_comm]
    conv_lhs => enter [2, δ]; rw [Finset.sum_comm]
    conv_lhs => enter [2, δ, 2, ε]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun δ _ => Finset.sum_congr rfl (fun ε _ =>
      Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun γ _ => ?_))))
    rw [ginv_symm g hg x γ δ, ginv_symm g hg x β ε]
    ring
  have s2 : pdq α (hamiltonian g A e m) x p
      = (1 / (2 * m)) * (-e * ∑ β, dA α β * u β + -∑ δ, ∑ ε, u δ * u ε * dg δ ε + -e * ∑ β, dA α β * u β) := by
    rw [pdq_ham g hg A hA]
    simp only [Finset.sum_add_distrib]
    rw [s2a, s2b, s2c]
  -- step 3
  have s3a : ∑ δ, ∑ γ, poisson (posFn δ) (hamiltonian g A e m) x p * christoffel g γ δ α x
          * kineticMomentum A e γ x p
      = (1 / m) * ∑ δ, ∑ μ, u δ * u μ * christoffelFirst g μ δ α x := by
    simp only [poisson_pos, pdp_ham g hg, christoffel, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun δ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    simp only [hu, hP, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun γ _ => ?_))
    rw [ginv_symm g hg x β μ]
    ring
  have s3b : ∑ δ, ∑ μ, u δ * u μ * christoffelFirst g μ δ α x
      = (1 / 2) * ∑ δ, ∑ ε, u δ * u ε * dg δ ε := by
    have hsym : ∀ δ μ, (fun y => g y μ δ) = (fun y => g y δ μ) := fun δ μ => funext fun y => hg.2.1 y μ δ
    have hsw : ∑ δ, ∑ μ, u δ * u μ * pd δ (fun y => g y μ α) x
        = ∑ δ, ∑ μ, u δ * u μ * pd μ (fun y => g y δ α) x := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    have e1 : ∀ δ μ, u δ * u μ * christoffelFirst g μ δ α x
        = (1 / 2) * (u δ * u μ * dg δ μ) + (1 / 2) * (u δ * u μ * pd δ (fun y => g y μ α) x)
          - (1 / 2) * (u δ * u μ * pd μ (fun y => g y δ α) x) := by
      intro δ μ
      simp only [christoffelFirst, hdg, hsym δ μ]
      simp only [hsym α δ]
      ring
    simp only [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsw]
    ring
  rw [s1, s3a, s3b, s2]
  unfold forceTensor
  have hR : ∑ β, ∑ γ, (pd α (A β) x - pd β (A α) x) * ginv g x β γ * kineticMomentum A e γ x p
      = ∑ β, dA α β * u β - ∑ μ, dA μ α * u μ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    simp only [hu, hP, hdA, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    ring
  rw [hR]
  field_simp
  ring


namespace RPAux

lemma pdq_vel {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (A : CovectorField n)
    (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e m : ℝ) (α μ : Fin n) (x p : Coord n) :
    pdq μ (velocity g A e m α) x p = (1 / m) * ∑ γ,
      (pd μ (fun y => ginv g y α γ) x * kineticMomentum A e γ x p
        + ginv g x α γ * -(e * pd μ (A γ) x)) := by
  have hid : ∀ i j, DifferentiableAt ℝ (fun y => ginv g y i j) x :=
    fun i j => ((ginv_contDiff g hg i j).differentiable (by simp)) x
  have hK := fun β => hasFDeriv_kin_q A hA e β x p
  have h : HasFDerivAt (fun y => velocity g A e m α y p) _ x :=
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun γ _ => (hid α γ).hasFDerivAt.mul (hK γ))).const_mul (1 / m)
  unfold pdq
  rw [h.fderiv]
  simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.add_apply, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.neg_apply, pd]
  congr 1
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  ring

lemma poisson_vel {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e m : ℝ) (hm : m ≠ 0)
    (α β : Fin n) (x p : Coord n) :
    poisson (velocity g A e m α) (velocity g A e m β) x p =
      (1 / m ^ 2) * (∑ γ, gSymbolUp g α β γ x * kineticMomentum A e γ x p + e * forceTensorUp g A α β x) := by
  unfold poisson
  simp only [pdp_vel g hg, pdq_vel g hg A hA]
  simp only [gSymbolUp_eq' g hg, forceTensorUp, forceTensor, pdUp]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib, mul_sub, sub_mul,
    Finset.sum_sub_distrib]
  have hm2 : (1 / m ^ 2) = 1 / m * (1 / m) := by ring
  have t1 : ∑ μ, ∑ i, 1 / m * (pd μ (fun y => ginv g y α i) x * kineticMomentum A e i x p) * (1 / m * ginv g x μ β)
      = ∑ γ, ∑ i, 1 / m ^ 2 * (ginv g x β i * pd i (fun y => ginv g y α γ) x * kineticMomentum A e γ x p) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun γ _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [ginv_symm g hg x i β, hm2]; ring
  have t2 : ∑ μ, ∑ i, 1 / m * ginv g x μ α * (1 / m * (pd μ (fun y => ginv g y β i) x * kineticMomentum A e i x p))
      = ∑ γ, ∑ i, 1 / m ^ 2 * (ginv g x α i * pd i (fun y => ginv g y β γ) x * kineticMomentum A e γ x p) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun γ _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [ginv_symm g hg x i α, hm2]; ring
  have t3 : ∑ μ, ∑ i, 1 / m * (ginv g x α i * -(e * pd μ (A i) x)) * (1 / m * ginv g x μ β)
      = -∑ γ, ∑ i, 1 / m ^ 2 * (e * (ginv g x α γ * ginv g x β i * pd i (A γ) x)) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ginv_symm g hg x i β, hm2]; ring
  have t4 : ∑ μ, ∑ i, 1 / m * ginv g x μ α * (1 / m * (ginv g x β i * -(e * pd μ (A i) x)))
      = -∑ γ, ∑ i, 1 / m ^ 2 * (e * (ginv g x α γ * ginv g x β i * pd γ (A i) x)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ginv_symm g hg x γ α, hm2]; ring
  rw [t1, t2, t3, t4]
  ring

end RPAux

namespace RPAux

lemma g_vel {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (e m : ℝ) (hm : m ≠ 0) (γ : Fin n) (x p : Coord n) :
    ∑ δ, m * g x γ δ * velocity g A e m δ x p = kineticMomentum A e γ x p := by
  unfold velocity
  have hinv := Matrix.mul_nonsing_inv (g x) (hg.2.2 x)
  have e1 : ∀ δ, m * g x γ δ * (1 / m * ∑ β, ginv g x δ β * kineticMomentum A e β x p)
      = ∑ β, g x γ δ * ginv g x δ β * kineticMomentum A e β x p := by
    intro δ; rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun β _ => ?_); field_simp
  simp only [e1]
  rw [Finset.sum_comm]
  have e2 : ∀ β, ∑ δ, g x γ δ * ginv g x δ β * kineticMomentum A e β x p
      = (g x * ginv g x) γ β * kineticMomentum A e β x p := by
    intro β; rw [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun β _ => e2 β)]
  simp only [ginv, hinv, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end RPAux

open RPAux in
theorem poisson_velocities' {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e m : ℝ) (hm : m ≠ 0)
    (α β : Fin n) (x p : Coord n) :
    poisson (velocity g A e m α) (velocity g A e m β) x p =
      (1 / m ^ 2) * (∑ γ, ∑ δ, gSymbolUp g α β γ x * m * g x γ δ * velocity g A e m δ x p
        + e * forceTensorUp g A α β x) := by
  rw [poisson_vel g hg A hA e m hm]
  congr 2
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [← g_vel g hg A e m hm γ x p, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  ring

namespace RPAux

lemma pdq_ham' {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (A : CovectorField n)
    (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e m : ℝ) (α : Fin n) (x p : Coord n) :
    pdq α (hamiltonian g A e m) x p = (1 / (2 * m)) *
      (-(2 * e) * ∑ β, pd α (A β) x * (∑ γ, ginv g x β γ * kineticMomentum A e γ x p)
        - ∑ δ, ∑ ε, (∑ β, ginv g x δ β * kineticMomentum A e β x p)
            * (∑ β, ginv g x ε β * kineticMomentum A e β x p) * pd α (fun y => g y δ ε) x) := by
  set P : Fin n → ℝ := fun β => kineticMomentum A e β x p with hP
  set u : Fin n → ℝ := fun δ => ∑ β, ginv g x δ β * P β with hu
  have s2a : ∑ β, ∑ γ, -(e * pd α (A β) x) * ginv g x β γ * kineticMomentum A e γ x p
      = -e * ∑ β, pd α (A β) x * u β := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun β _ => ?_)
    simp only [hu, hP, Finset.mul_sum]; refine Finset.sum_congr rfl (fun γ _ => ?_); ring
  have s2b : ∑ β, ∑ γ, kineticMomentum A e β x p * ginv g x β γ * -(e * pd α (A γ) x)
      = -e * ∑ β, pd α (A β) x * u β := by
    rw [Finset.sum_comm, Finset.mul_sum]; refine Finset.sum_congr rfl (fun γ _ => ?_)
    simp only [hu, hP, Finset.mul_sum]; refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [ginv_symm g hg x β γ]; ring
  have s2c : ∑ β, ∑ γ, kineticMomentum A e β x p * pd α (fun y => ginv g y β γ) x * kineticMomentum A e γ x p
      = -∑ δ, ∑ ε, u δ * u ε * pd α (fun y => g y δ ε) x := by
    simp only [inv_metric_deriv' g hg, hu, hP, Finset.sum_mul, Finset.mul_sum, mul_neg, neg_mul,
      Finset.sum_neg_distrib]
    congr 1
    conv_lhs => enter [2, β]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => enter [2, δ, 2, β]; rw [Finset.sum_comm]
    conv_lhs => enter [2, δ]; rw [Finset.sum_comm]
    conv_lhs => enter [2, δ, 2, ε]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun δ _ => Finset.sum_congr rfl (fun ε _ =>
      Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun γ _ => ?_))))
    rw [ginv_symm g hg x γ δ, ginv_symm g hg x β ε]
    ring
  rw [pdq_ham g hg A hA]
  simp only [Finset.sum_add_distrib]
  rw [s2a, s2b, s2c]
  ring

end RPAux

open RPAux in
theorem velocity_geodesic' {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e m : ℝ) (hm : m ≠ 0)
    (α : Fin n) (x p : Coord n) :
    poisson (velocity g A e m α) (hamiltonian g A e m) x p
      + ∑ β, ∑ γ, velocity g A e m β x p * poisson (posFn γ) (hamiltonian g A e m) x p
          * christoffel g α β γ x =
      (e / m) * ∑ γ, ∑ β, forceTensorUp g A α γ x * g x γ β * velocity g A e m β x p := by
  obtain ⟨P, hP⟩ : ∃ P : Fin n → ℝ, P = fun β => kineticMomentum A e β x p := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Fin n → ℝ, U = fun δ => ∑ β, ginv g x δ β * P β := ⟨_, rfl⟩
  obtain ⟨dA, hdA⟩ : ∃ dA : Fin n → Fin n → ℝ, dA = fun μ β => pd μ (A β) x := ⟨_, rfl⟩
  obtain ⟨dg, hdg⟩ : ∃ dg : Fin n → Fin n → Fin n → ℝ, dg = fun μ δ ε => pd μ (fun y => g y δ ε) x :=
    ⟨_, rfl⟩
  have hvel : ∀ δ, velocity g A e m δ x p = (1 / m) * U δ := fun δ => by rw [hU, hP]; rfl
  have hpos : ∀ γ, poisson (posFn γ) (hamiltonian g A e m) x p = (1 / m) * U γ := by
    intro γ; rw [poisson_pos, pdp_ham g hg, hU, hP]
  have hsg : ∀ κ δ ε, dg κ δ ε = dg κ ε δ := fun κ δ ε => by
    simp only [hdg]; rw [show (fun y => g y δ ε) = (fun y => g y ε δ) from funext fun y => hg.2.1 y δ ε]
  -- A1
  have A1 : ∑ μ, ((1 / m) * ∑ γ, (pd μ (fun y => ginv g y α γ) x * kineticMomentum A e γ x p
        + ginv g x α γ * -(e * pd μ (A γ) x))) * ((1 / m) * U μ)
      = (1 / m ^ 2) * (-∑ κ, ginv g x α κ * ∑ μ, ∑ ℓ, dg μ κ ℓ * U ℓ * U μ)
        - (e / m ^ 2) * ∑ κ, ginv g x α κ * ∑ μ, dA μ κ * U μ := by
    have inner : ∀ μ, ∑ γ, pd μ (fun y => ginv g y α γ) x * kineticMomentum A e γ x p
        = -∑ κ, ginv g x α κ * ∑ ℓ, dg μ κ ℓ * U ℓ := by
      intro μ
      simp only [inv_metric_deriv' g hg, hU, hP, hdg, Finset.sum_mul, Finset.mul_sum, neg_mul,
        Finset.sum_neg_distrib, mul_neg]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun κ _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun ℓ _ => Finset.sum_congr rfl (fun γ _ => ?_))
      rw [ginv_symm g hg x γ ℓ]; ring
    have per : ∀ μ, ((1 / m) * ∑ γ, (pd μ (fun y => ginv g y α γ) x * kineticMomentum A e γ x p
        + ginv g x α γ * -(e * pd μ (A γ) x))) * ((1 / m) * U μ)
        = -((1 / m ^ 2) * ∑ κ, ∑ ℓ, ginv g x α κ * (dg μ κ ℓ * U ℓ * U μ))
          - (e / m ^ 2) * ∑ κ, ginv g x α κ * (dA μ κ * U μ) := by
      intro μ
      rw [Finset.sum_add_distrib, inner μ]
      have e1 : ∑ κ, ∑ ℓ, ginv g x α κ * (dg μ κ ℓ * U ℓ * U μ)
          = (∑ κ, ginv g x α κ * ∑ ℓ, dg μ κ ℓ * U ℓ) * U μ := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun κ _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl (fun ℓ _ => ?_); ring
      have e2 : ∑ κ, ginv g x α κ * (dA μ κ * U μ) = (∑ γ, ginv g x α γ * pd μ (A γ) x) * U μ := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun κ _ => ?_); simp only [hdA]; ring
      have e3 : ∑ γ, ginv g x α γ * -(e * pd μ (A γ) x) = -e * ∑ γ, ginv g x α γ * pd μ (A γ) x := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun κ _ => ?_); ring
      rw [e1, e2, e3]
      field_simp
      ring
    have c1 : ∑ μ, ∑ κ, ∑ ℓ, ginv g x α κ * (dg μ κ ℓ * U ℓ * U μ)
        = ∑ κ, ginv g x α κ * ∑ μ, ∑ ℓ, dg μ κ ℓ * U ℓ * U μ := by
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun κ _ => ?_)
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun μ _ => ?_)
      rw [Finset.mul_sum]
    have c2 : ∑ μ, ∑ κ, ginv g x α κ * (dA μ κ * U μ) = ∑ κ, ginv g x α κ * ∑ μ, dA μ κ * U μ := by
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun κ _ => ?_)
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun μ _ => per μ), Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, c1, c2]
    ring
  set X : Fin n → ℝ := fun κ => ∑ μ, ∑ ℓ, dg μ κ ℓ * U ℓ * U μ with hX
  set Y : Fin n → ℝ := fun κ => ∑ μ, dA μ κ * U μ with hY
  set Z : Fin n → ℝ := fun κ => ∑ β, dA κ β * U β with hZ
  set W : Fin n → ℝ := fun κ => ∑ δ, ∑ ε, U δ * U ε * dg κ δ ε with hW
  have hpdpH : ∀ μ, pdp μ (hamiltonian g A e m) x p = (1 / m) * U μ := by
    intro μ; rw [pdp_ham g hg, hU, hP]
  have hpdqH : ∀ μ, pdq μ (hamiltonian g A e m) x p = (1 / (2 * m)) * (-(2 * e) * Z μ - W μ) := by
    intro μ; rw [pdq_ham' g hg A hA, hZ, hW, hU, hP, hdA, hdg]
  have L : poisson (velocity g A e m α) (hamiltonian g A e m) x p
      = (1 / m ^ 2) * (-∑ κ, ginv g x α κ * X κ) - (e / m ^ 2) * ∑ κ, ginv g x α κ * Y κ
        - (1 / (2 * m ^ 2)) * (-(2 * e) * ∑ κ, ginv g x α κ * Z κ - ∑ κ, ginv g x α κ * W κ) := by
    unfold poisson
    simp only [pdq_vel g hg A hA, pdp_vel g hg, hpdpH, hpdqH, Finset.sum_sub_distrib]
    rw [A1]
    congr 1
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun κ _ => ?_)
    rw [ginv_symm g hg x κ α]
    field_simp
  have A4 : ∀ κ, ∑ β, ∑ γ, U β * U γ * christoffelFirst g κ β γ x = X κ - (1 / 2) * W κ := by
    intro κ
    have e1 : ∀ β γ, U β * U γ * christoffelFirst g κ β γ x
        = (1 / 2) * (U β * U γ * dg γ κ β) + (1 / 2) * (U β * U γ * dg β κ γ)
          - (1 / 2) * (U β * U γ * dg κ β γ) := by
      intro β γ; simp only [christoffelFirst, hdg]; ring
    simp only [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hX, hW]
    have s1 : ∑ β, ∑ γ, U β * U γ * dg γ κ β = ∑ μ, ∑ ℓ, dg μ κ ℓ * U ℓ * U μ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun γ _ => ?_)); ring
    have s2 : ∑ β, ∑ γ, U β * U γ * dg β κ γ = ∑ μ, ∑ ℓ, dg μ κ ℓ * U ℓ * U μ := by
      refine Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun γ _ => ?_)); ring
    rw [s1, s2]; ring
  have A3 : ∑ β, ∑ γ, velocity g A e m β x p * poisson (posFn γ) (hamiltonian g A e m) x p
        * christoffel g α β γ x
      = (1 / m ^ 2) * ∑ κ, ginv g x α κ * (X κ - (1 / 2) * W κ) := by
    simp only [hvel, hpos, christoffel, ← A4, Finset.mul_sum]
    conv_lhs => enter [2, b]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun κ _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
    ring
  have hdelta : ∀ ℓ β, ∑ γ, ginv g x γ ℓ * g x γ β = if ℓ = β then 1 else 0 := by
    intro ℓ β
    have h := congrFun (congrFun (Matrix.nonsing_inv_mul (g x) (hg.2.2 x)) ℓ) β
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [ginv_symm g hg x γ ℓ]; rfl
  have A5 : (e / m) * ∑ γ, ∑ β, forceTensorUp g A α γ x * g x γ β * velocity g A e m β x p
      = (e / m ^ 2) * ∑ κ, ginv g x α κ * (Z κ - Y κ) := by
    have step : ∑ γ, ∑ β, forceTensorUp g A α γ x * g x γ β * velocity g A e m β x p
        = ∑ κ, ∑ ℓ, ∑ β, ginv g x α κ * forceTensor A κ ℓ x * ((1 / m) * U β)
            * ∑ γ, ginv g x γ ℓ * g x γ β := by
      unfold forceTensorUp
      simp only [hvel, Finset.sum_mul, Finset.mul_sum]
      -- LHS order γ β κ ℓ ; RHS κ ℓ β γ
      conv_lhs => enter [2, γ]; rw [Finset.sum_comm]
      conv_lhs => enter [2, γ, 2, κ]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      conv_lhs => enter [2, κ]; rw [Finset.sum_comm]
      conv_lhs => enter [2, κ, 2, γ]; rw [Finset.sum_comm]
      conv_lhs => enter [2, κ]; rw [Finset.sum_comm]
      conv_lhs => enter [2, κ, 2, ℓ]; rw [Finset.sum_comm]
      conv_lhs => enter [2, κ, 2, b]; rw [Finset.sum_comm]
      conv_lhs => enter [2, κ]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun κ _ => Finset.sum_congr rfl (fun ℓ _ =>
        Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun γ _ => ?_))))
      ring
    rw [step]
    simp only [hdelta, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [Finset.mul_sum, forceTensor, hZ, hY, hdA, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun κ _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    field_simp
  rw [L, A3, A5]
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hw : ∑ κ, ginv g x α κ * (1 / 2 * W κ) = (1 / 2) * ∑ κ, ginv g x α κ * W κ := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun κ _ => ?_); ring
  rw [hw]
  ring

theorem solution {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e m : ℝ) (hm : m ≠ 0)
    (α : Fin n) (x p : Coord n) :
    poisson (velocity g A e m α) (hamiltonian g A e m) x p
      + ∑ β, ∑ γ, velocity g A e m β x p * poisson (posFn γ) (hamiltonian g A e m) x p
          * christoffel g α β γ x =
      (e / m) * ∑ γ, ∑ β, forceTensorUp g A α γ x * g x γ β * velocity g A e m β x p :=
  velocity_geodesic' g hg A hA e m hm α x p
