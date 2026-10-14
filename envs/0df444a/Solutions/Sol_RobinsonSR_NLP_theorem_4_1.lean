-- Prove2me | solution 1 for RobinsonSR.NLP.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T06:23:49.693503+00:00
-- url     : https://prove2.me/submissions/f0186264-04a1-433d-b018-3cafde9d2344

import Mathlib
import Definitions.Def_RobinsonSR_NLP_Setting
open scoped RealInnerProductSpace Matrix


namespace RobinsonSR.NLP

section basics
variable {n p q : ℕ}

@[simp] lemma xPart_apply' (z : KKTSpace n p q) (k : Fin n) : xPart z k = z (Sum.inl k) := rfl
@[simp] lemma uPart_apply' (z : KKTSpace n p q) (k : Fin p) : uPart z k = z (Sum.inr (Sum.inl k)) := rfl
@[simp] lemma vPart_apply' (z : KKTSpace n p q) (k : Fin q) : vPart z k = z (Sum.inr (Sum.inr k)) := rfl
@[simp] lemma mk_inl (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) (k : Fin n) : mk x u v (Sum.inl k) = x k := rfl
@[simp] lemma mk_inrl (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) (k : Fin p) : mk x u v (Sum.inr (Sum.inl k)) = u k := rfl
@[simp] lemma mk_inrr (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) (k : Fin q) : mk x u v (Sum.inr (Sum.inr k)) = v k := rfl

lemma kkt_ext {z w : KKTSpace n p q} (hx : xPart z = xPart w) (hu : uPart z = uPart w)
    (hv : vPart z = vPart w) : z = w := by
  ext k
  rcases k with k | k | k
  · exact congrArg (fun t => t k) hx
  · exact congrArg (fun t => t k) hu
  · exact congrArg (fun t => t k) hv

@[simp] lemma xPart_mk (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) : xPart (mk x u v) = x := by ext k; simp
@[simp] lemma uPart_mk (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) : uPart (mk x u v) = u := by ext k; simp
@[simp] lemma vPart_mk (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) : vPart (mk x u v) = v := by ext k; simp

@[simp] lemma xPart_add (z w : KKTSpace n p q) : xPart (z + w) = xPart z + xPart w := by ext k; simp
@[simp] lemma uPart_add (z w : KKTSpace n p q) : uPart (z + w) = uPart z + uPart w := by ext k; simp
@[simp] lemma vPart_add (z w : KKTSpace n p q) : vPart (z + w) = vPart z + vPart w := by ext k; simp
@[simp] lemma xPart_sub (z w : KKTSpace n p q) : xPart (z - w) = xPart z - xPart w := by ext k; simp
@[simp] lemma uPart_sub (z w : KKTSpace n p q) : uPart (z - w) = uPart z - uPart w := by ext k; simp
@[simp] lemma vPart_sub (z w : KKTSpace n p q) : vPart (z - w) = vPart z - vPart w := by ext k; simp
@[simp] lemma xPart_neg (z : KKTSpace n p q) : xPart (-z) = -xPart z := by ext k; simp
@[simp] lemma uPart_neg (z : KKTSpace n p q) : uPart (-z) = -uPart z := by ext k; simp
@[simp] lemma vPart_neg (z : KKTSpace n p q) : vPart (-z) = -vPart z := by ext k; simp
@[simp] lemma xPart_smul (c : ℝ) (z : KKTSpace n p q) : xPart (c • z) = c • xPart z := by ext k; simp
@[simp] lemma uPart_smul (c : ℝ) (z : KKTSpace n p q) : uPart (c • z) = c • uPart z := by ext k; simp
@[simp] lemma vPart_smul (c : ℝ) (z : KKTSpace n p q) : vPart (c • z) = c • vPart z := by ext k; simp
@[simp] lemma xPart_zero : xPart (0 : KKTSpace n p q) = 0 := by ext k; simp
@[simp] lemma uPart_zero : uPart (0 : KKTSpace n p q) = 0 := by ext k; simp
@[simp] lemma vPart_zero : vPart (0 : KKTSpace n p q) = 0 := by ext k; simp

lemma mk_add (x x' : EuclideanSpace ℝ (Fin n)) (u u' : EuclideanSpace ℝ (Fin p))
    (v v' : EuclideanSpace ℝ (Fin q)) : mk x u v + mk x' u' v' = mk (x + x') (u + u') (v + v') :=
  kkt_ext (by simp) (by simp) (by simp)

lemma mk_parts (z : KKTSpace n p q) : mk (xPart z) (uPart z) (vPart z) = z :=
  kkt_ext (by simp) (by simp) (by simp)

lemma norm_xPart_le (z : KKTSpace n p q) : ‖xPart z‖ ≤ ‖z‖ := by
  have h1 := EuclideanSpace.real_norm_sq_eq (xPart z)
  have h2 := EuclideanSpace.real_norm_sq_eq z
  rw [Fintype.sum_sum_type] at h2
  have h3 : 0 ≤ ∑ i : Fin p ⊕ Fin q, z (Sum.inr i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h4 : ∑ i, (xPart z) i ^ 2 = ∑ a, z (Sum.inl a) ^ 2 := rfl
  have : ‖xPart z‖ ^ 2 ≤ ‖z‖ ^ 2 := by rw [h1, h2, h4]; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

lemma abs_uPart_le (z : KKTSpace n p q) (i : Fin p) : |uPart z i| ≤ ‖z‖ := by
  have := PiLp.norm_apply_le z (Sum.inr (Sum.inl i))
  simpa using this

/-- linear version of xPart -/
noncomputable def xPartL : KKTSpace n p q →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := xPart, map_add' := xPart_add, map_smul' := fun c z => xPart_smul c z }
noncomputable def uPartL : KKTSpace n p q →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  LinearMap.toContinuousLinearMap
    { toFun := uPart, map_add' := uPart_add, map_smul' := fun c z => uPart_smul c z }
noncomputable def vPartL : KKTSpace n p q →L[ℝ] EuclideanSpace ℝ (Fin q) :=
  LinearMap.toContinuousLinearMap
    { toFun := vPart, map_add' := vPart_add, map_smul' := fun c z => vPart_smul c z }
@[simp] lemma xPartL_apply (z : KKTSpace n p q) : xPartL z = xPart z := rfl
@[simp] lemma uPartL_apply (z : KKTSpace n p q) : uPartL z = uPart z := rfl
@[simp] lemma vPartL_apply (z : KKTSpace n p q) : vPartL z = vPart z := rfl

/-- linear version of mk -/
noncomputable def mkL : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p) ×
    EuclideanSpace ℝ (Fin q)) →L[ℝ] KKTSpace n p q :=
  LinearMap.toContinuousLinearMap
    { toFun := fun t => mk t.1 t.2.1 t.2.2
      map_add' := fun a b => by rw [mk_add]; rfl
      map_smul' := fun c a => kkt_ext (by simp) (by simp) (by simp) }
@[simp] lemma mkL_apply (t : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p) ×
    EuclideanSpace ℝ (Fin q)) : mkL t = mk t.1 t.2.1 t.2.2 := rfl

/-- normal cone of the KKT cone -/
lemma mem_normalCone_kkt (w z : KKTSpace n p q) :
    w ∈ RobinsonSR.Reduction.normalCone (kktCone n p q) z ↔
      (∀ i, 0 ≤ uPart z i) ∧ xPart w = 0 ∧ vPart w = 0 ∧
        ∀ i, uPart w i ≤ 0 ∧ uPart w i * uPart z i = 0 := by
  constructor
  · rintro ⟨hz, hw⟩
    have hz' : ∀ i, 0 ≤ uPart z i := hz
    have key : ∀ d : KKTSpace n p q, z + d ∈ kktCone n p q → ⟪w, d⟫ ≤ 0 := by
      intro d hd; have := hw _ hd; simpa using this
    have inner_single : ∀ k t, ⟪w, EuclideanSpace.single k t⟫ = t * w k := by
      intro k t; simp [EuclideanSpace.inner_single_right, mul_comm]
    have free : ∀ k, (∀ t : ℝ, z + EuclideanSpace.single k t ∈ kktCone n p q) → w k = 0 := by
      intro k hk
      have h1 := key _ (hk 1); have h2 := key _ (hk (-1))
      rw [inner_single] at h1 h2; linarith
    refine ⟨hz', ?_, ?_, ?_⟩
    · ext k; simp only [xPart_apply', PiLp.zero_apply]
      apply free
      intro t i; simpa [kktCone, EuclideanSpace.single_apply] using hz' i
    · ext k; simp only [vPart_apply', PiLp.zero_apply]
      apply free
      intro t i; simpa [kktCone, EuclideanSpace.single_apply] using hz' i
    · intro i
      have h1 := key (EuclideanSpace.single (Sum.inr (Sum.inl i)) 1) (by
        intro j; by_cases hj : j = i
        · subst hj; have := hz' j; simp at this; simp; linarith
        · simpa [EuclideanSpace.single_apply, hj] using hz' j)
      have h2 := key (EuclideanSpace.single (Sum.inr (Sum.inl i)) (-uPart z i)) (by
        intro j; by_cases hj : j = i
        · subst hj; simp [EuclideanSpace.single_apply]
        · simpa [EuclideanSpace.single_apply, hj] using hz' j)
      rw [inner_single] at h1 h2
      simp only [uPart_apply'] at h1 h2 ⊢
      have hzi := hz' i; simp only [uPart_apply'] at hzi
      refine ⟨by linarith, ?_⟩
      have h3 := key (EuclideanSpace.single (Sum.inr (Sum.inl i)) (uPart z i)) (by
        intro j; by_cases hj : j = i
        · subst hj; have := hz' j; simp at this; simp; linarith
        · simpa [EuclideanSpace.single_apply, hj] using hz' j)
      rw [inner_single] at h3
      simp only [uPart_apply'] at h3
      nlinarith
  · rintro ⟨hz, hx, hv, hu⟩
    refine ⟨hz, fun c hc => ?_⟩
    have hc' : ∀ i, 0 ≤ uPart c i := hc
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Fintype.sum_sum_type]
    have ex : ∀ k, w (Sum.inl k) = 0 := fun k => by
      have := congrArg (fun t => t k) hx; simpa using this
    have ev : ∀ k, w (Sum.inr (Sum.inr k)) = 0 := fun k => by
      have := congrArg (fun t => t k) hv; simpa using this
    simp only [ex, ev, star_trivial, PiLp.sub_apply, mul_zero, zero_mul,
      Finset.sum_const_zero, zero_add, add_zero]
    apply Finset.sum_nonpos
    intro i _
    obtain ⟨h1, h2⟩ := hu i
    have := hc' i; have hzi := hz i
    simp only [uPart_apply'] at h1 h2 this hzi
    nlinarith

end basics

section deriv
variable {n p q : ℕ}

lemma comp_xPart {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : EuclideanSpace ℝ (Fin n) → F} {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] F}
    {x0 : EuclideanSpace ℝ (Fin n)} (u0 : EuclideanSpace ℝ (Fin p)) (v0 : EuclideanSpace ℝ (Fin q))
    (hf : HasFDerivAt f f' x0) :
    HasFDerivAt (fun z : KKTSpace n p q => f (xPart z)) (f' ∘L xPartL) (mk x0 u0 v0) := by
  have : HasFDerivAt f f' (xPartL (mk x0 u0 v0)) := by simpa using hf
  exact this.comp _ xPartL.hasFDerivAt

lemma fderiv_coord {m : ℕ} {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x0 : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x0) (d : EuclideanSpace ℝ (Fin n))
    (i : Fin m) : fderiv ℝ f x0 d i = ⟪gradient (fun x => f x i) x0, d⟫ := by
  have h1 : HasFDerivAt (fun x => f x i)
      ((PiLp.proj 2 (fun _ : Fin m => ℝ) i) ∘L fderiv ℝ f x0) x0 :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (f x0) i).comp x0 hf.hasFDerivAt
  rw [gradient, h1.fderiv, InnerProductSpace.toDual_symm_apply]
  rfl

theorem kkt_deriv {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ Ω)
    (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (hg : ∀ i, DifferentiableOn ℝ (fun x => g x i) Ω)
    (hh : ∀ j, DifferentiableOn ℝ (fun x => h x j) Ω)
    (hθ2 : DifferentiableAt ℝ (gradient θ) x0)
    (hg2 : ∀ i, DifferentiableAt ℝ (gradient (fun x => g x i)) x0)
    (hh2 : ∀ j, DifferentiableAt ℝ (gradient (fun x => h x j)) x0)
    (u0 : EuclideanSpace ℝ (Fin p)) (v0 : EuclideanSpace ℝ (Fin q)) :
    ∃ DF : KKTSpace n p q →L[ℝ] KKTSpace n p q, HasFDerivAt (kktMap θ g h) DF (mk x0 u0 v0) ∧
      ∀ dz, xPart (DF dz) = lagHess θ g h x0 u0 v0 (xPart dz) +
          ∑ i, uPart dz i • gradient (fun x => g x i) x0 +
          ∑ j, vPart dz j • gradient (fun x => h x j) x0 ∧
        (∀ i, uPart (DF dz) i = -⟪gradient (fun x => g x i) x0, xPart dz⟫) ∧
        (∀ j, vPart (DF dz) j = -⟪gradient (fun x => h x j) x0, xPart dz⟫) := by
  set z0 : KKTSpace n p q := mk x0 u0 v0
  have hgd : DifferentiableAt ℝ g x0 :=
    differentiableAt_piLp 2 |>.2 fun i => (hg i).differentiableAt (hΩ.mem_nhds hx0)
  have hhd : DifferentiableAt ℝ h x0 :=
    differentiableAt_piLp 2 |>.2 fun j => (hh j).differentiableAt (hΩ.mem_nhds hx0)
  -- the Lagrangian gradient at fixed multipliers
  have hLd : DifferentiableAt ℝ (fun x => lagGrad θ g h x u0 v0) x0 := by
    unfold lagGrad
    refine (hθ2.add ?_).add ?_
    · exact DifferentiableAt.fun_sum fun i _ => (hg2 i).fun_const_smul _
    · exact DifferentiableAt.fun_sum fun j _ => (hh2 j).fun_const_smul _
  have hA0 := comp_xPart u0 v0 hLd.hasFDerivAt
  -- correction terms
  have hU : ∀ i : Fin p, HasFDerivAt
      (fun z : KKTSpace n p q => (uPart z i - u0 i) • gradient (fun x => g x i) (xPart z))
      ((uPart z0 i - u0 i) • (fderiv ℝ (gradient fun x => g x i) x0 ∘L xPartL) +
        ((EuclideanSpace.proj i ∘L uPartL) - 0).smulRight
          (gradient (fun x => g x i) (xPart z0))) z0 := by
    intro i
    have hc : HasFDerivAt (fun z : KKTSpace n p q => uPart z i - u0 i)
        ((EuclideanSpace.proj i ∘L uPartL) - 0) z0 :=
      ((EuclideanSpace.proj i ∘L uPartL).hasFDerivAt).sub (hasFDerivAt_const _ _)
    exact hc.smul (comp_xPart u0 v0 (hg2 i).hasFDerivAt)
  have hV : ∀ j : Fin q, HasFDerivAt
      (fun z : KKTSpace n p q => (vPart z j - v0 j) • gradient (fun x => h x j) (xPart z))
      ((vPart z0 j - v0 j) • (fderiv ℝ (gradient fun x => h x j) x0 ∘L xPartL) +
        ((EuclideanSpace.proj j ∘L vPartL) - 0).smulRight
          (gradient (fun x => h x j) (xPart z0))) z0 := by
    intro j
    have hc : HasFDerivAt (fun z : KKTSpace n p q => vPart z j - v0 j)
        ((EuclideanSpace.proj j ∘L vPartL) - 0) z0 :=
      ((EuclideanSpace.proj j ∘L vPartL).hasFDerivAt).sub (hasFDerivAt_const _ _)
    exact hc.smul (comp_xPart u0 v0 (hh2 j).hasFDerivAt)
  have hA := (hA0.fun_add (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hU i)).fun_add
    (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => hV j)
  have hAeq : (fun z : KKTSpace n p q => lagGrad θ g h (xPart z) u0 v0 +
      ∑ i ∈ Finset.univ, (uPart z i - u0 i) • gradient (fun x => g x i) (xPart z) +
      ∑ j ∈ Finset.univ, (vPart z j - v0 j) • gradient (fun x => h x j) (xPart z)) =
      fun z => lagGrad θ g h (xPart z) (uPart z) (vPart z) := by
    funext z
    simp only [lagGrad, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hAeq] at hA
  have hB := comp_xPart u0 v0 hgd.hasFDerivAt
  have hC := comp_xPart u0 v0 hhd.hasFDerivAt
  have hF := mkL.hasFDerivAt.comp z0 (hA.prodMk (hB.neg.prodMk hC.neg))
  refine ⟨_, hF, fun dz => ⟨?_, fun i => ?_, fun j => ?_⟩⟩
  · simp [z0, lagHess]
  · simp [fderiv_coord hgd]
  · simp [fderiv_coord hhd]

end deriv
section linear
variable {n p q : ℕ}
variable (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  (γ : Fin p → EuclideanSpace ℝ (Fin n)) (η : Fin q → EuclideanSpace ℝ (Fin n))
  (P Z : Fin p → Prop) [DecidablePred P] [DecidablePred Z]

noncomputable def PhiL : KKTSpace n p q →ₗ[ℝ] KKTSpace n p q where
  toFun dz := mk (L (xPart dz) + ∑ i ∈ Finset.univ.filter P, uPart dz i • γ i +
      ∑ j, vPart dz j • η j)
    (WithLp.toLp 2 fun i => if P i then ⟪γ i, xPart dz⟫ else uPart dz i)
    (WithLp.toLp 2 fun j => ⟪η j, xPart dz⟫)
  map_add' a b := by
    apply kkt_ext
    · simp only [xPart_mk, xPart_add, uPart_add, vPart_add, map_add, PiLp.add_apply, add_smul,
        Finset.sum_add_distrib]; abel
    · ext i; by_cases hP : P i <;> simp [hP, inner_add_right]
    · ext j; simp [inner_add_right]
  map_smul' c a := by
    apply kkt_ext
    · simp only [xPart_mk, xPart_smul, uPart_smul, vPart_smul, map_smul, PiLp.smul_apply,
        smul_eq_mul, mul_smul, RingHom.id_apply, smul_add, Finset.smul_sum]
    · ext i; by_cases hP : P i <;> simp [hP, inner_smul_right]
    · ext j; simp [inner_smul_right]

noncomputable def R1L : KKTSpace n p q →ₗ[ℝ] KKTSpace n p q where
  toFun y := mk (xPart y) (WithLp.toLp 2 fun i => if P i then -uPart y i else 0) (-vPart y)
  map_add' a b := by
    apply kkt_ext
    · simp
    · ext i; by_cases hP : P i <;> simp [hP]; ring
    · ext j; simp; ring
  map_smul' c a := by
    apply kkt_ext
    · simp
    · ext i; by_cases hP : P i <;> simp [hP]
    · ext j; simp

noncomputable def R2L : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] KKTSpace n p q where
  toFun μ := mk (-∑ i ∈ Finset.univ.filter Z, μ i • γ i) 0 0
  map_add' a b := by
    apply kkt_ext
    · simp [add_smul, Finset.sum_add_distrib]; abel
    · simp
    · simp
  map_smul' c a := by
    apply kkt_ext
    · simp [mul_smul, Finset.smul_sum]
    · simp
    · simp

noncomputable def EL : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] KKTSpace n p q where
  toFun μ := mk 0 (WithLp.toLp 2 fun i => if Z i then μ i else 0) 0
  map_add' a b := by
    apply kkt_ext
    · simp
    · ext i; by_cases hZ : Z i <;> simp [hZ]
    · simp
  map_smul' c a := by
    apply kkt_ext
    · simp
    · ext i; by_cases hZ : Z i <;> simp [hZ]
    · simp

variable {L γ η P Z}

lemma phi_x (dz : KKTSpace n p q) : xPart (PhiL L γ η P dz) = L (xPart dz) +
    ∑ i ∈ Finset.univ.filter P, uPart dz i • γ i + ∑ j, vPart dz j • η j := by
  simp [PhiL]
lemma phi_u (dz : KKTSpace n p q) (i : Fin p) : uPart (PhiL L γ η P dz) i =
    if P i then ⟪γ i, xPart dz⟫ else uPart dz i := by
  simp [PhiL]
lemma phi_v (dz : KKTSpace n p q) (j : Fin q) : vPart (PhiL L γ η P dz) j = ⟪η j, xPart dz⟫ := by
  simp [PhiL]

/-- the key quadratic identity -/
lemma phi_quad (dz : KKTSpace n p q) (hu : ∀ i, P i → ⟪γ i, xPart dz⟫ = 0)
    (hv : ∀ j, ⟪η j, xPart dz⟫ = 0) :
    ⟪xPart dz, L (xPart dz)⟫ = ⟪xPart dz, xPart (PhiL L γ η P dz)⟫ := by
  rw [phi_x, inner_add_right, inner_add_right, inner_sum, inner_sum]
  have h1 : ∑ i ∈ Finset.univ.filter P, ⟪xPart dz, uPart dz i • γ i⟫ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [inner_smul_right, real_inner_comm, hu i hi.2, mul_zero]
  have h2 : ∑ j, ⟪xPart dz, vPart dz j • η j⟫ = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [inner_smul_right, real_inner_comm, hv j, mul_zero]
  rw [h1, h2]; ring

end linear
section lcp
lemma pd_const {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (S : E →L[ℝ] E) (h : ∀ μ, μ ≠ 0 → 0 < ⟪μ, S μ⟫) :
    ∃ c > 0, ∀ μ, c * ‖μ‖ ^ 2 ≤ ⟪μ, S μ⟫ := by
  have hφ : Continuous fun μ : E => ⟪μ, S μ⟫ := continuous_id.inner S.continuous
  have scale : ∀ μ : E, μ ≠ 0 → ‖μ‖⁻¹ • μ ∈ Metric.sphere (0 : E) 1 := by
    intro μ hμ
    simp [norm_smul, norm_ne_zero_iff.mpr hμ]
  have hom : ∀ μ : E, ⟪‖μ‖⁻¹ • μ, S (‖μ‖⁻¹ • μ)⟫ = (‖μ‖⁻¹) ^ 2 * ⟪μ, S μ⟫ := by
    intro μ; simp [inner_smul_left, inner_smul_right, map_smul]; ring
  by_cases hs : (Metric.sphere (0 : E) 1).Nonempty
  · obtain ⟨m, hm, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hs hφ.continuousOn
    have hm0 : m ≠ 0 := by
      intro h0; rw [h0] at hm; simp at hm
    refine ⟨⟪m, S m⟫, h m hm0, fun μ => ?_⟩
    by_cases hμ : μ = 0
    · subst hμ; simp
    have h1 : ⟪m, S m⟫ ≤ ⟪‖μ‖⁻¹ • μ, S (‖μ‖⁻¹ • μ)⟫ := hmin (scale μ hμ)
    rw [hom] at h1
    have hn : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
    have : ⟪m, S m⟫ * ‖μ‖ ^ 2 ≤ ‖μ‖⁻¹ ^ 2 * ⟪μ, S μ⟫ * ‖μ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    calc ⟪m, S m⟫ * ‖μ‖ ^ 2 ≤ ‖μ‖⁻¹ ^ 2 * ⟪μ, S μ⟫ * ‖μ‖ ^ 2 := this
      _ = ⟪μ, S μ⟫ := by field_simp
  · refine ⟨1, one_pos, fun μ => ?_⟩
    have hμ : μ = 0 := by
      by_contra hμ; exact hs ⟨_, scale μ hμ⟩
    subst hμ; simp

variable {ι : Type*} [Fintype ι]

def IsLCP (S : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) (q μ : EuclideanSpace ℝ ι) : Prop :=
  ∀ i, 0 ≤ μ i ∧ 0 ≤ (S μ + q) i ∧ μ i * (S μ + q) i = 0

lemma lcp_lip (S : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) {c : ℝ} (hc : 0 < c)
    (hS : ∀ μ, c * ‖μ‖ ^ 2 ≤ ⟪μ, S μ⟫) {q1 q2 μ1 μ2 : EuclideanSpace ℝ ι}
    (h1 : IsLCP S q1 μ1) (h2 : IsLCP S q2 μ2) : c * ‖μ1 - μ2‖ ≤ ‖q1 - q2‖ := by
  set d := μ1 - μ2
  have hneg : ⟪d, (S μ1 + q1) - (S μ2 + q2)⟫ ≤ 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial]
    apply Finset.sum_nonpos
    intro i _
    obtain ⟨a1, b1, c1⟩ := h1 i
    obtain ⟨a2, b2, c2⟩ := h2 i
    simp only [d, PiLp.sub_apply] at *
    nlinarith [mul_nonneg a1 b2, mul_nonneg a2 b1]
  have hsplit : (S μ1 + q1) - (S μ2 + q2) = S d + (q1 - q2) := by
    simp only [d, map_sub]; abel
  rw [hsplit, inner_add_right] at hneg
  have hcs : -⟪d, q1 - q2⟫ ≤ ‖d‖ * ‖q1 - q2‖ := by
    have := abs_real_inner_le_norm d (q1 - q2)
    linarith [neg_abs_le ⟪d, q1 - q2⟫]
  have key : c * ‖d‖ ^ 2 ≤ ‖d‖ * ‖q1 - q2‖ := by linarith [hS d]
  rcases (norm_nonneg d).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have : c * ‖d‖ * ‖d‖ ≤ ‖q1 - q2‖ * ‖d‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

lemma lcp_exists (S : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) {c : ℝ} (hc : 0 < c)
    (hS : ∀ μ, c * ‖μ‖ ^ 2 ≤ ⟪μ, S μ⟫) (q : EuclideanSpace ℝ ι) : ∃ μ, IsLCP S q μ := by
  set c' := min c 1 with hc'
  have hc'pos : 0 < c' := lt_min hc one_pos
  have hc'1 : c' ≤ 1 := min_le_right _ _
  have hS' : ∀ μ, c' * ‖μ‖ ^ 2 ≤ ⟪μ, S μ⟫ := fun μ =>
    le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)) (hS μ)
  set t := c' / (‖S‖ ^ 2 + 1) with ht
  have htpos : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]; nlinarith [sq_nonneg ‖S‖]
  have htS : t * ‖S‖ ^ 2 ≤ c' := by
    rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg ‖S‖]
  have htc : t * c' ≤ 1 := by nlinarith
  set K : NNReal := ⟨Real.sqrt (1 - t * c'), Real.sqrt_nonneg _⟩ with hK
  have hK1 : K < 1 := by
    show Real.sqrt (1 - t * c') < 1
    rw [Real.sqrt_lt' one_pos]; nlinarith [mul_pos htpos hc'pos]
  let f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
    fun μ => WithLp.toLp 2 (fun i => max (μ i - t * (S μ + q) i) 0)
  have hlip : LipschitzWith K f := by
    apply LipschitzWith.of_dist_le_mul
    intro μ ν
    set d := μ - ν
    have hlin : (fun i => (μ i - t * (S μ + q) i) - (ν i - t * (S ν + q) i)) =
        fun i => (d - t • S d) i := by
      funext i; simp [d, map_sub]; ring
    have step1 : dist (f μ) (f ν) ≤ ‖d - t • S d‖ := by
      rw [EuclideanSpace.dist_eq, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i _
      simp only [f, PiLp.toLp_apply, Real.dist_eq, Real.norm_eq_abs, sq_abs]
      have := abs_max_sub_max_le_abs (μ i - t * (S μ + q) i) (ν i - t * (S ν + q) i) 0
      have e := congrFun hlin i
      simp only at e
      rw [← e]
      nlinarith [abs_nonneg (max (μ i - t * (S μ + q) i) 0 - max (ν i - t * (S ν + q) i) 0),
        sq_abs (max (μ i - t * (S μ + q) i) 0 - max (ν i - t * (S ν + q) i) 0),
        sq_abs ((μ i - t * (S μ + q) i) - (ν i - t * (S ν + q) i))]
    have step2 : ‖d - t • S d‖ ^ 2 ≤ (1 - t * c') * ‖d‖ ^ 2 := by
      have e : ‖d - t • S d‖ ^ 2 = ‖d‖ ^ 2 - 2 * t * ⟪d, S d⟫ + t ^ 2 * ‖S d‖ ^ 2 := by
        rw [@norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        ring
      have hSd : ‖S d‖ ≤ ‖S‖ * ‖d‖ := S.le_opNorm d
      have hSd2 : ‖S d‖ ^ 2 ≤ ‖S‖ ^ 2 * ‖d‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hSd 2
      have := hS' d
      have h3 : t ^ 2 * ‖S d‖ ^ 2 ≤ t * c' * ‖d‖ ^ 2 := by
        calc t ^ 2 * ‖S d‖ ^ 2 ≤ t ^ 2 * (‖S‖ ^ 2 * ‖d‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hSd2 (by positivity)
          _ = t * (t * ‖S‖ ^ 2) * ‖d‖ ^ 2 := by ring
          _ ≤ t * c' * ‖d‖ ^ 2 := by gcongr
      rw [e]; nlinarith
    have step3 : ‖d - t • S d‖ ≤ Real.sqrt (1 - t * c') * ‖d‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (d - t • S d)), ← Real.sqrt_sq (norm_nonneg d),
        ← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt step2
    calc dist (f μ) (f ν) ≤ ‖d - t • S d‖ := step1
      _ ≤ Real.sqrt (1 - t * c') * ‖d‖ := step3
      _ = K * dist μ ν := by rw [dist_eq_norm]; rfl
  have hcon : ContractingWith K f := ⟨hK1, hlip⟩
  set μ := ContractingWith.fixedPoint f hcon
  have hfix : f μ = μ := ContractingWith.fixedPoint_isFixedPt hcon
  refine ⟨μ, fun i => ?_⟩
  have hi : max (μ i - t * (S μ + q) i) 0 = μ i := by
    have := congrArg (fun v : EuclideanSpace ℝ ι => v i) hfix
    simpa [f] using this
  have hμ0 : 0 ≤ μ i := by rw [← hi]; exact le_max_right _ _
  rcases hμ0.eq_or_lt with h0 | hpos
  · have hz : μ i = 0 := h0.symm
    have h3 := le_max_left (μ i - t * (S μ + q) i) 0
    rw [hi] at h3
    refine ⟨hμ0, ?_, by rw [hz, zero_mul]⟩
    by_contra hw; push_neg at hw
    nlinarith [mul_neg_of_pos_of_neg htpos hw]
  · have : max (μ i - t * (S μ + q) i) 0 = μ i - t * (S μ + q) i := by
      rcases le_total (μ i - t * (S μ + q) i) 0 with hle | hle
      · rw [max_eq_right hle] at hi; linarith
      · exact max_eq_left hle
    rw [this] at hi
    have hw : (S μ + q) i = 0 := by
      have : t * (S μ + q) i = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
    exact ⟨hpos.le, by rw [hw], by rw [hw, mul_zero]⟩

end lcp
section main
variable {n p q : ℕ}
open Topology

lemma sum_filter_smul (P : Fin p → Prop) [DecidablePred P] (f : Fin p → ℝ)
    (γ : Fin p → EuclideanSpace ℝ (Fin n)) :
    ∑ i ∈ Finset.univ.filter P, f i • γ i = ∑ i, (if P i then f i else 0) • γ i := by
  rw [Finset.sum_filter]; congr 1; ext i; split_ifs <;> simp

set_option maxHeartbeats 1000000 in
theorem linear_sr
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (γ : Fin p → EuclideanSpace ℝ (Fin n)) (η : Fin q → EuclideanSpace ℝ (Fin n))
    (P Z : Fin p → Prop) [DecidablePred P] [DecidablePred Z]
    (hSS : ∀ d, d ≠ 0 → (∀ i, P i → ⟪γ i, d⟫ = 0) → (∀ j, ⟪η j, d⟫ = 0) → 0 < ⟪d, L d⟫)
    (hLI : ∀ (α : Fin p → ℝ) (β : Fin q → ℝ), (∀ i, ¬ P i → ¬ Z i → α i = 0) →
      ∑ i, α i • γ i + ∑ j, β j • η j = 0 → (∀ i, α i = 0) ∧ ∀ j, β j = 0)
    (hPZ : ∀ i, P i → ¬ Z i)
    (z0 : KKTSpace n p q) (gv : Fin p → ℝ)
    (hu0P : ∀ i, P i → 0 < uPart z0 i) (hu0n : ∀ i, ¬ P i → uPart z0 i = 0)
    (hgP : ∀ i, P i → gv i = 0) (hgZ : ∀ i, Z i → gv i = 0)
    (hgI : ∀ i, ¬ P i → ¬ Z i → gv i < 0)
    (a : KKTSpace n p q) (ha_x : xPart a = 0) (ha_u : ∀ i, uPart a i = -gv i) (ha_v : vPart a = 0)
    (DF : KKTSpace n p q →L[ℝ] KKTSpace n p q)
    (hDF : ∀ dz, xPart (DF dz) = L (xPart dz) + ∑ i, uPart dz i • γ i + ∑ j, vPart dz j • η j ∧
        (∀ i, uPart (DF dz) i = -⟪γ i, xPart dz⟫) ∧ (∀ j, vPart (DF dz) j = -⟪η j, xPart dz⟫)) :
    ∃ lam, StronglyRegular (kktCone n p q) a DF z0 lam := by
  -- Step 1: injectivity of Φ
  have hinj : Function.Injective (PhiL L γ η P) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro dz h0
    have hv : ∀ j, ⟪η j, xPart dz⟫ = 0 := fun j => by
      have := phi_v (L := L) (γ := γ) (η := η) (P := P) dz j; rw [h0] at this; simpa using this.symm
    have hu : ∀ i, P i → ⟪γ i, xPart dz⟫ = 0 := fun i hi => by
      have := phi_u (L := L) (γ := γ) (η := η) (P := P) dz i; rw [h0, if_pos hi] at this
      simpa using this.symm
    have hun : ∀ i, ¬ P i → uPart dz i = 0 := fun i hi => by
      have := phi_u (L := L) (γ := γ) (η := η) (P := P) dz i; rw [h0, if_neg hi] at this
      simpa using this.symm
    have hx : xPart dz = 0 := by
      by_contra hne
      have := hSS _ hne hu hv
      rw [phi_quad (L := L) (γ := γ) (η := η) (P := P) dz hu hv, h0] at this; simp at this
    have hxx := phi_x (L := L) (γ := γ) (η := η) (P := P) dz
    rw [h0, hx, sum_filter_smul] at hxx
    simp only [xPart_zero, map_zero, zero_add] at hxx
    obtain ⟨hα, hβ⟩ := hLI (fun i => if P i then uPart dz i else 0) (fun j => vPart dz j)
      (fun i hi _ => by simp [hi]) hxx.symm
    apply kkt_ext
    · simpa using hx
    · ext i; by_cases hi : P i
      · have := hα i; simp [hi] at this; simpa using this
      · simpa using hun i hi
    · ext j; simpa using hβ j
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : KKTSpace n p q →ₗ[ℝ] KKTSpace n p q, ∀ w, PhiL L γ η P (Ψ w) = w :=
    ⟨(LinearEquiv.ofInjectiveEndo _ hinj).symm.toLinearMap, fun w => by
      have := (LinearEquiv.ofInjectiveEndo _ hinj).apply_symm_apply w
      rwa [LinearEquiv.coe_ofInjectiveEndo] at this⟩
  have hΨu : ∀ dz w, PhiL L γ η P dz = w → dz = Ψ w := fun dz w h => hinj (by rw [hΨ, h])
  -- facts about Ψ w
  have hΨx : ∀ w, L (xPart (Ψ w)) + ∑ i, (if P i then uPart (Ψ w) i else 0) • γ i +
      ∑ j, vPart (Ψ w) j • η j = xPart w := fun w => by
    rw [← sum_filter_smul, ← phi_x (L := L) (γ := γ) (η := η) (P := P), hΨ]
  have hΨP : ∀ w i, P i → ⟪γ i, xPart (Ψ w)⟫ = uPart w i := fun w i hi => by
    have := phi_u (L := L) (γ := γ) (η := η) (P := P) (Ψ w) i
    rw [hΨ, if_pos hi] at this; exact this.symm
  have hΨn : ∀ w i, ¬ P i → uPart (Ψ w) i = uPart w i := fun w i hi => by
    have := phi_u (L := L) (γ := γ) (η := η) (P := P) (Ψ w) i
    rw [hΨ, if_neg hi] at this; exact this.symm
  have hΨv : ∀ w j, ⟪η j, xPart (Ψ w)⟫ = vPart w j := fun w j => by
    rw [← phi_v (L := L) (γ := γ) (η := η) (P := P), hΨ]
  -- parts of the right-hand sides
  have R1x : ∀ y, xPart (R1L (n := n) (q := q) P y) = xPart y := fun y => by simp [R1L]
  have R1u : ∀ y i, uPart (R1L (n := n) (q := q) P y) i = if P i then -uPart y i else 0 :=
    fun y i => by simp [R1L]
  have R1v : ∀ y j, vPart (R1L (n := n) (q := q) P y) j = -vPart y j := fun y j => by simp [R1L]
  have R2x : ∀ μ, xPart (R2L (n := n) (q := q) γ Z μ) = -∑ i ∈ Finset.univ.filter Z, μ i • γ i :=
    fun μ => by simp [R2L]
  have R2u : ∀ μ i, uPart (R2L (n := n) (q := q) γ Z μ) i = 0 := fun μ i => by simp [R2L]
  have R2v : ∀ μ j, vPart (R2L (n := n) (q := q) γ Z μ) j = 0 := fun μ j => by simp [R2L]
  have Ex : ∀ μ, xPart (EL (n := n) (q := q) Z μ) = 0 := fun μ => by simp [EL]
  have Eu : ∀ μ i, uPart (EL (n := n) (q := q) Z μ) i = if Z i then μ i else 0 :=
    fun μ i => by simp [EL]
  have Ev : ∀ μ, vPart (EL (n := n) (q := q) Z μ) = 0 := fun μ => by simp [EL]
  have hZP : ∀ i, Z i → ¬ P i := fun i hz hp => hPZ i hp hz
  -- the Schur-type operator and the LCP data
  obtain ⟨S, hS⟩ : ∃ S : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p), ∀ μ i,
      S μ i = if Z i then -⟪γ i, xPart (Ψ (R2L (n := n) (q := q) γ Z μ))⟫ else μ i :=
    ⟨LinearMap.toContinuousLinearMap
      { toFun := fun μ => WithLp.toLp 2 fun i =>
          if Z i then -⟪γ i, xPart (Ψ (R2L (n := n) (q := q) γ Z μ))⟫ else μ i
        map_add' := fun a b => by
          ext i; by_cases hZ : Z i <;> simp [hZ, map_add, inner_add_right]; ring
        map_smul' := fun c a => by
          ext i; by_cases hZ : Z i <;> simp [hZ, map_smul, inner_smul_right] }, fun μ i => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : KKTSpace n p q →L[ℝ] EuclideanSpace ℝ (Fin p), ∀ y i,
      Q y i = if Z i then -(uPart y i + ⟪γ i, xPart (Ψ (R1L (n := n) (q := q) P y))⟫) else 0 :=
    ⟨LinearMap.toContinuousLinearMap
      { toFun := fun y => WithLp.toLp 2 fun i =>
          if Z i then -(uPart y i + ⟪γ i, xPart (Ψ (R1L (n := n) (q := q) P y))⟫) else 0
        map_add' := fun a b => by
          ext i; by_cases hZ : Z i <;> simp [hZ, map_add, inner_add_right]; ring
        map_smul' := fun c a => by
          ext i; by_cases hZ : Z i <;> simp [hZ, map_smul, inner_smul_right]; ring }, fun y i => rfl⟩
  -- positivity of S
  have hSpos : ∀ μ, μ ≠ 0 → 0 < ⟪μ, S μ⟫ := by
    intro μ hμ
    obtain ⟨dz, hdz⟩ : ∃ dz, dz = Ψ (R2L (n := n) (q := q) γ Z μ) := ⟨_, rfl⟩
    have hP0 : ∀ i, P i → ⟪γ i, xPart dz⟫ = 0 := fun i hi => by rw [hdz, hΨP _ i hi, R2u]
    have hv0 : ∀ j, ⟪η j, xPart dz⟫ = 0 := fun j => by rw [hdz, hΨv, R2v]
    have hq := phi_quad (L := L) (γ := γ) (η := η) (P := P) dz hP0 hv0
    rw [hdz, hΨ, R2x, ← hdz, inner_neg_right, inner_sum] at hq
    have hinner : ⟪μ, S μ⟫ = ∑ i, μ i * S μ i := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct, mul_comm]
    have hsplit : ∑ i, μ i * S μ i = ⟪xPart dz, L (xPart dz)⟫ +
        ∑ i ∈ Finset.univ.filter (fun i => ¬ Z i), μ i ^ 2 := by
      rw [hq]
      have : ∀ i, μ i * S μ i = if Z i then -⟪xPart dz, μ i • γ i⟫ else μ i ^ 2 := by
        intro i; rw [hS, ← hdz]; split_ifs
        · rw [inner_smul_right, real_inner_comm]; ring
        · ring
      simp only [this]
      rw [Finset.sum_ite, Finset.sum_neg_distrib]
    have hLnn : 0 ≤ ⟪xPart dz, L (xPart dz)⟫ := by
      by_cases h0 : xPart dz = 0
      · simp [h0]
      · exact (hSS _ h0 hP0 hv0).le
    have hsq : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ Z i), μ i ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    by_contra hle; push_neg at hle
    rw [hinner, hsplit] at hle
    have hL0 : ⟪xPart dz, L (xPart dz)⟫ = 0 := by linarith
    have hsq0 : ∑ i ∈ Finset.univ.filter (fun i => ¬ Z i), μ i ^ 2 = 0 := by linarith
    have hx0 : xPart dz = 0 := by
      by_contra h0; have := hSS _ h0 hP0 hv0; linarith
    have hnZ : ∀ i, ¬ Z i → μ i = 0 := by
      intro i hi
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (μ i))).1 hsq0 i
        (by simp [hi])
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have hxx := hΨx (R2L (n := n) (q := q) γ Z μ)
    rw [← hdz, hx0, map_zero, zero_add, R2x, sum_filter_smul] at hxx
    have hsum : ∑ i, ((if P i then uPart dz i else 0) + (if Z i then μ i else 0)) • γ i +
        ∑ j, vPart dz j • η j = 0 := by
      simp only [add_smul, Finset.sum_add_distrib]
      rw [add_right_comm, hxx]; abel
    obtain ⟨hα, -⟩ := hLI _ _ (fun i hp hz => by simp [hp, hz]) hsum
    apply hμ
    ext i
    by_cases hz : Z i
    · have := hα i; simp [hz, hZP i hz] at this; simpa using this
    · simpa using hnZ i hz
  obtain ⟨c, hc, hSc⟩ := pd_const S hSpos
  choose μf hμf using fun y => lcp_exists S hc hSc (Q y)
  have hμu : ∀ y μ', IsLCP S (Q y) μ' → μ' = μf y := by
    intro y μ' h
    have := lcp_lip S hc hSc h (hμf y)
    rw [sub_self, norm_zero] at this
    have h2 : ‖μ' - μf y‖ = 0 := le_antisymm (by
      by_contra hh; push_neg at hh; nlinarith) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 h2)
  have hμL : ∀ y1 y2, ‖μf y1 - μf y2‖ ≤ ‖Q‖ / c * ‖y1 - y2‖ := by
    intro y1 y2
    have h1 := lcp_lip S hc hSc (hμf y1) (hμf y2)
    have h2 : ‖Q y1 - Q y2‖ ≤ ‖Q‖ * ‖y1 - y2‖ := by rw [← map_sub]; exact Q.le_opNorm _
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]; linarith
  have hμ0 : μf 0 = 0 := (hμu 0 0 (fun i => by simp)).symm
  -- the solution map
  set T1 : KKTSpace n p q →L[ℝ] KKTSpace n p q :=
    (Ψ ∘ₗ R1L (n := n) (q := q) P).toContinuousLinearMap with hT1
  set T2 : EuclideanSpace ℝ (Fin p) →L[ℝ] KKTSpace n p q :=
    (Ψ ∘ₗ R2L (n := n) (q := q) γ Z + EL (n := n) (q := q) Z).toContinuousLinearMap with hT2
  obtain ⟨s, hs⟩ : ∃ s : KKTSpace n p q → KKTSpace n p q, ∀ y, s y = z0 +
      (Ψ (R1L (n := n) (q := q) P y + R2L (n := n) (q := q) γ Z (μf y)) +
        EL (n := n) (q := q) Z (μf y)) := ⟨_, fun y => rfl⟩
  have hsdiff : ∀ y1 y2, s y1 - s y2 = T1 (y1 - y2) + T2 (μf y1 - μf y2) := by
    intro y1 y2
    simp only [hs, hT1, hT2, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
      Function.comp_apply, LinearMap.add_apply, ContinuousLinearMap.add_apply, map_add, map_sub]
    abel
  set lam := ‖T1‖ + ‖T2‖ * (‖Q‖ / c) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hsL : ∀ y1 y2, ‖s y1 - s y2‖ ≤ lam * ‖y1 - y2‖ := by
    intro y1 y2
    rw [hsdiff]
    have a1 := T1.le_opNorm (y1 - y2)
    have a2 := T2.le_opNorm (μf y1 - μf y2)
    have a3 := mul_le_mul_of_nonneg_left (hμL y1 y2) (norm_nonneg T2)
    calc ‖T1 (y1 - y2) + T2 (μf y1 - μf y2)‖
        ≤ ‖T1 (y1 - y2)‖ + ‖T2 (μf y1 - μf y2)‖ := norm_add_le _ _
      _ ≤ lam * ‖y1 - y2‖ := by rw [hlam]; nlinarith
  have hs0 : s 0 = z0 := by rw [hs, hμ0]; simp
  have hsnear : ∀ y, ‖s y - z0‖ ≤ lam * ‖y‖ := fun y => by
    have := hsL y 0; rwa [hs0, sub_zero] at this
  -- constants
  obtain ⟨m, hm, hmP, hmI⟩ : ∃ m : ℝ, 0 < m ∧ (∀ i, P i → m ≤ uPart z0 i) ∧
      (∀ i, ¬ P i → ¬ Z i → gv i ≤ -m) := by
    set mi : Fin p → ℝ := fun i => if P i then uPart z0 i else if Z i then 1 else -gv i with hmi
    have hmipos : ∀ i, 0 < mi i := by
      intro i; simp only [hmi]
      split_ifs with h1 h2
      · exact hu0P i h1
      · exact one_pos
      · linarith [hgI i h1 h2]
    have hsum0 : 0 ≤ ∑ i, 1 / mi i := Finset.sum_nonneg fun i _ => (one_div_pos.2 (hmipos i)).le
    have hle : ∀ i, 1 / (1 + ∑ i, 1 / mi i) ≤ mi i := by
      intro i
      have h1 : 1 / mi i ≤ ∑ i, 1 / mi i :=
        Finset.single_le_sum (f := fun i => 1 / mi i)
          (fun i _ => (one_div_pos.2 (hmipos i)).le) (Finset.mem_univ i)
      have h2 : 1 / mi i ≤ 1 + ∑ i, 1 / mi i := by linarith
      calc 1 / (1 + ∑ i, 1 / mi i) ≤ 1 / (1 / mi i) :=
            one_div_le_one_div_of_le (one_div_pos.2 (hmipos i)) h2
        _ = mi i := one_div_one_div _
    refine ⟨1 / (1 + ∑ i, 1 / mi i), by positivity, fun i hi => ?_, fun i h1 h2 => ?_⟩
    · have := hle i; simp only [hmi, if_pos hi] at this; exact this
    · have := hle i; simp only [hmi, if_neg h1, if_neg h2] at this; linarith
  set Γ := ∑ i, ‖γ i‖ with hΓdef
  have hΓ0 : 0 ≤ Γ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hΓ : ∀ i, ‖γ i‖ ≤ Γ := fun i =>
    Finset.single_le_sum (f := fun i => ‖γ i‖) (fun i _ => norm_nonneg _) (Finset.mem_univ i)
  have hInn : ∀ i (dz : KKTSpace n p q), ⟪γ i, xPart dz⟫ ≤ Γ * ‖dz‖ := by
    intro i dz
    calc ⟪γ i, xPart dz⟫ ≤ ‖γ i‖ * ‖xPart dz‖ := real_inner_le_norm _ _
      _ ≤ Γ * ‖dz‖ := mul_le_mul (hΓ i) (norm_xPart_le dz) (norm_nonneg _) hΓ0
  set δ := m / (2 * (Γ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδe : δ * (2 * (Γ + 1)) = m := by rw [hδ]; field_simp
  have hδm : δ ≤ m / 2 := by nlinarith
  have hΓδ : Γ * δ ≤ m / 2 := by nlinarith
  set ε := min (δ / (lam + 1)) (m / 2) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  have hεm : ε ≤ m / 2 := min_le_right _ _
  have hεδ : lam * ε < δ := by
    have h1 : ε ≤ δ / (lam + 1) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  -- residual
  have hres : ∀ y z : KKTSpace n p q,
      xPart (y - (a + DF (z - z0))) = xPart y - (L (xPart (z - z0)) +
        ∑ i, uPart (z - z0) i • γ i + ∑ j, vPart (z - z0) j • η j) ∧
      (∀ i, uPart (y - (a + DF (z - z0))) i = uPart y i + gv i + ⟪γ i, xPart (z - z0)⟫) ∧
      (∀ j, vPart (y - (a + DF (z - z0))) j = vPart y j + ⟪η j, xPart (z - z0)⟫) := by
    intro y z
    obtain ⟨h1, h2, h3⟩ := hDF (z - z0)
    refine ⟨?_, fun i => ?_, fun j => ?_⟩
    · rw [xPart_sub, xPart_add, h1, ha_x, zero_add]
    · rw [uPart_sub, uPart_add, PiLp.sub_apply, PiLp.add_apply, h2, ha_u]; ring
    · rw [vPart_sub, vPart_add, PiLp.sub_apply, PiLp.add_apply, h3, ha_v]; simp
  -- inactive constraints stay inactive
  have hIneg : ∀ (y z : KKTSpace n p q) i, ‖y‖ < ε → ‖z - z0‖ < δ → ¬ P i → ¬ Z i →
      uPart y i + gv i + ⟪γ i, xPart (z - z0)⟫ < 0 := by
    intro y z i hy hz h1 h2
    have e1 := (abs_le.1 (abs_uPart_le y i)).2
    have e2 := hInn i (z - z0)
    have e3 := hmI i h1 h2
    have e4 : Γ * ‖z - z0‖ ≤ Γ * δ := mul_le_mul_of_nonneg_left hz.le hΓ0
    linarith
  refine ⟨lam, Metric.ball 0 ε, Metric.ball_mem_nhds _ hεpos, Metric.ball z0 δ,
    Metric.ball_mem_nhds _ hδpos, s, fun y hy => ?_, fun y1 _ y2 _ => hsL y1 y2⟩
  rw [Metric.mem_ball, dist_zero_right] at hy
  have hsV : ‖s y - z0‖ < δ := by
    have := hsnear y
    have : lam * ‖y‖ ≤ lam * ε := mul_le_mul_of_nonneg_left hy.le hlam0
    linarith
  refine ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact hsV, ?_, ?_⟩
  · -- existence
    obtain ⟨w, hw⟩ : ∃ w, w = R1L (n := n) (q := q) P y + R2L (n := n) (q := q) γ Z (μf y) :=
      ⟨_, rfl⟩
    have hsy : s y - z0 = Ψ w + EL (n := n) (q := q) Z (μf y) := by rw [hs, hw]; abel
    have dxe : xPart (s y - z0) = xPart (Ψ w) := by rw [hsy, xPart_add, Ex, add_zero]
    have dve : vPart (s y - z0) = vPart (Ψ w) := by rw [hsy, vPart_add, Ev, add_zero]
    have due : ∀ i, uPart (s y - z0) i = uPart (Ψ w) i + (if Z i then μf y i else 0) := by
      intro i; rw [hsy, uPart_add, PiLp.add_apply, Eu]
    have hwn : ∀ i, ¬ P i → uPart (Ψ w) i = 0 := by
      intro i hi; rw [hΨn _ _ hi, hw, uPart_add, PiLp.add_apply, R1u, R2u, if_neg hi]; simp
    have hwP : ∀ i, P i → ⟪γ i, xPart (Ψ w)⟫ = -uPart y i := by
      intro i hi; rw [hΨP _ _ hi, hw, uPart_add, PiLp.add_apply, R1u, R2u, if_pos hi]; simp
    have hwv : ∀ j, ⟪η j, xPart (Ψ w)⟫ = -vPart y j := by
      intro j; rw [hΨv, hw, vPart_add, PiLp.add_apply, R1v, R2v]; simp
    have hxw : xPart w = xPart y - ∑ i ∈ Finset.univ.filter Z, μf y i • γ i := by
      rw [hw, xPart_add, R1x, R2x]; abel
    have hwx := hΨx w
    rw [hxw] at hwx
    have hsplitΨ : xPart (Ψ w) = xPart (Ψ (R1L (n := n) (q := q) P y)) +
        xPart (Ψ (R2L (n := n) (q := q) γ Z (μf y))) := by rw [hw, map_add, xPart_add]
    have hu_sy : ∀ i, uPart (s y) i = uPart z0 i + uPart (s y - z0) i := by
      intro i; rw [uPart_sub]; simp
    have hL := hμf y
    have hLz : ∀ i, Z i → (S (μf y) + Q y) i = -(uPart y i + ⟪γ i, xPart (Ψ w)⟫) := by
      intro i hz
      rw [PiLp.add_apply, hS, hQ, if_pos hz, if_pos hz, hsplitΨ, inner_add_right]; ring
    rw [mem_normalCone_kkt]
    obtain ⟨rx, ru, rv⟩ := hres y (s y)
    refine ⟨fun i => ?_, ?_, ?_, fun i => ?_⟩
    · rw [hu_sy, due]
      by_cases hp : P i
      · have hz := hPZ i hp
        rw [if_neg hz, add_zero]
        have e1 := (abs_le.1 (abs_uPart_le (s y - z0) i)).1
        rw [due, if_neg hz, add_zero] at e1
        have := hmP i hp
        linarith
      · rw [hwn i hp, hu0n i hp, zero_add, zero_add]
        split_ifs with hz
        · exact (hL i).1
        · exact le_refl 0
    · rw [rx, dxe, dve]
      have hsum : ∑ i, uPart (s y - z0) i • γ i =
          ∑ i, (if P i then uPart (Ψ w) i else 0) • γ i +
            ∑ i ∈ Finset.univ.filter Z, μf y i • γ i := by
        rw [sum_filter_smul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [due, ← add_smul]
        congr 1
        by_cases hp : P i
        · simp [hp, hPZ i hp]
        · rw [if_neg hp, hwn i hp]
      rw [hsum]
      rw [show L (xPart (Ψ w)) + (∑ i, (if P i then uPart (Ψ w) i else 0) • γ i +
          ∑ i ∈ Finset.univ.filter Z, μf y i • γ i) + ∑ j, vPart (Ψ w) j • η j =
          (L (xPart (Ψ w)) + ∑ i, (if P i then uPart (Ψ w) i else 0) • γ i +
            ∑ j, vPart (Ψ w) j • η j) + ∑ i ∈ Finset.univ.filter Z, μf y i • γ i by abel, hwx]
      abel
    · ext j; rw [rv, dxe, hwv]; simp
    · rw [ru, dxe, hu_sy, due]
      by_cases hp : P i
      · rw [hgP i hp, hwP i hp]; simp
      · rw [hwn i hp, hu0n i hp]
        by_cases hz : Z i
        · rw [hgZ i hz, if_pos hz]
          have h1 := hLz i hz
          obtain ⟨a1, a2, a3⟩ := hL i
          rw [h1] at a2 a3
          constructor
          · linarith
          · simp only [zero_add, add_zero]; nlinarith
        · rw [if_neg hz]
          have := hIneg y (s y) i hy hsV hp hz
          rw [dxe] at this
          exact ⟨this.le, by ring⟩
  · -- uniqueness
    intro z hz hN
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [mem_normalCone_kkt] at hN
    obtain ⟨hzu, hx', hv', hc'⟩ := hN
    obtain ⟨rx, ru, rv⟩ := hres y z
    have hI0 : ∀ i, ¬ P i → ¬ Z i → uPart z i = 0 := by
      intro i h1 h2
      have hneg := hIneg y z i hy hz h1 h2
      rw [← ru] at hneg
      have := (hc' i).2
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
    have hu_dz : ∀ i, uPart (z - z0) i = uPart z i - uPart z0 i := fun i => by simp
    have hu0n' : ∀ i, ¬ P i → z0 (Sum.inr (Sum.inl i)) = 0 := fun i hi => by
      simpa using hu0n i hi
    have hI0' : ∀ i, ¬ P i → ¬ Z i → z (Sum.inr (Sum.inl i)) = 0 := fun i h1 h2 => by
      simpa using hI0 i h1 h2
    have hPr : ∀ i, P i → ⟪γ i, xPart (z - z0)⟫ = -uPart y i := by
      intro i hp
      have hpos : 0 < uPart z i := by
        have e1 := (abs_le.1 (abs_uPart_le (z - z0) i)).1
        rw [hu_dz] at e1
        have := hmP i hp; linarith
      have := (hc' i).2
      rcases mul_eq_zero.1 this with h | h
      · rw [ru, hgP i hp] at h; linarith
      · linarith
    obtain ⟨μ', hμ'⟩ : ∃ μ' : EuclideanSpace ℝ (Fin p),
        μ' = WithLp.toLp 2 fun i => if Z i then uPart z i else 0 := ⟨_, rfl⟩
    obtain ⟨w', hw'⟩ : ∃ w', w' = R1L (n := n) (q := q) P y + R2L (n := n) (q := q) γ Z μ' :=
      ⟨_, rfl⟩
    have hdz1 : z - z0 - EL (n := n) (q := q) Z μ' = Ψ w' := by
      apply hΨu
      apply kkt_ext
      · rw [phi_x (L := L) (γ := γ) (η := η) (P := P), hw', xPart_add, R1x, R2x, xPart_sub, Ex, sub_zero, vPart_sub, Ev,
          sub_zero]
        have := hx'; rw [rx] at this
        have hsum : ∑ i, uPart (z - z0) i • γ i =
            ∑ i ∈ Finset.univ.filter P, uPart (z - z0 - EL (n := n) (q := q) Z μ') i • γ i +
              ∑ i ∈ Finset.univ.filter Z, μ' i • γ i := by
          rw [sum_filter_smul, sum_filter_smul, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← add_smul]; congr 1
          by_cases hp : P i
          · have hE : (EL (n := n) (q := q) Z μ') (Sum.inr (Sum.inl i)) = 0 := by
              have := Eu μ' i; rw [if_neg (hPZ i hp)] at this; simpa using this
            simp [hp, hE, hPZ i hp]
          · by_cases hzz : Z i
            · simp [hp, hzz, hμ', hu0n' i hp]
            · simp [hp, hzz, hu0n' i hp, hI0' i hp hzz]
        rw [hsum, sub_eq_zero] at this
        rw [this]; abel
      · ext i
        rw [phi_u (L := L) (γ := γ) (η := η) (P := P), hw', uPart_add, PiLp.add_apply, R1u, R2u, xPart_sub, Ex, sub_zero]
        by_cases hp : P i
        · rw [if_pos hp, if_pos hp, hPr i hp]; simp
        · rw [if_neg hp, if_neg hp, uPart_sub, PiLp.sub_apply, Eu, hu_dz]
          by_cases hzz : Z i
          · simp [hzz, hμ', hu0n' i hp]
          · simp [hzz, hu0n' i hp, hI0' i hp hzz]
      · ext j
        rw [phi_v (L := L) (γ := γ) (η := η) (P := P), hw', vPart_add, PiLp.add_apply, R1v, R2v, xPart_sub, Ex, sub_zero]
        have := congrArg (fun t => t j) hv'
        simp only [PiLp.zero_apply] at this
        rw [rv] at this
        rw [add_zero]; linarith
    have hLCP : IsLCP S (Q y) μ' := by
      intro i
      by_cases hzz : Z i
      · have hxx : xPart (Ψ w') = xPart (z - z0) := by rw [← hdz1, xPart_sub, Ex, sub_zero]
        have e : (S μ' + Q y) i = -(uPart y i + gv i + ⟪γ i, xPart (z - z0)⟫) := by
          rw [PiLp.add_apply, hS, hQ, if_pos hzz, if_pos hzz, hgZ i hzz, ← hxx, hw', map_add,
            xPart_add, inner_add_right]; ring
        rw [e, ← ru]
        have hμi : μ' i = uPart z i := by simp [hμ', hzz]
        rw [hμi]
        obtain ⟨c1, c2⟩ := hc' i
        exact ⟨hzu i, by linarith, by nlinarith⟩
      · have hμi : μ' i = 0 := by simp [hμ', hzz]
        rw [PiLp.add_apply, hS, hQ, if_neg hzz, if_neg hzz, hμi]; simp
    have hμeq := hμu y μ' hLCP
    rw [hs, ← hμeq, ← hw', ← hdz1]; abel


theorem theorem_4_1_core {n p q : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ Ω)
    (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (hθ : DifferentiableOn ℝ θ Ω)
    (hg : ∀ i, DifferentiableOn ℝ (fun x => g x i) Ω)
    (hh : ∀ j, DifferentiableOn ℝ (fun x => h x j) Ω)
    (hθ2 : DifferentiableAt ℝ (gradient θ) x0)
    (hg2 : ∀ i, DifferentiableAt ℝ (gradient (fun x => g x i)) x0)
    (hh2 : ∀ j, DifferentiableAt ℝ (gradient (fun x => h x j)) x0)
    (u0 : EuclideanSpace ℝ (Fin p)) (v0 : EuclideanSpace ℝ (Fin q))
    (hsol : -(kktMap θ g h (mk x0 u0 v0)) ∈ RobinsonSR.Reduction.normalCone (kktCone n p q) (mk x0 u0 v0))
    (hSSOSC : ∀ y : EuclideanSpace ℝ (Fin n), y ≠ 0 →
      (∀ i, 0 < u0 i → ⟪gradient (fun x => g x i) x0, y⟫ = 0) →
      (∀ j, ⟪gradient (fun x => h x j) x0, y⟫ = 0) →
      0 < ⟪y, lagHess θ g h x0 u0 v0 y⟫)
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun i : {i : Fin p // g x0 i = 0} => gradient (fun x => g x i) x0)
        (fun j : Fin q => gradient (fun x => h x j) x0))) :
    StronglyRegularAt (kktMap θ g h) (kktCone n p q) (mk x0 u0 v0) := by
  classical
  obtain ⟨DF, hDFd, hDF⟩ := kkt_deriv hΩ x0 hx0 θ g h hg hh hθ2 hg2 hh2 u0 v0
  refine ⟨DF, hDFd, ?_⟩
  rw [mem_normalCone_kkt] at hsol
  obtain ⟨hu0, hx, hv, hu⟩ := hsol
  have kx : xPart (kktMap θ g h (mk x0 u0 v0)) = lagGrad θ g h x0 u0 v0 := by simp [kktMap]
  have ku : ∀ i, uPart (kktMap θ g h (mk x0 u0 v0)) i = -g x0 i := fun i => by simp [kktMap]
  have kv : vPart (kktMap θ g h (mk x0 u0 v0)) = -h x0 := by simp [kktMap]
  simp only [uPart_mk] at hu0
  have hlag : lagGrad θ g h x0 u0 v0 = 0 := by rw [xPart_neg, kx, neg_eq_zero] at hx; exact hx
  have hh0 : h x0 = 0 := by rw [vPart_neg, kv, neg_neg] at hv; exact hv
  have hgle : ∀ i, g x0 i ≤ 0 := fun i => by
    have := (hu i).1; rw [uPart_neg, PiLp.neg_apply, ku] at this; linarith
  have hcs : ∀ i, g x0 i * u0 i = 0 := fun i => by
    have := (hu i).2; rw [uPart_neg, PiLp.neg_apply, ku, uPart_mk] at this; linarith
  set P : Fin p → Prop := fun i => 0 < u0 i with hPdef
  set Z : Fin p → Prop := fun i => g x0 i = 0 ∧ u0 i = 0 with hZdef
  have hPZ : ∀ i, P i → ¬ Z i := fun i hp hz => by
    simp only [hPdef, hZdef] at hp hz; linarith [hz.2]
  have hBin : ∀ i, ¬ P i → ¬ Z i → g x0 i ≠ 0 := by
    intro i h1 h2 hg0
    simp only [hPdef, hZdef, not_lt, not_and] at h1 h2
    exact h2 hg0 (le_antisymm h1 (hu0 i))
  have hLI' : ∀ (α : Fin p → ℝ) (β : Fin q → ℝ), (∀ i, ¬ P i → ¬ Z i → α i = 0) →
      ∑ i, α i • gradient (fun x => g x i) x0 + ∑ j, β j • gradient (fun x => h x j) x0 = 0 →
      (∀ i, α i = 0) ∧ ∀ j, β j = 0 := by
    intro α β hα hsum
    have hvan : ∀ i, g x0 i ≠ 0 → α i = 0 := by
      intro i hne
      by_contra hαi
      by_cases h1 : P i
      · exact hne (by
          have := hcs i; simp only [hPdef] at h1
          rcases mul_eq_zero.1 this with h | h
          · exact h
          · linarith)
      · by_cases h2 : Z i
        · exact hne h2.1
        · exact hαi (hα i h1 h2)
    have hsub : ∑ i, α i • gradient (fun x => g x i) x0 =
        ∑ i : {i : Fin p // g x0 i = 0}, α i • gradient (fun x => g x i) x0 := by
      rw [← Finset.sum_filter_of_ne (p := fun i => g x0 i = 0)]
      · exact Finset.sum_subtype _ (fun i => by simp) (fun i => α i • gradient (fun x => g x i) x0)
      · intro i _ hne
        by_contra hb
        exact hne (by rw [hvan i hb, zero_smul])
    have key := Fintype.linearIndependent_iff.1 hLI
      (Sum.elim (fun i : {i : Fin p // g x0 i = 0} => α i) β) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [← hsub]; exact hsum)
    refine ⟨fun i => ?_, fun j => ?_⟩
    · by_cases hb : g x0 i = 0
      · exact key (Sum.inl ⟨i, hb⟩)
      · exact hvan i hb
    · exact key (Sum.inr j)
  exact linear_sr (lagHess θ g h x0 u0 v0) (fun i => gradient (fun x => g x i) x0)
    (fun j => gradient (fun x => h x j) x0) P Z hSSOSC hLI' hPZ (mk x0 u0 v0) (fun i => g x0 i)
    (fun i hi => by simpa using hi)
    (fun i hi => by simp only [uPart_mk]; simp only [hPdef, not_lt] at hi; linarith [hu0 i])
    (fun i hi => by
      have := hcs i; simp only [hPdef] at hi
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · linarith)
    (fun i hi => hi.1)
    (fun i h1 h2 => lt_of_le_of_ne (hgle i) (hBin i h1 h2))
    (kktMap θ g h (mk x0 u0 v0)) (by rw [kx, hlag]) (fun i => ku i) (by rw [kv, hh0, neg_zero])
    DF hDF

end main
end RobinsonSR.NLP

open RobinsonSR.NLP


theorem solution {n p q : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ Ω)
    (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (hθ : DifferentiableOn ℝ θ Ω)
    (hg : ∀ i, DifferentiableOn ℝ (fun x => g x i) Ω)
    (hh : ∀ j, DifferentiableOn ℝ (fun x => h x j) Ω)
    (hθ2 : DifferentiableAt ℝ (gradient θ) x0)
    (hg2 : ∀ i, DifferentiableAt ℝ (gradient (fun x => g x i)) x0)
    (hh2 : ∀ j, DifferentiableAt ℝ (gradient (fun x => h x j)) x0)
    (u0 : EuclideanSpace ℝ (Fin p)) (v0 : EuclideanSpace ℝ (Fin q))
    (hsol : -(kktMap θ g h (mk x0 u0 v0)) ∈ RobinsonSR.Reduction.normalCone (kktCone n p q) (mk x0 u0 v0))
    (hSSOSC : ∀ y : EuclideanSpace ℝ (Fin n), y ≠ 0 →
      (∀ i, 0 < u0 i → ⟪gradient (fun x => g x i) x0, y⟫ = 0) →
      (∀ j, ⟪gradient (fun x => h x j) x0, y⟫ = 0) →
      0 < ⟪y, lagHess θ g h x0 u0 v0 y⟫)
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun i : {i : Fin p // g x0 i = 0} => gradient (fun x => g x i) x0)
        (fun j : Fin q => gradient (fun x => h x j) x0))) :
    StronglyRegularAt (kktMap θ g h) (kktCone n p q) (mk x0 u0 v0) := by
  exact theorem_4_1_core Ω hΩ x0 hx0 θ g h hθ hg hh hθ2 hg2 hh2 u0 v0 hsol hSSOSC hLI
