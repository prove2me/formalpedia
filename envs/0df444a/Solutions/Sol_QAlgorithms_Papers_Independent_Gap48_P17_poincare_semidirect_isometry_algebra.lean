-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P17.poincare_semidirect_isometry_algebra
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:29:48.176579+00:00
-- url     : https://prove2.me/submissions/e894db1a-8666-4ca1-a765-bcc336941dbb

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17
open QAlgorithms.Papers.Independent.Gap48.P17

section
open NormedSpace

theorem g74c_exp_entry {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    AnalyticOnNhd ℝ (fun t : ℝ => (exp (t • X)) i j) Set.univ ∧
    HasDerivAt (fun t : ℝ => (exp (t • X)) i j) (X i j) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℝ) := FiniteDimensional.complete ℝ _
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let Lc := LinearMap.toContinuousLinearMap L
  have hL : ∀ M, Lc M = M i j := fun _ => rfl
  constructor
  · intro t _
    have h1 : AnalyticAt ℝ (fun u : ℝ => u • X) t := analyticAt_id.smul analyticAt_const
    have h2 : AnalyticAt ℝ (fun u : ℝ => exp (u • X)) t :=
      AnalyticAt.comp (g := exp) (f := fun u : ℝ => u • X) (exp_analytic (𝕂 := ℝ) _) h1
    have h3 := Lc.analyticAt _ |>.comp h2
    exact h3
  · have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
    have h3 := Lc.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h3
    exact h3

end

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

section
set_option linter.unusedSectionVars false
variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

theorem g74c_sign_sq {t : K} (h : IsSign t) : t * t = 1 := by
  rcases h with rfl | rfl <;> norm_num

theorem g74c_cva (rho : SpinRepresentation g S) (v : Fin d → K) :
    cliffordVectorAction rho v = rho.action (CliffordAlgebra.ι (cliffordQ g) v) := rfl

theorem g74c_even_comm (rho : SpinRepresentation g S) (A : Module.End K S) (τ : K)
    (hτ : IsSign τ) (hA : ∀ v, cliffordVectorAction rho v * A = τ • (A * cliffordVectorAction rho v))
    (a : CliffordAlgebra.even (cliffordQ g)) : rho.action a.val * A = A * rho.action a.val := by
  obtain ⟨x, hx⟩ := a
  change rho.action x * A = A * rho.action x
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r A
  | add x y hx hy ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, ← g74c_cva, ← g74c_cva]
    have h1 : cliffordVectorAction rho m₁ * (cliffordVectorAction rho m₂ * A) =
        A * (cliffordVectorAction rho m₁ * cliffordVectorAction rho m₂) := by
      rw [hA, mul_smul_comm, ← mul_assoc, hA, smul_mul_assoc, smul_smul, g74c_sign_sq hτ,
        one_smul, mul_assoc]
    rw [mul_assoc, mul_assoc, ih, ← mul_assoc (cliffordVectorAction rho m₂),
      ← mul_assoc (cliffordVectorAction rho m₁), h1]
    simp only [mul_assoc]

theorem g74c_form_gen (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S) (τ σ : K)
    (h : FormSigns rho b τ σ) (u v : Fin d → K) (s t : S) :
    b (spinGenerator rho u v s) t = - b s (spinGenerator rho u v t) := by
  obtain ⟨hτ, -, hc, -⟩ := h
  have key : ∀ x y : Fin d → K, ∀ s t, b ((cliffordVectorAction rho x * cliffordVectorAction rho y) s) t
      = b s ((cliffordVectorAction rho y * cliffordVectorAction rho x) t) := by
    intro x y s t
    simp only [Module.End.mul_apply]
    rw [hc, hc, ← mul_assoc, g74c_sign_sq hτ, one_mul]
  simp only [spinGenerator, LinearMap.smul_apply, LinearMap.sub_apply, map_smul, map_sub,
    LinearMap.smul_apply, LinearMap.sub_apply, key, smul_eq_mul]
  ring

theorem g74c_inv (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S) (τ σ : K)
    (h : FormSigns rho b τ σ) : b ∈ invariantForms rho := by
  intro u v s t
  rw [g74c_form_gen rho b τ σ h]; ring

theorem g74c_isSign_mul {a b : K} (ha : IsSign a) (hb : IsSign b) : IsSign (a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [IsSign]

end
section
set_option linter.unusedSectionVars false
variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

theorem g74c_polar (x y : Fin d → K) :
    QuadraticMap.polar (cliffordQ g) x y = -(g.toBilin' x y + g.toBilin' y x) := by
  unfold cliffordQ Matrix.toQuadraticForm'
  rw [LinearMap.BilinMap.polar_toQuadraticMap]
  simp [Matrix.toBilin'_apply', Matrix.toLinearMap₂'_apply', Matrix.neg_mulVec]
  ring

theorem g74c_rel (rho : SpinRepresentation g S) (x y : Fin d → K) :
    cliffordVectorAction rho x * cliffordVectorAction rho y =
      (QuadraticMap.polar (cliffordQ g) x y) • 1 - cliffordVectorAction rho y * cliffordVectorAction rho x := by
  have h := congrArg rho.action (CliffordAlgebra.ι_mul_ι_add_swap (Q := cliffordQ g) x y)
  rw [map_add, map_mul, map_mul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one] at h
  rw [← h, g74c_cva, g74c_cva]; abel

theorem g74c_comm_calc {A : Type*} [Ring A] [Algebra K A] (X Y Z : A) (a b c : K)
    (hXY : Y * X = a • 1 - X * Y) (hYZ : Y * Z = b • 1 - Z * Y) (hXZ : X * Z = c • 1 - Z * X) :
    ((1/4 : K) • (X * Y - Y * X)) * Z - Z * ((1/4 : K) • (X * Y - Y * X)) =
      (-(c/2)) • Y + (b/2) • X := by
  have h3 : X * Y * Z = b • X - c • Y + Z * X * Y := by
    rw [mul_assoc, hYZ, mul_sub, mul_smul_comm, mul_one, ← mul_assoc, hXZ, sub_mul,
      smul_mul_assoc, one_mul, mul_assoc]; abel
  rw [hXY]
  simp only [smul_sub, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h3,
    ← mul_assoc]
  module

end
section
set_option linter.unusedSectionVars false
variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

theorem g74c_vec_gen (rho : SpinRepresentation g S) (hg : ∀ x y, g.toBilin' x y = g.toBilin' y x)
    (u v x : Fin d → K) :
    cliffordVectorAction rho (vectorGenerator g u v x) =
      spinGenerator rho u v * cliffordVectorAction rho x -
        cliffordVectorAction rho x * spinGenerator rho u v := by
  unfold spinGenerator
  rw [g74c_comm_calc _ _ _ _ _ _ (g74c_rel rho v u) (g74c_rel rho v x) (g74c_rel rho u x),
    g74c_polar, g74c_polar, hg x u, hg x v]
  simp only [vectorGenerator, map_sub, map_smul]
  module

end

theorem g74c_sig_symm (p q : ℕ) (x y : Fin (p + q) → ℝ) :
    (signatureMatrix p q).toBilin' x y = (signatureMatrix p q).toBilin' y x := by
  simp only [signatureMatrix, Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem g74c_sig_single (p q : ℕ) (x : Fin (p + q) → ℝ) (i : Fin (p + q)) :
    (signatureMatrix p q).toBilin' x (Pi.single i 1) = x i * (if i.val < p then 1 else -1) := by
  simp only [signatureMatrix, Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

/-- Section 1.1, PDF p. 6: the complete semidirect/standard-action statement and the
isometry Lie algebra. The latter uses actual smooth group curves. No assertion
about a radical, reductivity, or causal cones is added. -/
theorem solution (p q : ℕ) :
    (∀ z : Matrix (Fin (p + q)) (Fin (p + q)) ℝ × (Fin (p + q) → ℝ),
      z ∈ poincareSpace p q ↔ IsometryVelocity p q z) ∧
    (∀ x y, x ∈ poincareSpace p q → y ∈ poincareSpace p q →
      poincareBracket x y ∈ poincareSpace p q) ∧
    (∀ x y : Matrix (Fin (p + q)) (Fin (p + q)) ℝ × (Fin (p + q) → ℝ),
      poincareBracket x y = -poincareBracket y x) ∧
    (∀ x y z : Matrix (Fin (p + q)) (Fin (p + q)) ℝ × (Fin (p + q) → ℝ),
      poincareBracket x (poincareBracket y z) + poincareBracket y (poincareBracket z x) +
        poincareBracket z (poincareBracket x y) = 0) ∧
    (∀ v w : (Fin (p + q) → ℝ), poincareBracket (0, v) (0, w) = (0, 0)) ∧
    (∀ (A : orthogonalSpace p q) (v w : (Fin (p + q) → ℝ)),
      poincareBracket (A.val, v) (0, w) = (0, A.val.mulVec w)) ∧
    (∀ f : (Fin (p + q) → ℝ) ≃ (Fin (p + q) → ℝ),
      (∀ x y, (signatureMatrix p q).toBilin' (f x - f y) (f x - f y) =
        (signatureMatrix p q).toBilin' (x - y) (x - y)) →
      ∃ (A : Matrix (Fin (p + q)) (Fin (p + q)) ℝ) (b : (Fin (p + q) → ℝ)),
        AffineIsometryCoefficients p q A ∧ ∀ x, f x = A.mulVec x + b) ∧
    (∀ (A : Matrix (Fin (p + q)) (Fin (p + q)) ℝ) (b : (Fin (p + q) → ℝ)),
      AffineIsometryCoefficients p q A →
      ∃ f : metricIsometryGroup p q, ∀ x, f.val x = A.mulVec x + b) := by
  have hεsq : ∀ i : Fin (p + q), signatureMatrix p q i i * signatureMatrix p q i i = 1 := by
    intro i; simp only [signatureMatrix, Matrix.diagonal_apply_eq]; split_ifs <;> norm_num
  have hgg : signatureMatrix p q * signatureMatrix p q = 1 := by
    simp only [signatureMatrix, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> norm_num
  have hgdet : (signatureMatrix p q).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hgg
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hBsym := g74c_sig_symm p q
  have hBnd : ∀ w : Fin (p + q) → ℝ, (∀ v, (signatureMatrix p q).toBilin' w v = 0) → w = 0 := by
    intro w hw; funext i
    have := hw (Pi.single i 1)
    rw [g74c_sig_single] at this
    simp only [Pi.zero_apply]
    split_ifs at this <;> linarith
  have hmemP : ∀ z : Matrix (Fin (p + q)) (Fin (p + q)) ℝ × (Fin (p + q) → ℝ),
      z ∈ poincareSpace p q ↔ (Matrix.transpose z.1) * signatureMatrix p q = signatureMatrix p q * (-z.1) := by
    intro z
    simp only [poincareSpace, Submodule.mem_prod, Submodule.mem_top, and_true,
      LieSubalgebra.mem_toSubmodule, orthogonalSpace, mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  have hiso_comp : ∀ A : Matrix (Fin (p + q)) (Fin (p + q)) ℝ, ∀ u v,
      ((Matrix.transpose A) * signatureMatrix p q * A).toBilin' u v =
        (signatureMatrix p q).toBilin' (A.mulVec u) (A.mulVec v) := by
    intro A u v
    rw [← Matrix.toBilin'_comp, LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply,
      Matrix.toLin'_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [hmemP]
    constructor
    · intro hX
      refine ⟨fun t => NormedSpace.exp (t • z.1), fun t => t • z.2, by simp, by simp, ?_, ?_, ?_,
        ?_, ?_⟩
      · exact contDiff_pi.mpr fun i => contDiff_pi.mpr fun j =>
          (g74c_exp_entry z.1 i j).1.contDiff
      · exact contDiff_id.smul contDiff_const
      · refine Filter.Eventually.of_forall fun t => ?_
        refine ⟨?_, ?_⟩
        · exact ((Matrix.isUnit_exp (t • z.1)).map Matrix.detMonoidHom).ne_zero
        · have hzt : Matrix.transpose z.1 = signatureMatrix p q * (-z.1) * signatureMatrix p q := by
            rw [← hX, Matrix.mul_assoc, hgg, Matrix.mul_one]
          have hT : (Matrix.transpose (t • z.1)) = signatureMatrix p q * (-(t • z.1)) * (signatureMatrix p q)⁻¹ := by
            rw [Matrix.inv_eq_left_inv hgg, Matrix.transpose_smul, hzt]
            simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul]
          have hgu : IsUnit (signatureMatrix p q) :=
            (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hgdet)
          show Matrix.transpose (NormedSpace.exp (t • z.1)) * signatureMatrix p q *
            NormedSpace.exp (t • z.1) = signatureMatrix p q
          rw [← Matrix.exp_transpose, hT, Matrix.exp_conj _ _ hgu, Matrix.exp_neg,
            Matrix.inv_eq_left_inv hgg]
          have hu := Matrix.isUnit_exp (t • z.1)
          set E := NormedSpace.exp (t • z.1)
          rw [show signatureMatrix p q * E⁻¹ * signatureMatrix p q * signatureMatrix p q * E =
            signatureMatrix p q * E⁻¹ * (signatureMatrix p q * signatureMatrix p q) * E by
              simp only [Matrix.mul_assoc], hgg, Matrix.mul_one, Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.mul_one]
      · exact hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => (g74c_exp_entry z.1 i j).2
      · simpa using (hasDerivAt_id (0 : ℝ)).smul_const z.2
    · rintro ⟨A, b, hA0, -, -, -, hev, hAd, -⟩
      ext i j
      have hent : ∀ k l, HasDerivAt (fun t => A t k l) (z.1 k l) 0 := fun k l =>
        hasDerivAt_pi.mp (hasDerivAt_pi.mp hAd k) l
      have hfun : ∀ t, ((Matrix.transpose (A t)) * signatureMatrix p q * A t) i j =
          ∑ k, A t k i * (signatureMatrix p q k k * A t k j) := by
        intro t
        rw [Matrix.mul_apply]
        simp only [signatureMatrix, Matrix.mul_diagonal, Matrix.transpose_apply,
          Matrix.diagonal_apply_eq]
        exact Finset.sum_congr rfl fun k _ => by ring
      have hd : HasDerivAt (fun t => ∑ k, A t k i * (signatureMatrix p q k k * A t k j))
          (∑ k, (z.1 k i * (signatureMatrix p q k k * A 0 k j) +
            A 0 k i * (signatureMatrix p q k k * z.1 k j))) 0 :=
        HasDerivAt.fun_sum (fun k _ => (hent k i).mul ((hent k j).const_mul _))
      have hc : HasDerivAt (fun t => ∑ k, A t k i * (signatureMatrix p q k k * A t k j)) 0 0 := by
        refine (hasDerivAt_const (0 : ℝ) (signatureMatrix p q i j)).congr_of_eventuallyEq ?_
        filter_upwards [hev] with t ht
        rw [← hfun, ht.2]
      have hu := hd.unique hc
      rw [hA0] at hu
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul,
        Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
        if_true] at hu
      simp only [Matrix.transpose_apply, signatureMatrix, Matrix.mul_diagonal,
        Matrix.diagonal_mul, Matrix.neg_apply]
      simp only [signatureMatrix, Matrix.diagonal_apply_eq] at hu
      linarith
  · intro x y hx hy
    rw [hmemP] at hx hy ⊢
    simp only [poincareBracket]
    have h1 : ∀ a b : Matrix (Fin (p + q)) (Fin (p + q)) ℝ,
        Matrix.transpose a * signatureMatrix p q = signatureMatrix p q * (-a) →
        Matrix.transpose b * signatureMatrix p q = signatureMatrix p q * (-b) →
        Matrix.transpose (a * b) * signatureMatrix p q = signatureMatrix p q * (b * a) := by
      intro a b ha hb
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ha, ← Matrix.mul_assoc, Matrix.mul_neg, hb]
      simp [Matrix.mul_assoc]
    rw [Matrix.transpose_sub, Matrix.sub_mul, h1 _ _ hx hy, h1 _ _ hy hx, Matrix.mul_neg,
      Matrix.mul_sub]
    abel
  · intro x y
    refine Prod.ext ?_ ?_ <;> simp [poincareBracket]
  · intro x y z
    refine Prod.ext ?_ ?_
    · simp only [poincareBracket, Prod.fst_add, Prod.fst_zero]; noncomm_ring
    · simp only [poincareBracket, Prod.snd_add, Prod.snd_zero, Matrix.mulVec_sub,
        Matrix.sub_mulVec, Matrix.mulVec_mulVec]
      abel
  · intro v w; simp [poincareBracket]
  · intro A v w; simp [poincareBracket]
  · intro f hf
    obtain ⟨F, hF⟩ : ∃ F : (Fin (p + q) → ℝ) → (Fin (p + q) → ℝ), ∀ x, F x = f x - f 0 :=
      ⟨_, fun _ => rfl⟩
    set B := (signatureMatrix p q).toBilin' with hB
    have hexp : ∀ a b, B (a - b) (a - b) = B a a - 2 * B a b + B b b := by
      intro a b
      simp only [map_sub, LinearMap.sub_apply]
      rw [hBsym b a]; ring
    have hQ : ∀ x y, B (F x - F y) (F x - F y) = B (x - y) (x - y) := by
      intro x y
      have : F x - F y = f x - f y := by rw [hF, hF]; abel
      rw [this, hf]
    have hQ0 : ∀ x, B (F x) (F x) = B x x := by
      intro x
      have := hQ x 0
      have h0 : F 0 = 0 := by rw [hF, sub_self]
      rwa [h0, sub_zero, sub_zero] at this
    have hpol : ∀ x y, B (F x) (F y) = B x y := by
      intro x y
      have h1 := hQ x y
      rw [hexp, hexp, hQ0, hQ0] at h1
      linarith
    have hsurj : ∀ v, ∃ x, F x = v := fun v => ⟨f.symm (v + f 0), by rw [hF]; simp⟩
    have hadd : ∀ x y, F (x + y) = F x + F y := by
      intro x y
      rw [← sub_eq_zero, sub_add_eq_sub_sub]
      apply hBnd
      intro v
      obtain ⟨z, rfl⟩ := hsurj v
      simp only [map_sub, LinearMap.sub_apply, hpol, map_add, LinearMap.add_apply]
      ring
    have hsmul : ∀ (c : ℝ) x, F (c • x) = c • F x := by
      intro c x
      rw [← sub_eq_zero]
      apply hBnd
      intro v
      obtain ⟨z, rfl⟩ := hsurj v
      simp only [map_sub, LinearMap.sub_apply, hpol, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    let L : (Fin (p + q) → ℝ) →ₗ[ℝ] (Fin (p + q) → ℝ) :=
      { toFun := F, map_add' := hadd, map_smul' := hsmul }
    have hAL : ∀ x, (LinearMap.toMatrix' L).mulVec x = F x := by
      intro x
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl
    have hiso : (Matrix.transpose (LinearMap.toMatrix' L)) * signatureMatrix p q * LinearMap.toMatrix' L =
        signatureMatrix p q := by
      apply Matrix.toBilin'.injective
      refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
      rw [hiso_comp, hAL, hAL]
      exact hpol u v
    refine ⟨LinearMap.toMatrix' L, f 0, ⟨?_, hiso⟩, fun x => by rw [hAL, hF, sub_add_cancel]⟩
    intro h0
    have := congrArg Matrix.det hiso
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at this
    exact hgdet this.symm
  · intro A b hA
    obtain ⟨hdet, hiso⟩ := hA
    have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
    let e : (Fin (p + q) → ℝ) ≃ (Fin (p + q) → ℝ) :=
      { toFun := fun x => A.mulVec x + b
        invFun := fun y => A⁻¹.mulVec (y - b)
        left_inv := fun x => by
          simp only [add_sub_cancel_right, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
            Matrix.one_mulVec]
        right_inv := fun y => by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec,
            sub_add_cancel] }
    refine ⟨⟨e, fun x y => ?_⟩, fun x => rfl⟩
    show (signatureMatrix p q).toBilin' (A.mulVec x + b - (A.mulVec y + b)) (A.mulVec x + b - (A.mulVec y + b)) = _
    rw [add_sub_add_right_eq_sub, ← Matrix.mulVec_sub, ← hiso_comp, hiso]
