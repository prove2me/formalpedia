-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P14.povmDistance_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T12:02:39.250048+00:00
-- url     : https://prove2.me/submissions/c6116dab-0444-4f4e-aa9c-360155d33edb

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14
noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms QAlgorithms.QuditFidelity QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

instance g58d_prob' (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

instance g58d_haar' (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar; infer_instance

theorem g58d_cc {d : ℕ} (i j : Fin d) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => (U : Matrix (Fin d) (Fin d) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

def g58d_q {n : ℕ} (i0 : Fin n) (D : Matrix (Fin n) (Fin n) ℂ) (U : Matrix.unitaryGroup (Fin n) ℂ) : ℝ :=
  (∑ a, ∑ b, conj ((U : Matrix (Fin n) (Fin n) ℂ) a i0) * D a b * (U : Matrix (Fin n) (Fin n) ℂ) b i0).re

theorem g58d_q_cont {n : ℕ} (i0 : Fin n) (D : Matrix (Fin n) (Fin n) ℂ) : Continuous (g58d_q i0 D) := by
  unfold g58d_q
  exact Complex.continuous_re.comp (continuous_finset_sum _ (fun a _ => continuous_finset_sum _ (fun b _ =>
    ((Complex.continuous_conj.comp (g58d_cc _ _)).mul continuous_const).mul (g58d_cc _ _))))

theorem g58d_pd {n : ℕ} (hh : 0 < n) (D : Matrix (Fin n) (Fin n) ℂ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    effectProb D (pureDensity (act (U : Matrix (Fin n) (Fin n) ℂ) (ket ⟨0, hh⟩))) = g58d_q ⟨0, hh⟩ D U := by
  simp only [effectProb, pureDensity, act, ket, g58d_q, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.of_apply, Matrix.mulVec, dotProduct]
  simp only [PiLp.ofLp_single, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem g58d_dist {n m : ℕ} (hh : 0 < n) (P Q : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    povmDistance hh P Q = ∫ U, ∑ i, (g58d_q ⟨0, hh⟩ (P i - Q i) U) ^ 2 ∂QAlgorithms.Schur.unitaryHaar n := by
  unfold povmDistance haarPureStateLaw
  have hc : Continuous (fun psi : EuclideanSpace ℂ (Fin n) =>
      ∑ i, (effectProb (P i - Q i) (pureDensity psi)) ^ 2) := by
    unfold effectProb pureDensity; fun_prop
  rw [integral_map (haarState_continuous n hh).measurable.aemeasurable hc.aestronglyMeasurable]
  simp only [g58d_pd]

theorem g58d_intc {n : ℕ} {f : Matrix.unitaryGroup (Fin n) ℂ → ℝ} (hf : Continuous f) :
    Integrable f (QAlgorithms.Schur.unitaryHaar n) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem g58d_q_comb {n : ℕ} (i0 : Fin n) (P Q Q2 : Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    g58d_q i0 (P - ((t : ℂ) • Q + ((1 - t : ℝ) : ℂ) • Q2)) U =
      t * g58d_q i0 (P - Q) U + (1 - t) * g58d_q i0 (P - Q2) U := by
  unfold g58d_q
  rw [← Complex.re_ofReal_mul, ← Complex.re_ofReal_mul, ← Complex.add_re]
  congr 1
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => ?_))
  push_cast; ring

theorem g58d_q_conj {n : ℕ} (i0 : Fin n) (V : Matrix.unitaryGroup (Fin n) ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    g58d_q i0 ((V : Matrix (Fin n) (Fin n) ℂ) * D * (V : Matrix (Fin n) (Fin n) ℂ)ᴴ) U = g58d_q i0 D (V⁻¹ * U) := by
  have hc : ((V⁻¹ * U : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      (V : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ) := rfl
  unfold g58d_q
  rw [hc]
  congr 1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, map_sum, map_mul,
    Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  simp only [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv
    { toFun := fun x : Fin n × Fin n × Fin n × Fin n => (x.2.2.2, x.2.2.1, x.2.1, x.1)
      invFun := fun y : Fin n × Fin n × Fin n × Fin n => (y.2.2.2, y.2.2.1, y.2.1, y.1)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  intro x
  simp only [Equiv.coe_fn_mk]; ring

lemma g58d_conj_eig {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix n n ℂ) * Y * (hY.eigenvectorUnitary : Matrix n n ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) := by
  have hs := hY.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hu := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize (Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) : Matrix n n ℂ) = D at *
  subst hs
  calc star U * (U * D * star U) * U
      = (star U * U) * D * (star U * U) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, one_mul, mul_one]

theorem g58d_perm_mem' {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    (Matrix.of fun a b => if a = τ b then (1 : ℂ) else 0) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.star_apply, Matrix.one_apply]
  have hh : ∀ x, (b = τ x) ↔ (x = τ.symm b) := by
    intro x; constructor <;> intro h <;> subst h <;> simp
  simp [apply_ite, hh]

theorem g58d_herm_zero {n : ℕ} (i0 : Fin n) (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian)
    (h : ∀ U, g58d_q i0 D U = 0) : D = 0 := by
  set E := (hD.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hEdef
  have hEu : E ∈ Matrix.unitaryGroup (Fin n) ℂ := hD.eigenvectorUnitary.2
  have hk : ∀ k, hD.eigenvalues k = 0 := by
    intro k
    let Uk : Matrix.unitaryGroup (Fin n) ℂ :=
      ⟨E * Matrix.of (fun a b => if a = (Equiv.swap i0 k) b then (1 : ℂ) else 0),
        Submonoid.mul_mem _ hEu (g58d_perm_mem' _)⟩
    have hcol : ∀ a, (Uk : Matrix (Fin n) (Fin n) ℂ) a i0 = E a k := by
      intro a
      simp [Uk, Matrix.mul_apply, Equiv.swap_apply_left]
    have h1 := h Uk
    unfold g58d_q at h1
    simp only [hcol] at h1
    have h2 := congrFun (congrFun (g58d_conj_eig hD) k) k
    rw [← hEdef] at h2
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply_eq, Function.comp,
      RCLike.star_def, Finset.sum_mul] at h2
    have h2' : (∑ x, ∑ x_1, (starRingEnd ℂ) (E x k) * D x x_1 * E x_1 k) = ((hD.eigenvalues k : ℝ) : ℂ) := by
      rw [Finset.sum_comm]; exact h2
    have h3 := congrArg Complex.re h2'
    rw [h1, Complex.ofReal_re] at h3
    exact h3.symm
  have hz : star E * D * E = 0 := by
    rw [g58d_conj_eig hD]
    ext a b
    simp [Matrix.diagonal_apply, hk]
  have hu : E * star E = 1 := Unitary.mul_star_self_of_mem hEu
  have hu' : star E * E = 1 := Unitary.star_mul_self_of_mem hEu
  calc D = (E * star E) * D * (E * star E) := by rw [hu, Matrix.one_mul, Matrix.mul_one]
    _ = E * (star E * D * E) * star E := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hz, Matrix.mul_zero, Matrix.zero_mul]

theorem solution {h m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (P Q : Fin m → (Matrix (Fin h) (Fin h) ℂ)) (hP : IsPOVM P) (hQ : IsPOVM Q) :
    0 ≤ povmDistance hh P Q ∧
    (povmDistance hh P Q = 0 ↔ ∀ i, P i = Q i) ∧
    (∀ Q2 : Fin m → (Matrix (Fin h) (Fin h) ℂ), IsPOVM Q2 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      povmDistance hh P ((t : ℂ) • Q + ((1-t : ℝ) : ℂ) • Q2) ≤
        t*povmDistance hh P Q + (1-t)*povmDistance hh P Q2) ∧
    (∀ U : Matrix.unitaryGroup (Fin h) ℂ,
      povmDistance hh (fun i => (U : (Matrix (Fin h) (Fin h) ℂ))*P i*(U : (Matrix (Fin h) (Fin h) ℂ))ᴴ)
        (fun i => (U : (Matrix (Fin h) (Fin h) ℂ))*Q i*(U : (Matrix (Fin h) (Fin h) ℂ))ᴴ) = povmDistance hh P Q) := by
  set i0 : Fin h := ⟨0, hh⟩
  have hc : ∀ (A : Fin m → Matrix (Fin h) (Fin h) ℂ),
      Continuous (fun U => ∑ i, (g58d_q i0 (A i) U) ^ 2) :=
    fun A => continuous_finset_sum _ (fun i _ => (g58d_q_cont _ _).pow 2)
  have hI : ∀ (A : Fin m → Matrix (Fin h) (Fin h) ℂ),
      Integrable (fun U => ∑ i, (g58d_q i0 (A i) U) ^ 2) (QAlgorithms.Schur.unitaryHaar h) :=
    fun A => g58d_intc (hc A)
  refine ⟨?_, ⟨fun h0 => ?_, fun he => ?_⟩, fun Q2 hQ2 t ht0 ht1 => ?_, fun V => ?_⟩
  · rw [g58d_dist]
    exact integral_nonneg (fun U => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  · rw [g58d_dist] at h0
    have hae := (integral_eq_zero_iff_of_nonneg (fun U => Finset.sum_nonneg (fun i _ => sq_nonneg _))
      (hI (fun i => P i - Q i))).mp h0
    have hF := (Continuous.ae_eq_iff_eq (QAlgorithms.Schur.unitaryHaar h) (hc (fun i => P i - Q i))
      continuous_const).mp hae
    intro i
    have hz : ∀ U, g58d_q i0 (P i - Q i) U = 0 := by
      intro U
      have h1 := congrFun hF U
      try simp only [Pi.zero_apply] at h1
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (g58d_q i0 (P j - Q j) U))).mp h1 i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
    exact sub_eq_zero.mp (g58d_herm_zero i0 _ ((hP.1 i).1.sub (hQ.1 i).1) hz)
  · rw [g58d_dist]
    have : ∀ i, P i - Q i = 0 := fun i => by rw [he i, sub_self]
    have hq0 : ∀ U, g58d_q i0 0 U = 0 := by intro U; simp [g58d_q]
    simp only [this]
    simp [g58d_q]
  · rw [g58d_dist, g58d_dist, g58d_dist]
    simp only [Pi.add_apply, Pi.smul_apply, g58d_q_comb]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hI _).const_mul _) ((hI _).const_mul _)]
    refine integral_mono (by
        have := hI (fun i => P i - ((t : ℂ) • Q i + ((1 - t : ℝ) : ℂ) • Q2 i))
        simpa only [g58d_q_comb] using this)
      (((hI _).const_mul _).add ((hI _).const_mul _)) (fun U => ?_)
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have h1t : 0 ≤ 1 - t := by linarith
    nlinarith [mul_nonneg ht0 h1t, sq_nonneg (g58d_q i0 (P i - Q i) U - g58d_q i0 (P i - Q2 i) U),
      mul_nonneg (mul_nonneg ht0 h1t) (sq_nonneg (g58d_q i0 (P i - Q i) U - g58d_q i0 (P i - Q2 i) U))]
  · rw [g58d_dist, g58d_dist]
    have e : ∀ i, (V : Matrix (Fin h) (Fin h) ℂ) * P i * (V : Matrix (Fin h) (Fin h) ℂ)ᴴ -
        (V : Matrix (Fin h) (Fin h) ℂ) * Q i * (V : Matrix (Fin h) (Fin h) ℂ)ᴴ =
        (V : Matrix (Fin h) (Fin h) ℂ) * (P i - Q i) * (V : Matrix (Fin h) (Fin h) ℂ)ᴴ := by
      intro i; rw [Matrix.mul_sub, Matrix.sub_mul]
    simp only [e, g58d_q_conj]
    exact integral_mul_left_eq_self (fun W => ∑ i, (g58d_q i0 (P i - Q i) W) ^ 2) V⁻¹
