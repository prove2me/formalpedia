-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P06.perfect_fidelity_iff_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:58:32.141288+00:00
-- url     : https://prove2.me/submissions/fe9e306e-6e7c-4613-a68c-5abb52d82b78

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P06

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq
def g73c_y {R Q : Type*} [Fintype Q] (A : Matrix Q Q ℂ) (psi : EuclideanSpace ℂ (R × Q)) :
    EuclideanSpace ℂ (R × Q) :=
  WithLp.toLp 2 (fun z => ∑ i, A z.2 i * psi (z.1, i))

lemma g73c_Fe_trace {R Q : Type*} [Fintype R] [Fintype Q] {m : ℕ} (E : Fin m → Matrix Q Q ℂ)
    (psi : EuclideanSpace ℂ (R × Q)) :
    ((pureDensity psi) * idTensorSuperop (krausApply E) (pureDensity psi)).trace =
      ∑ j, inner ℂ psi (g73c_y (E j) psi) * conj (inner ℂ psi (g73c_y (E j) psi)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, idTensorSuperop, krausApply,
    pureDensity, Matrix.of_apply, Matrix.sum_apply, Matrix.conjTranspose_apply, g73c_y,
    PiLp.inner_apply, RCLike.inner_apply, map_sum, map_mul, Complex.star_def,
    Complex.conj_conj]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, q]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, j, 2, p]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun x2 _ =>
    Finset.sum_congr rfl fun i _ => by ring

lemma g73c_F_trace {Q : Type*} [Fintype Q] {m : ℕ} (E : Fin m → Matrix Q Q ℂ)
    (v : EuclideanSpace ℂ Q) :
    ((pureDensity v) * krausApply E (pureDensity v)).trace =
      ∑ j, inner ℂ v (Matrix.toEuclideanLin (E j) v) *
        conj (inner ℂ v (Matrix.toEuclideanLin (E j) v)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, krausApply, Matrix.toEuclideanLin_apply,
    pureDensity, Matrix.of_apply, Matrix.sum_apply, Matrix.conjTranspose_apply, Matrix.mulVec,
    dotProduct, PiLp.inner_apply, RCLike.inner_apply, map_sum, map_mul, Complex.star_def,
    Complex.conj_conj]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, q]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, j, 2, p]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun x2 _ =>
    Finset.sum_congr rfl fun i _ => by ring

lemma g73c_re_mul_conj (z : ℂ) : (z * conj z).re = ‖z‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma g73c_kraus_norm {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ} (E : Fin m → Matrix Q Q ℂ)
    (hE : IsKrausFamily E) (v : EuclideanSpace ℂ Q) :
    ∑ j, ‖Matrix.toEuclideanLin (E j) v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h : ∀ j, ‖Matrix.toEuclideanLin (E j) v‖ ^ 2 =
      RCLike.re (inner ℂ (Matrix.toEuclideanLin ((E j)ᴴ * E j) v) v) := by
    intro j
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    have : Matrix.toEuclideanLin ((E j)ᴴ * E j) v =
        (Matrix.toEuclideanLin (E j)).adjoint (Matrix.toEuclideanLin (E j) v) := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
    rw [this, LinearMap.adjoint_inner_left]
  simp_rw [h]
  have hs : ∑ j, Matrix.toEuclideanLin ((E j)ᴴ * E j) v = v := by
    rw [← LinearMap.sum_apply, ← map_sum]
    unfold IsKrausFamily at hE
    rw [hE]; simp
  rw [← map_sum, ← sum_inner, hs, inner_self_eq_norm_sq]

def g73c_w {R Q : Type*} (psi : EuclideanSpace ℂ (R × Q)) (a : R) : EuclideanSpace ℂ Q :=
  WithLp.toLp 2 (fun q => psi (a, q))

lemma g73c_y_norm {R Q : Type*} [Fintype R] [Fintype Q] [DecidableEq Q] (A : Matrix Q Q ℂ)
    (psi : EuclideanSpace ℂ (R × Q)) :
    ‖g73c_y A psi‖ ^ 2 = ∑ a, ‖Matrix.toEuclideanLin A (g73c_w psi a)‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, g73c_y, g73c_w,
    Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]

lemma g73c_psi_norm {R Q : Type*} [Fintype R] [Fintype Q]
    (psi : EuclideanSpace ℂ (R × Q)) :
    ‖psi‖ ^ 2 = ∑ a, ‖g73c_w psi a‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, g73c_w]

lemma g73c_ys_norm {R Q : Type*} [Fintype R] [Fintype Q] [DecidableEq Q] {m : ℕ}
    (E : Fin m → Matrix Q Q ℂ) (hE : IsKrausFamily E) (psi : EuclideanSpace ℂ (R × Q)) :
    ∑ j, ‖g73c_y (E j) psi‖ ^ 2 = ‖psi‖ ^ 2 := by
  simp_rw [g73c_y_norm]
  rw [Finset.sum_comm, g73c_psi_norm]
  exact Finset.sum_congr rfl fun a _ => g73c_kraus_norm E hE _

lemma g73c_proj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x y : V)
    (hx : ‖x‖ = 1) : ‖y - (inner ℂ x y) • x‖ ^ 2 = ‖y‖ ^ 2 - ‖inner ℂ x y‖ ^ 2 := by
  rw [@norm_sub_sq ℂ, inner_smul_right, norm_smul, hx, ← inner_conj_symm, mul_one]
  have h1 : RCLike.re ((starRingEnd ℂ) (inner ℂ y x) * inner ℂ y x) = ‖inner ℂ y x‖ ^ 2 := by
    rw [mul_comm]; exact g73c_re_mul_conj _
  rw [h1, RCLike.norm_conj]
  ring

lemma g73c_collinear {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*}
    [Fintype ι] (x : V) (hx : ‖x‖ = 1) (y : ι → V) (hy : ∑ j, ‖y j‖ ^ 2 = 1)
    (h : ∑ j, ‖inner ℂ x (y j)‖ ^ 2 = 1) : ∀ j, y j = (inner ℂ x (y j)) • x := by
  have hle : ∀ j ∈ Finset.univ, ‖inner ℂ x (y j)‖ ^ 2 ≤ ‖y j‖ ^ 2 := by
    intro j _
    have := norm_inner_le_norm (𝕜 := ℂ) x (y j)
    rw [hx, one_mul] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (by rw [h, hy])
  intro j
  have := g73c_proj x (y j) hx
  rw [heq j (Finset.mem_univ _), sub_self] at this
  have h0 : ‖y j - (inner ℂ x (y j)) • x‖ = 0 := by
    exact (pow_eq_zero_iff two_ne_zero).1 this
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)

lemma g73c_act_range {R Q : Type*} [Fintype R] [Fintype Q] [DecidableEq Q] (A : Matrix Q Q ℂ)
    (psi : EuclideanSpace ℂ (R × Q)) (c : ℂ) (hy : g73c_y A psi = c • psi)
    (v : EuclideanSpace ℂ Q)
    (hv : v ∈ LinearMap.range (Matrix.toEuclideanLin (traceLeft (pureDensity psi)))) :
    Matrix.toEuclideanLin A v = c • v := by
  obtain ⟨u, rfl⟩ := hv
  have hp : ∀ a q, ∑ i, A q i * psi (a, i) = c * psi (a, q) := by
    intro a q
    have := congrArg (fun z : EuclideanSpace ℂ (R × Q) => z (a, q)) hy
    simpa [g73c_y] using this
  ext q
  simp only [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, traceLeft, pureDensity,
    Matrix.of_apply, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_toLp]
  calc ∑ i, A q i * ∑ q', (∑ a, psi (a, i) * conj (psi (a, q'))) * u q'
      = ∑ q', ∑ a, (∑ i, A q i * psi (a, i)) * (conj (psi (a, q')) * u q') := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q' _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring
    _ = c * ∑ q', (∑ a, psi (a, q) * conj (psi (a, q'))) * u q' := by
        simp only [hp, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun q' _ => Finset.sum_congr rfl fun a _ => by ring

lemma g73c_quad {R Q : Type*} [Fintype R] [Fintype Q] [DecidableEq Q]
    (psi : EuclideanSpace ℂ (R × Q)) (u : EuclideanSpace ℂ Q) :
    inner ℂ u (Matrix.toEuclideanLin (traceLeft (pureDensity psi)) u) =
      ∑ a, conj (inner ℂ (g73c_w psi a) u) * inner ℂ (g73c_w psi a) u := by
  simp only [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, traceLeft, pureDensity,
    Matrix.of_apply, PiLp.inner_apply, RCLike.inner_apply, g73c_w, WithLp.ofLp_toLp, map_sum,
    map_mul, Complex.conj_conj]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, q']; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun q' _ =>
    Finset.sum_congr rfl fun q _ => by ring

lemma g73c_w_mem {R Q : Type*} [Fintype R] [Fintype Q] [DecidableEq Q]
    (psi : EuclideanSpace ℂ (R × Q)) (hH : (traceLeft (pureDensity psi)).IsHermitian) (a : R) :
    g73c_w psi a ∈ LinearMap.range (Matrix.toEuclideanLin (traceLeft (pureDensity psi))) := by
  have h1 : LinearMap.range (Matrix.toEuclideanLin (traceLeft (pureDensity psi))) =
      (LinearMap.ker (Matrix.toEuclideanLin (traceLeft (pureDensity psi))))ᗮ := by
    rw [LinearMap.orthogonal_ker, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hH.eq]
  rw [h1, Submodule.mem_orthogonal]
  intro u hu
  have hq := g73c_quad psi u
  rw [LinearMap.mem_ker.1 hu, inner_zero_right] at hq
  have hre := congrArg Complex.re hq
  simp only [Complex.zero_re, Complex.re_sum] at hre
  have hnn : ∀ b ∈ Finset.univ, 0 ≤ (conj (inner ℂ (g73c_w psi b) u) * inner ℂ (g73c_w psi b) u).re := by
    intro b _
    rw [mul_comm, g73c_re_mul_conj]; positivity
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hre.symm a (Finset.mem_univ _)
  rw [mul_comm, g73c_re_mul_conj] at h0
  have : inner ℂ (g73c_w psi a) u = 0 := by
    have := (pow_eq_zero_iff two_ne_zero).1 h0
    exact norm_eq_zero.1 this
  rw [← inner_conj_symm, this, map_zero]

lemma g73c_scalar {Q : Type*} [Fintype Q]
    (V : Submodule ℂ (EuclideanSpace ℂ Q)) (T : EuclideanSpace ℂ Q →ₗ[ℂ] EuclideanSpace ℂ Q)
    (h : ∀ v ∈ V, ∃ c : ℂ, T v = c • v) : ∃ c : ℂ, ∀ v ∈ V, T v = c • v := by
  have hmaps : ∀ v ∈ V, T v ∈ V := by
    intro v hv
    obtain ⟨c, hc⟩ := h v hv
    rw [hc]; exact V.smul_mem c hv
  obtain ⟨a, ha⟩ := (T.restrict hmaps).exists_eq_smul_id_of_forall_notLinearIndependent (by
    intro v hli
    obtain ⟨c, hc⟩ := h v.1 v.2
    have hT : T.restrict hmaps v = c • v := by
      ext; simp [LinearMap.restrict_apply, hc]
    rw [LinearIndependent.pair_iff] at hli
    have := hli c (-1) (by rw [hT]; simp)
    norm_num at this)
  refine ⟨a, fun v hv => ?_⟩
  have := congrArg (fun F => (F ⟨v, hv⟩ : V).1) ha
  simpa [LinearMap.restrict_apply] using this

lemma g73c_tl_herm {R Q : Type*} [Fintype R] (psi : EuclideanSpace ℂ (R × Q)) :
    (traceLeft (pureDensity psi)).IsHermitian := by
  ext a b
  simp [traceLeft, pureDensity, Matrix.conjTranspose_apply, map_sum, mul_comm]

/-- PDF pp.6--7 (conclusion of Section 2): Fe=1 iff every normalized pure vector
in the support has input-output fidelity one, including every superposition. -/
theorem solution {R Q : Type*}
    [Fintype R] [Fintype Q] [Nonempty R] [Nonempty Q]
    (rho : Matrix Q Q ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (R × Q)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho)
    (f : Superop Q Q) (hf : IsChannel f) :
    inputEntanglementFidelity psi f = 1 ↔
      ∀ v : EuclideanSpace ℂ Q, ‖v‖ = 1 → v ∈ LinearMap.range (Matrix.toEuclideanLin rho) →
        effectProb (pureDensity v) (f (pureDensity v)) = 1 := by
  obtain ⟨m, E, hE, hfE⟩ := hf
  have hf' : f = krausApply E := funext hfE
  subst hf'
  subst hpur
  have hFe : inputEntanglementFidelity psi (krausApply E) =
      ∑ j, ‖inner ℂ psi (g73c_y (E j) psi)‖ ^ 2 := by
    unfold inputEntanglementFidelity effectProb
    rw [g73c_Fe_trace, Complex.re_sum]
    simp_rw [g73c_re_mul_conj]
  have hF : ∀ v : EuclideanSpace ℂ Q, effectProb (pureDensity v) (krausApply E (pureDensity v)) =
      ∑ j, ‖inner ℂ v (Matrix.toEuclideanLin (E j) v)‖ ^ 2 := by
    intro v
    unfold effectProb
    rw [g73c_F_trace, Complex.re_sum]
    simp_rw [g73c_re_mul_conj]
  have hy1 : ∑ j, ‖g73c_y (E j) psi‖ ^ 2 = 1 := by rw [g73c_ys_norm E hE, hpsi, one_pow]
  constructor
  · intro h1 v hv1 hvr
    rw [hFe] at h1
    have hc := g73c_collinear psi hpsi (fun j => g73c_y (E j) psi) hy1 h1
    have hTv : ∀ j, Matrix.toEuclideanLin (E j) v = (inner ℂ psi (g73c_y (E j) psi)) • v :=
      fun j => g73c_act_range _ psi _ (hc j) v hvr
    rw [hF]
    simp_rw [hTv, inner_smul_right, inner_self_eq_norm_sq_to_K, hv1]
    simpa using h1
  · intro h
    set V := LinearMap.range (Matrix.toEuclideanLin (traceLeft (pureDensity psi))) with hV
    have heig : ∀ j, ∀ v ∈ V, ∃ c : ℂ, Matrix.toEuclideanLin (E j) v = c • v := by
      intro j v hv
      by_cases hv0 : v = 0
      · exact ⟨0, by simp [hv0]⟩
      have hn : (‖v‖ : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero, norm_eq_zero]; exact hv0
      set x := ((‖v‖ : ℂ)⁻¹) • v with hx
      have hx1 : ‖x‖ = 1 := by
        rw [hx, norm_smul, norm_inv, Complex.norm_real, norm_norm]
        field_simp [norm_ne_zero_iff.2 hv0]
      have hxr : x ∈ V := V.smul_mem _ hv
      have h1 := h x hx1 hxr
      rw [hF] at h1
      have hcol := g73c_collinear x hx1 (fun j => Matrix.toEuclideanLin (E j) x)
        (by rw [g73c_kraus_norm E hE, hx1, one_pow]) h1 j
      refine ⟨inner ℂ x (Matrix.toEuclideanLin (E j) x), ?_⟩
      have hv' : v = (‖v‖ : ℂ) • x := by
        rw [hx, smul_smul, mul_inv_cancel₀ hn, one_smul]
      rw [hv', map_smul]
      conv_lhs => rw [hcol]
      rw [smul_comm]
    choose c hc using fun j => g73c_scalar V (Matrix.toEuclideanLin (E j)) (heig j)
    have hyc : ∀ j, g73c_y (E j) psi = c j • psi := by
      intro j
      ext z
      have h2 := hc j (g73c_w psi z.1) (g73c_w_mem psi (g73c_tl_herm psi) z.1)
      have h3 := congrArg (fun w : EuclideanSpace ℂ Q => w z.2) h2
      simpa [g73c_y, g73c_w, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct] using h3
    rw [hFe]
    simp_rw [hyc, inner_smul_right, inner_self_eq_norm_sq_to_K, hpsi] at hy1 ⊢
    simp_rw [norm_smul, hpsi] at hy1
    simpa using hy1
