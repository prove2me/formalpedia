-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P06.environment_no_information
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:21:04.306185+00:00
-- url     : https://prove2.me/submissions/bda098fa-d469-411f-b7d4-bbfd1f4921e7

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P06

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq
def g73c_y {R Q : Type*} [Fintype Q] (A : Matrix Q Q ℂ) (psi : EuclideanSpace ℂ (R × Q)) :
    EuclideanSpace ℂ (R × Q) :=
  WithLp.toLp 2 (fun z => ∑ i, A z.2 i * psi (z.1, i))

lemma g73c_Fe_trace {R Q : Type*} [Fintype R] [Fintype Q] {K : Type*} [Fintype K] (E : K → Matrix Q Q ℂ)
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

lemma g73c_F_trace {Q : Type*} [Fintype Q] {K : Type*} [Fintype K] (E : K → Matrix Q Q ℂ)
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

lemma g73c_kraus_norm {Q : Type*} [Fintype Q] [DecidableEq Q] {K : Type*} [Fintype K] (E : K → Matrix Q Q ℂ)
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

lemma g73c_ys_norm {R Q : Type*} [Fintype R] [Fintype Q] [DecidableEq Q] {K : Type*} [Fintype K]
    (E : K → Matrix Q Q ℂ) (hE : IsKrausFamily E) (psi : EuclideanSpace ℂ (R × Q)) :
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


def g73c_F {Q E : Type*} [Fintype Q] [Fintype E] (U : Matrix.unitaryGroup (Q × E) ℂ)
    (eta : EuclideanSpace ℂ E) (e : E) : Matrix Q Q ℂ :=
  Matrix.of fun q q' => ∑ t, (U : Matrix (Q × E) (Q × E) ℂ) (q, e) (q', t) * eta t

lemma g73c_conj_kron {Q E : Type*} [Fintype Q] [Fintype E] (U : Matrix.unitaryGroup (Q × E) ℂ)
    (eta : EuclideanSpace ℂ E) (X : Matrix Q Q ℂ) (q q2 : Q) (e e2 : E) :
    conjSuperop (U : Matrix (Q × E) (Q × E) ℂ) (Matrix.kronecker X (pureDensity eta)) (q, e) (q2, e2) =
      (g73c_F U eta e * X * (g73c_F U eta e2)ᴴ) q q2 := by
  simp only [conjSuperop, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    pureDensity, Matrix.of_apply, Matrix.conjTranspose_apply, g73c_F, Fintype.sum_prod_type,
    star_sum, star_mul', Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma g73c_dil_eq {Q E : Type*} [Fintype Q] [Fintype E] (U : Matrix.unitaryGroup (Q × E) ℂ)
    (eta : EuclideanSpace ℂ E) (X : Matrix Q Q ℂ) :
    dilationChannel U eta X = krausApply (g73c_F U eta) X := by
  ext q q2
  simp only [dilationChannel, traceRight, Matrix.of_apply, krausApply, Matrix.sum_apply,
    g73c_conj_kron]

lemma g73c_env_eq {Q E : Type*} [Fintype Q] [Fintype E] (U : Matrix.unitaryGroup (Q × E) ℂ)
    (eta : EuclideanSpace ℂ E) (X : Matrix Q Q ℂ) (e e2 : E) :
    environmentOutput U eta X e e2 = (g73c_F U eta e * X * (g73c_F U eta e2)ᴴ).trace := by
  simp only [environmentOutput, traceLeft, Matrix.of_apply, Matrix.trace, Matrix.diag,
    g73c_conj_kron]

lemma g73c_F_kraus {Q E : Type*} [Fintype Q] [Fintype E]
    (U : Matrix.unitaryGroup (Q × E) ℂ)
    (eta : EuclideanSpace ℂ E) (heta : ‖eta‖ = 1) : IsKrausFamily (g73c_F U eta) := by
  have hU : star (U : Matrix (Q × E) (Q × E) ℂ) * (U : Matrix (Q × E) (Q × E) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem U.2
  have hUe : ∀ a b : Q × E, ∑ z, conj ((U : Matrix (Q × E) (Q × E) ℂ) z a) *
      (U : Matrix (Q × E) (Q × E) ℂ) z b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hU a) b
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using this
  have heta2 : ∑ t, conj (eta t) * eta t = 1 := by
    have h := EuclideanSpace.norm_sq_eq eta
    rw [heta, one_pow] at h
    have : ∀ t, conj (eta t) * eta t = ((‖eta t‖ ^ 2 : ℝ) : ℂ) := by
      intro t; rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [this]; rw [← Complex.ofReal_sum, ← h]; simp
  unfold IsKrausFamily
  ext q1 q2
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, g73c_F,
    Matrix.of_apply, star_sum, star_mul', Complex.star_def, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  rw [Finset.sum_comm]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  have : ∀ x i, ∑ z : Q × E, (starRingEnd ℂ) ((U : Matrix (Q × E) (Q × E) ℂ) z (q1, i)) *
      (starRingEnd ℂ) (eta i) * ((U : Matrix (Q × E) (Q × E) ℂ) z (q2, x) * eta x) =
      (if (q1, i) = (q2, x) then 1 else 0) * ((starRingEnd ℂ) (eta i) * eta x) := by
    intro x i
    rw [← hUe, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [this]
  by_cases hq : q1 = q2
  · subst hq
    simp only [Prod.mk.injEq, true_and, Matrix.one_apply_eq, ite_mul, one_mul, zero_mul]
    rw [← heta2]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_ite_eq']; simp
  · simp [hq, Matrix.one_apply_ne hq]

lemma g73c_dvec {R Q E : Type*} [Fintype R] [Fintype Q] [Fintype E]
    (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (psi : EuclideanSpace ℂ (R × Q)) (a : R) (q : Q) (e : E) :
    dilatedVector U eta psi (a, (q, e)) = Matrix.toEuclideanLin (g73c_F U eta e) (g73c_w psi a) q := by
  simp only [dilatedVector, act, Matrix.mulVec, dotProduct, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.toEuclideanLin_apply, g73c_F, g73c_w, Matrix.of_apply,
    Fintype.sum_prod_type, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_mul, PiLp.toLp_apply]
  rw [Fintype.sum_eq_single a (fun x hx => by simp [Ne.symm hx])]
  simp only [if_true]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma g73c_polar {Q : Type*} [Fintype Q] [DecidableEq Q] {K : Type*} [Fintype K]
    (D : K → Matrix Q Q ℂ) (hD : IsKrausFamily D) (x y : EuclideanSpace ℂ Q) :
    ∑ k, inner ℂ (Matrix.toEuclideanLin (D k) x) (Matrix.toEuclideanLin (D k) y) = inner ℂ x y := by
  have h : ∀ k, inner ℂ (Matrix.toEuclideanLin (D k) x) (Matrix.toEuclideanLin (D k) y) =
      inner ℂ x (Matrix.toEuclideanLin ((D k)ᴴ * D k) y) := by
    intro k
    have : Matrix.toEuclideanLin ((D k)ᴴ * D k) y =
        (Matrix.toEuclideanLin (D k)).adjoint (Matrix.toEuclideanLin (D k) y) := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
    rw [this, LinearMap.adjoint_inner_right]
  simp_rw [h]
  have hs : ∑ k, Matrix.toEuclideanLin ((D k)ᴴ * D k) y = y := by
    rw [← LinearMap.sum_apply, ← map_sum]
    unfold IsKrausFamily at hD
    rw [hD]; simp
  rw [← inner_sum, hs]

lemma g73c_tr_pure {Q : Type*} [Fintype Q] [DecidableEq Q] (A B : Matrix Q Q ℂ)
    (v : EuclideanSpace ℂ Q) :
    (A * pureDensity v * Bᴴ).trace =
      inner ℂ (Matrix.toEuclideanLin B v) (Matrix.toEuclideanLin A v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply,
    Matrix.conjTranspose_apply, PiLp.inner_apply, RCLike.inner_apply, Matrix.toEuclideanLin_apply,
    Matrix.mulVec, dotProduct, map_sum, map_mul, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

lemma g73c_tl_sum {R Q : Type*} [Fintype R] (psi : EuclideanSpace ℂ (R × Q)) :
    traceLeft (pureDensity psi) = ∑ a, pureDensity (g73c_w psi a) := by
  ext q q2
  simp [traceLeft, pureDensity, g73c_w, Matrix.sum_apply]

lemma g73c_comp {Q E K : Type*} [Fintype Q] [Fintype E] [Fintype K]
    (D : K → Matrix Q Q ℂ) (F : E → Matrix Q Q ℂ) (X : Matrix Q Q ℂ) :
    krausApply D (krausApply F X) = krausApply (fun ke : K × E => D ke.1 * F ke.2) X := by
  simp only [krausApply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma g73c_comp_kraus {Q E K : Type*} [Fintype Q] [Fintype E] [Fintype K] [DecidableEq Q]
    (D : K → Matrix Q Q ℂ) (F : E → Matrix Q Q ℂ) (hD : IsKrausFamily D) (hF : IsKrausFamily F) :
    IsKrausFamily (fun ke : K × E => D ke.1 * F ke.2) := by
  unfold IsKrausFamily at *
  simp only [Fintype.sum_prod_type, Matrix.conjTranspose_mul]
  rw [Finset.sum_comm]
  have : ∀ e, ∑ k, (F e)ᴴ * (D k)ᴴ * (D k * F e) = (F e)ᴴ * F e := by
    intro e
    have h1 : ∀ k, (F e)ᴴ * (D k)ᴴ * (D k * F e) = (F e)ᴴ * ((D k)ᴴ * D k) * F e := by
      intro k; simp only [Matrix.mul_assoc]
    simp_rw [h1]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hD, Matrix.mul_one]
  simp_rw [this, hF]

lemma g73c_mem_range {Q : Type*} [Fintype Q] [DecidableEq Q] (rho : Matrix Q Q ℂ)
    (hH : rho.IsHermitian) (v : EuclideanSpace ℂ Q)
    (h : ∀ u, Matrix.toEuclideanLin rho u = 0 → inner ℂ v u = 0) :
    v ∈ LinearMap.range (Matrix.toEuclideanLin rho) := by
  have h1 : LinearMap.range (Matrix.toEuclideanLin rho) =
      (LinearMap.ker (Matrix.toEuclideanLin rho))ᗮ := by
    rw [LinearMap.orthogonal_ker, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hH.eq]
  rw [h1, Submodule.mem_orthogonal]
  intro u hu
  rw [← inner_conj_symm, h u (LinearMap.mem_ker.1 hu), map_zero]

lemma g73c_pure_apply {Q : Type*} [Fintype Q] [DecidableEq Q] (v u : EuclideanSpace ℂ Q) :
    Matrix.toEuclideanLin (pureDensity v) u = (inner ℂ v u) • v := by
  ext q
  simp only [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, pureDensity, Matrix.of_apply,
    PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply, PiLp.toLp_apply,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma g73c_ens_mem {Q : Type*} [Fintype Q] [DecidableEq Q] (m : ℕ) (p : Fin m → ℝ)
    (v : Fin m → EuclideanSpace ℂ Q) (hp : ∀ i, 0 ≤ p i) (i : Fin m) (hpi : 0 < p i) :
    v i ∈ LinearMap.range (Matrix.toEuclideanLin (∑ j, (p j : ℂ) • pureDensity (v j))) := by
  apply g73c_mem_range
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_smul]
    congr 1
    · simp [Complex.star_def]
    · ext a b; simp [pureDensity, Matrix.conjTranspose_apply, mul_comm]
  · intro u hu
    have h0 : inner ℂ u (Matrix.toEuclideanLin (∑ j, (p j : ℂ) • pureDensity (v j)) u) = 0 := by
      rw [hu, inner_zero_right]
    rw [map_sum, LinearMap.sum_apply, inner_sum] at h0
    simp_rw [map_smul, LinearMap.smul_apply, g73c_pure_apply, inner_smul_right] at h0
    have hre := congrArg Complex.re h0
    simp only [Complex.zero_re, Complex.re_sum] at hre
    have hterm : ∀ j, ((p j : ℂ) * (inner ℂ (v j) u * inner ℂ u (v j))).re =
        p j * ‖inner ℂ (v j) u‖ ^ 2 := by
      intro j
      rw [← inner_conj_symm u (v j), Complex.re_ofReal_mul, g73c_re_mul_conj]
    simp_rw [hterm] at hre
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ p j * ‖inner ℂ (v j) u‖ ^ 2 :=
      fun j _ => mul_nonneg (hp j) (by positivity)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hre i (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hpi.ne'
    · exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)

lemma g73c_lin_mul {Q : Type*} [Fintype Q] [DecidableEq Q] (A B : Matrix Q Q ℂ)
    (v : EuclideanSpace ℂ Q) :
    Matrix.toEuclideanLin (A * B) v = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

/-- PDF pp.17--18: perfect correction implies reference-environment independence
and the same environmental density for every positive-weight component of every
pure-state ensemble of rho. No converse is asserted in this node. -/
theorem solution {R Q E : Type*}
    [Fintype R] [Fintype Q] [Fintype E] [Nonempty R] [Nonempty Q] [Nonempty E]
    (rho : Matrix Q Q ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (R × Q)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho)
    (f : Superop Q Q) (hf : IsChannel f)
    (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (heta : ‖eta‖ = 1) (hdil : ∀ X, f X = dilationChannel U eta X)
    (hcorr : ∃ d : Superop Q Q, IsChannel d ∧ inputEntanglementFidelity psi (d ∘ f) = 1) :
    referenceEnvironment U eta psi =
      Matrix.kronecker (traceRight (pureDensity psi)) (environmentOutput U eta rho) ∧
    (∀ (m : ℕ) (p : Fin m → ℝ) (v : Fin m → EuclideanSpace ℂ Q),
      (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 → (∀ i, ‖v i‖ = 1) →
      (∑ i, (p i : ℂ) • pureDensity (v i)) = rho →
      ∀ i, 0 < p i → environmentOutput U eta (pureDensity (v i)) =
        environmentOutput U eta rho) := by
  obtain ⟨d, hd, hfid⟩ := hcorr
  obtain ⟨md, D, hDk, hdD⟩ := hd
  have hFk : IsKrausFamily (g73c_F U eta) := g73c_F_kraus U eta heta
  have hfF : ∀ X, f X = krausApply (g73c_F U eta) X := fun X => (hdil X).trans (g73c_dil_eq U eta X)
  have hGk := g73c_comp_kraus D (g73c_F U eta) hDk hFk
  have hdf : d ∘ f = krausApply (fun ke : Fin md × E => D ke.1 * g73c_F U eta ke.2) := by
    funext X
    rw [Function.comp_apply, hdD, hfF, g73c_comp]
  rw [hdf] at hfid
  subst hpur
  have hFe : ∑ g : Fin md × E, ‖inner ℂ psi (g73c_y (D g.1 * g73c_F U eta g.2) psi)‖ ^ 2 = 1 := by
    rw [← hfid]
    unfold inputEntanglementFidelity effectProb
    rw [g73c_Fe_trace, Complex.re_sum]
    simp_rw [g73c_re_mul_conj]
  have hy1 : ∑ g : Fin md × E, ‖g73c_y (D g.1 * g73c_F U eta g.2) psi‖ ^ 2 = 1 := by
    rw [g73c_ys_norm _ hGk, hpsi, one_pow]
  have hc := g73c_collinear psi hpsi _ hy1 hFe
  set c : Fin md × E → ℂ := fun g => inner ℂ psi (g73c_y (D g.1 * g73c_F U eta g.2) psi) with hcdef
  have hGv : ∀ g : Fin md × E, ∀ v ∈ LinearMap.range (Matrix.toEuclideanLin (traceLeft (pureDensity psi))),
      Matrix.toEuclideanLin (D g.1 * g73c_F U eta g.2) v = c g • v :=
    fun g v hv => g73c_act_range _ psi _ (hc g) v hv
  set M : E → E → ℂ := fun e e' => ∑ k, conj (c (k, e')) * c (k, e) with hM
  have hkey : ∀ e e' (v v' : EuclideanSpace ℂ Q),
      v ∈ LinearMap.range (Matrix.toEuclideanLin (traceLeft (pureDensity psi))) →
      v' ∈ LinearMap.range (Matrix.toEuclideanLin (traceLeft (pureDensity psi))) →
      inner ℂ (Matrix.toEuclideanLin (g73c_F U eta e') v') (Matrix.toEuclideanLin (g73c_F U eta e) v) =
        M e e' * inner ℂ v' v := by
    intro e e' v v' hv hv'
    rw [← g73c_polar D hDk]
    simp_rw [← g73c_lin_mul]
    rw [hM, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hGv (k, e') v' hv', hGv (k, e) v hv, inner_smul_left, inner_smul_right]
    ring
  have hw := g73c_w_mem psi (g73c_tl_herm psi)
  have hsumw : ∑ a, inner ℂ (g73c_w psi a) (g73c_w psi a) = 1 := by
    have := g73c_psi_norm psi
    rw [hpsi, one_pow] at this
    have h3 : ∀ a, inner ℂ (g73c_w psi a) (g73c_w psi a) = ((‖g73c_w psi a‖ ^ 2 : ℝ) : ℂ) := by
      intro a; rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    simp_rw [h3]
    rw [← Complex.ofReal_sum, ← this, Complex.ofReal_one]
  have henv : ∀ e e', environmentOutput U eta (traceLeft (pureDensity psi)) e e' = M e e' := by
    intro e e'
    rw [g73c_env_eq, g73c_tl_sum, Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum]
    simp_rw [g73c_tr_pure]
    rw [Finset.sum_congr rfl fun a _ => hkey e e' _ _ (hw a) (hw a), ← Finset.mul_sum, hsumw,
      mul_one]
  constructor
  · ext ⟨a, e⟩ ⟨b, e'⟩
    rw [Matrix.kronecker, Matrix.kroneckerMap_apply, henv]
    have h1 : referenceEnvironment U eta psi (a, e) (b, e') =
        inner ℂ (Matrix.toEuclideanLin (g73c_F U eta e') (g73c_w psi b))
          (Matrix.toEuclideanLin (g73c_F U eta e) (g73c_w psi a)) := by
      simp only [referenceEnvironment, pureDensity, Matrix.of_apply, g73c_dvec, PiLp.inner_apply,
        RCLike.inner_apply]
      all_goals exact Finset.sum_congr rfl fun _ _ => by ring
    have h2 : traceRight (pureDensity psi) a b = inner ℂ (g73c_w psi b) (g73c_w psi a) := by
      simp only [traceRight, pureDensity, Matrix.of_apply, PiLp.inner_apply, RCLike.inner_apply,
        g73c_w]
      all_goals exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h1, h2, hkey e e' _ _ (hw a) (hw b)]
    ring
  · intro m p v hp _ hv hens i hpi
    have hvi : v i ∈ LinearMap.range (Matrix.toEuclideanLin (traceLeft (pureDensity psi))) := by
      rw [← hens]; exact g73c_ens_mem m p v hp i hpi
    ext e e'
    rw [henv, g73c_env_eq, g73c_tr_pure, hkey e e' _ _ hvi hvi, inner_self_eq_norm_sq_to_K, hv i]
    simp
