-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.collectingSubspace_characterization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:34:11.191304+00:00
-- url     : https://prove2.me/submissions/2c35ef6d-5587-447e-a311-4dd3aa4ad988

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

lemma X7CS_act_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    QAlgorithms.act A (QAlgorithms.act B v) = QAlgorithms.act (A * B) v := by
  simp [QAlgorithms.act, Matrix.mulVec_mulVec]

lemma X7CS_act_inj {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ v, QAlgorithms.act A v = QAlgorithms.act B v) : A = B := by
  have : Matrix.toEuclideanLin A = Matrix.toEuclideanLin B := LinearMap.ext h
  exact Matrix.toEuclideanLin.injective this

lemma X7CS_projAct {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v : EuclideanSpace ℂ (Fin n)) :
    QAlgorithms.act (orthogonalProjector S) v = S.starProjection v := by
  have hv : v = ∑ j, v j • (WithLp.toLp 2 (fun k => if k = j then (1 : ℂ) else 0) :
      EuclideanSpace ℂ (Fin n)) := by
    ext i
    simp [Finset.sum_apply]
  conv_rhs => rw [hv]
  rw [map_sum]
  ext i
  simp only [map_smul, QAlgorithms.act, Matrix.mulVec, dotProduct, orthogonalProjector]
  simp [Finset.sum_apply, mul_comm]


lemma X7CS_proj_entry {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i j : Fin n) :
    orthogonalProjector S i j =
      inner ℂ (EuclideanSpace.single i (1 : ℂ)) (S.starProjection (EuclideanSpace.single j (1 : ℂ))) := by
  rw [EuclideanSpace.inner_single_left]
  have : (WithLp.toLp 2 (fun k => if k = j then (1 : ℂ) else 0) : EuclideanSpace ℂ (Fin n)) =
      EuclideanSpace.single j (1 : ℂ) := by
    ext k; simp
  simp [orthogonalProjector, this]

lemma X7CS_proj_herm {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    (orthogonalProjector S)ᴴ = orthogonalProjector S := by
  ext i j
  rw [Matrix.conjTranspose_apply, X7CS_proj_entry, X7CS_proj_entry,
    ← Submodule.inner_starProjection_left_eq_right, ← inner_conj_symm]
  simp

lemma X7CS_proj_idem {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    orthogonalProjector S * orthogonalProjector S = orthogonalProjector S := by
  apply X7CS_act_inj
  intro v
  rw [← X7CS_act_mul, X7CS_projAct, X7CS_projAct]
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

lemma X7CS_adjoin_inv {n : ℕ} (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : invariant G S) :
    invariant (Algebra.adjoin ℂ G : Set (Matrix (Fin n) (Fin n) ℂ)) S := by
  intro X hX
  induction hX using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap c =>
    intro v hv
    have : QAlgorithms.act (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) c) v = c • v := by
      ext i; simp [QAlgorithms.act, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    rw [this]; exact S.smul_mem c hv
  | add x y _ _ hx hy =>
    intro v hv
    have : QAlgorithms.act (x + y) v = QAlgorithms.act x v + QAlgorithms.act y v := by
      ext i; simp [QAlgorithms.act, Matrix.add_mulVec]
    rw [this]; exact S.add_mem (hx v hv) (hy v hv)
  | mul x y _ _ hx hy =>
    intro v hv
    rw [← X7CS_act_mul]; exact hx _ (hy v hv)


lemma X7CS_adj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v w : EuclideanSpace ℂ (Fin n)) :
    inner ℂ v (QAlgorithms.act Aᴴ w) = inner ℂ (QAlgorithms.act A v) w := by
  change inner ℂ v (Matrix.toEuclideanLin Aᴴ w) = inner ℂ (Matrix.toEuclideanLin A v) w
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

/-- S invariant under A implies Sᗮ invariant under Aᴴ. -/
lemma X7CS_perp {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ v ∈ S, QAlgorithms.act A v ∈ S) : ∀ w ∈ Sᗮ, QAlgorithms.act Aᴴ w ∈ Sᗮ := by
  intro w hw
  rw [Submodule.mem_orthogonal] at hw ⊢
  intro u hu
  rw [X7CS_adj]
  exact hw _ (h u hu)

lemma X7CS_perp' {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ v ∈ Sᗮ, QAlgorithms.act A v ∈ Sᗮ) : ∀ w ∈ S, QAlgorithms.act Aᴴ w ∈ S := by
  have := X7CS_perp Sᗮ A h
  rwa [Submodule.orthogonal_orthogonal] at this

/-- S and Sᗮ invariant implies commuting with the projector. -/
lemma X7CS_comm {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (A : Matrix (Fin n) (Fin n) ℂ)
    (h1 : ∀ v ∈ S, QAlgorithms.act A v ∈ S) (h2 : ∀ v ∈ Sᗮ, QAlgorithms.act A v ∈ Sᗮ) :
    orthogonalProjector S * A = A * orthogonalProjector S := by
  apply X7CS_act_inj
  intro v
  rw [← X7CS_act_mul, ← X7CS_act_mul, X7CS_projAct, X7CS_projAct]
  have hA : S.starProjection (QAlgorithms.act A (v - S.starProjection v)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff S).mpr (h2 _ (Submodule.sub_starProjection_mem_orthogonal v))
  have hB : S.starProjection (QAlgorithms.act A (S.starProjection v)) =
      QAlgorithms.act A (S.starProjection v) :=
    Submodule.starProjection_eq_self_iff.mpr (h1 _ (Submodule.starProjection_apply_mem _ _))
  have hlin : QAlgorithms.act A (v - S.starProjection v) =
      QAlgorithms.act A v - QAlgorithms.act A (S.starProjection v) :=
    map_sub (Matrix.toEuclideanLin A) _ _
  rw [hlin, map_sub, sub_eq_zero] at hA
  rw [hA, hB]

/-- commuting with the projector implies invariance -/
lemma X7CS_comm_inv {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : orthogonalProjector S * A = A * orthogonalProjector S) :
    ∀ v ∈ S, QAlgorithms.act A v ∈ S := by
  intro v hv
  have hPv : QAlgorithms.act (orthogonalProjector S) v = v := by
    rw [X7CS_projAct]; exact Submodule.starProjection_eq_self_iff.mpr hv
  rw [← hPv, X7CS_act_mul, ← h, ← X7CS_act_mul, X7CS_projAct]
  exact Submodule.starProjection_apply_mem _ _

lemma X7CS_exp_corner {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (A C : 𝔸) (hC : C * C = C) (h : C * A * C = A * C) :
    C * NormedSpace.exp A * C = NormedSpace.exp A * C := by
  have hp : ∀ k : ℕ, C * A ^ k * C = A ^ k * C := by
    intro k
    induction k with
    | zero => simp [hC]
    | succ k ih =>
      calc C * A ^ (k + 1) * C = C * A * (A ^ k * C) := by rw [pow_succ']; simp only [mul_assoc]
        _ = C * A * (C * A ^ k * C) := by rw [ih]
        _ = (C * A * C) * (A ^ k * C) := by simp only [mul_assoc]
        _ = A * C * (A ^ k * C) := by rw [h]
        _ = A * (C * A ^ k * C) := by simp only [mul_assoc]
        _ = A ^ (k + 1) * C := by rw [ih, pow_succ', mul_assoc]
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  rw [NormedSpace.exp_eq_tsum ℂ]
  dsimp only
  rw [← hs.tsum_mul_left, ← (hs.mul_left C).tsum_mul_right, ← hs.tsum_mul_right]
  congr 1
  funext k
  rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc, hp]

lemma X7CS_gen {n r : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    cpGenerator K V X = (∑ k, V k * X * (V k)ᴴ) - K * X - X * Kᴴ := by
  simp [cpGenerator, sandwich, LinearMap.sum_apply, Matrix.mul_assoc]

/-- invariance as a corner identity -/
lemma X7CS_inv_iff {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (A : Matrix (Fin n) (Fin n) ℂ) :
    (∀ v ∈ S, QAlgorithms.act A v ∈ S) ↔
      orthogonalProjector S * A * orthogonalProjector S = A * orthogonalProjector S := by
  constructor
  · intro h
    apply X7CS_act_inj
    intro v
    rw [← X7CS_act_mul, ← X7CS_act_mul, ← X7CS_act_mul, X7CS_projAct, X7CS_projAct]
    exact Submodule.starProjection_eq_self_iff.mpr (h _ (Submodule.starProjection_apply_mem _ _))
  · intro h v hv
    have hPv : QAlgorithms.act (orthogonalProjector S) v = v := by
      rw [X7CS_projAct]; exact Submodule.starProjection_eq_self_iff.mpr hv
    have e : QAlgorithms.act A v = QAlgorithms.act (orthogonalProjector S)
        (QAlgorithms.act (A * orthogonalProjector S) v) := by
      rw [X7CS_act_mul, ← Matrix.mul_assoc, h, ← X7CS_act_mul, hPv]
    rw [e, X7CS_projAct]
    exact Submodule.starProjection_apply_mem S _

lemma X7CS_alg {n r : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : P * P = P) (hH : Pᴴ = P)
    (hK : P * K * P = K * P) (hV : ∀ k, P * V k * P = V k * P) (X : Matrix (Fin n) (Fin n) ℂ) :
    P * cpGenerator K V (P * X * P) * P = cpGenerator K V (P * X * P) := by
  have hPP : ∀ Y : Matrix (Fin n) (Fin n) ℂ, P * (P * Y) = P * Y := by
    intro Y; rw [← Matrix.mul_assoc, hP]
  have hVh : ∀ k, P * (V k)ᴴ * P = P * (V k)ᴴ := by
    intro k
    have := congrArg Matrix.conjTranspose (hV k)
    simpa [Matrix.conjTranspose_mul, hH, Matrix.mul_assoc] using this
  have hKh : P * Kᴴ * P = P * Kᴴ := by
    have := congrArg Matrix.conjTranspose hK
    simpa [Matrix.conjTranspose_mul, hH, Matrix.mul_assoc] using this
  rw [X7CS_gen]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    calc P * (V k * (P * X * P) * (V k)ᴴ) * P
        = (P * V k * P) * X * (P * (V k)ᴴ * P) := by simp only [Matrix.mul_assoc, hPP]
      _ = V k * (P * X * P) * (V k)ᴴ := by rw [hV, hVh]; simp only [Matrix.mul_assoc]
  · calc P * (K * (P * X * P)) * P = (P * K * P) * X * (P * P) := by simp only [Matrix.mul_assoc]
      _ = K * (P * X * P) := by rw [hK, hP]; simp only [Matrix.mul_assoc]
  · calc P * (P * X * P * Kᴴ) * P = (P * P) * X * (P * Kᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = P * X * P * Kᴴ := by rw [hKh, hP]; simp only [Matrix.mul_assoc]


open scoped ComplexOrder in
lemma X7CS_ii_iii {n r : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : P * P = P) (hH : Pᴴ = P)
    (E : P * cpGenerator K V P * P = cpGenerator K V P) :
    P * K * P = K * P ∧ ∀ k, P * V k * P = V k * P := by
  set Q : Matrix (Fin n) (Fin n) ℂ := 1 - P with hQdef
  have hPQ : P * Q = 0 := by rw [hQdef, Matrix.mul_sub, Matrix.mul_one, hP, sub_self]
  have hQP : Q * P = 0 := by rw [hQdef, Matrix.sub_mul, Matrix.one_mul, hP, sub_self]
  have hPQ' : ∀ Y : Matrix (Fin n) (Fin n) ℂ, P * (Q * Y) = 0 := by
    intro Y; rw [← Matrix.mul_assoc, hPQ, Matrix.zero_mul]
  have hQP' : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Q * (P * Y) = 0 := by
    intro Y; rw [← Matrix.mul_assoc, hQP, Matrix.zero_mul]
  have hQH : Qᴴ = Q := by rw [hQdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH]
  have E1 : Q * cpGenerator K V P * Q = 0 := by
    rw [← E]; simp only [Matrix.mul_assoc, hPQ, hQP', Matrix.mul_zero, Matrix.zero_mul]
  have E2 : Q * cpGenerator K V P * P = 0 := by
    rw [← E]; simp only [Matrix.mul_assoc, hQP', Matrix.zero_mul]
  rw [X7CS_gen] at E1 E2
  have hB : ∀ k, Q * V k * P = 0 := by
    have hsum : (∑ k, (Q * V k * P) * (Q * V k * P)ᴴ) = 0 := by
      rw [← E1]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Finset.mul_sum, Finset.sum_mul,
        Matrix.conjTranspose_mul, hH, hQH, Matrix.mul_assoc, hPQ, hQP', Matrix.mul_zero,
        sub_zero]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Matrix.mul_assoc P P, hP]
    have htr := congrArg Matrix.trace hsum
    rw [Matrix.trace_sum, Matrix.trace_zero] at htr
    have hnn : ∀ k ∈ Finset.univ, 0 ≤ ((Q * V k * P) * (Q * V k * P)ᴴ).trace :=
      fun k _ => (Matrix.posSemidef_self_mul_conjTranspose _).trace_nonneg
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp htr
    intro k
    exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (this k (Finset.mem_univ _))
  have hV : ∀ k, P * V k * P = V k * P := by
    intro k
    have := hB k
    rw [hQdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    exact this.symm
  refine ⟨?_, hV⟩
  have hK0 : Q * K * P = 0 := by
    have h0 : Q * ((∑ k, V k * P * (V k)ᴴ) - K * P - P * Kᴴ) * P = - (Q * K * P) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Finset.mul_sum, Finset.sum_mul]
      have : ∀ k, Q * (V k * P * (V k)ᴴ) * P = 0 := by
        intro k
        have e : Q * (V k * P * (V k)ᴴ) * P = (Q * V k * P) * ((V k)ᴴ * P) := by
          simp only [Matrix.mul_assoc]
        rw [e, hB, Matrix.zero_mul]
      simp only [this, Finset.sum_const_zero, zero_sub]
      simp only [Matrix.mul_assoc, hQP', hP, Matrix.zero_mul, sub_zero]
    rw [h0] at E2
    exact neg_eq_zero.mp E2
  rw [hQdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hK0
  exact hK0.symm

lemma X7CS_P_ne {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hS : S ≠ ⊥) :
    orthogonalProjector S ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hPv : QAlgorithms.act (orthogonalProjector S) v = v := by
    rw [X7CS_projAct]; exact Submodule.starProjection_eq_self_iff.mpr hv
  rw [h0] at hPv
  apply hv0
  rw [← hPv]
  ext i; simp [QAlgorithms.act]

open scoped ComplexOrder in
lemma X7CS_density {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : P * P = P) (hH : Pᴴ = P)
    (h0 : P ≠ 0) : P.trace ≠ 0 ∧ QAlgorithms.IsDensityMatrix ((P.trace)⁻¹ • P) := by
  have hPP : Pᴴ * P = P := by rw [hH, hP]
  have hpsd : P.PosSemidef := by rw [← hPP]; exact Matrix.posSemidef_conjTranspose_mul_self P
  have htr0 : P.trace ≠ 0 := by
    rw [← hPP]; intro h; exact h0 (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h)
  have hnn : 0 ≤ P.trace := hpsd.trace_nonneg
  have hre : P.trace = ((P.trace.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
    exact (Complex.nonneg_iff.mp hnn).2.symm
  refine ⟨htr0, ?_, ?_⟩
  · apply hpsd.smul
    rw [hre, ← Complex.ofReal_inv]
    have : 0 ≤ P.trace.re := (Complex.nonneg_iff.mp hnn).1
    exact Complex.zero_le_real.mpr (inv_nonneg.mpr this)
  · rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ htr0]

lemma X7CS_iii_i {n r : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : P * P = P) (hH : Pᴴ = P)
    (hK : P * K * P = K * P) (hV : ∀ k, P * V k * P = V k * P) (t : ℝ)
    (rho : Matrix (Fin n) (Fin n) ℂ) :
    P * semigroupEvolution (cpGenerator K V) t (P * rho * P) * P =
      semigroupEvolution (cpGenerator K V) t (P * rho * P) := by
  let C : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ P))
  have hCa : ∀ X, C X = P * (X * P) := fun X => rfl
  let A : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (t : ℂ) • LinearMap.toContinuousLinearMap (cpGenerator K V)
  have hCC : C * C = C := by
    ext1 X
    simp only [ContinuousLinearMap.mul_apply, hCa]
    simp only [← Matrix.mul_assoc, hP]
    simp only [Matrix.mul_assoc, hP]
  have hCA : C * A * C = A * C := by
    ext1 X
    simp only [ContinuousLinearMap.mul_apply, hCa, A, ContinuousLinearMap.smul_apply,
      LinearMap.coe_toContinuousLinearMap', map_smul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have := X7CS_alg K V P hP hH hK hV X
    simpa [Matrix.mul_assoc] using this
  have key := X7CS_exp_corner A C hCC hCA
  have := congrArg (fun T => T rho) key
  simp only [ContinuousLinearMap.mul_apply, hCa] at this
  unfold semigroupEvolution
  simpa [Matrix.mul_assoc, A] using this

lemma X7CS_i_ii {n r : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t ≥ (0 : ℝ), P * semigroupEvolution (cpGenerator K V) t Y * P =
      semigroupEvolution (cpGenerator K V) t Y) :
    P * cpGenerator K V Y * P = cpGenerator K V Y := by
  let G' : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap (cpGenerator K V)
  let C : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ P))
  have hCa : ∀ X, C X = P * (X * P) := fun X => rfl
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℂ) G' (Complex.ofRealCLM 0)
  have hz : NormedSpace.exp ((Complex.ofRealCLM 0) • G') = 1 := by
    rw [map_zero]; convert NormedSpace.exp_zero using 2
    · exact zero_smul ℂ G'
    · infer_instance
  rw [hz, one_mul] at h1
  have h1' : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • G') Y)
      (G' Y) (Complex.ofRealCLM 0) := by
    have := h1.clm_apply (hasDerivAt_const (Complex.ofRealCLM 0) Y)
    simpa using this
  have h2 := h1'.scomp (0 : ℝ) Complex.ofRealCLM.hasDerivAt
  have h3 : HasDerivAt (fun y : ℝ => NormedSpace.exp ((y : ℂ) • G') Y) (G' Y) 0 := by
    simpa [Function.comp_def] using h2
  have h4 := ((C.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) h3
  have e1 : HasDerivWithinAt (fun y : ℝ => NormedSpace.exp ((y : ℂ) • G') Y) (C (G' Y))
      (Set.Ici 0) 0 := by
    apply h4.hasDerivWithinAt.congr
    · intro y hy
      have := h y hy
      unfold semigroupEvolution at this
      simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars', hCa]
      rw [← Matrix.mul_assoc]; exact this.symm
    · have := h 0 le_rfl
      unfold semigroupEvolution at this
      simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars', hCa]
      rw [← Matrix.mul_assoc]; exact this.symm
  have := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ e1 h3.hasDerivWithinAt
  rw [hCa] at this
  simpa [G', Matrix.mul_assoc] using this

end QAlgorithms.Papers.Independent.Dependency50.P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Dependency50.P16 in
theorem solution {n r : ℕ} (hn : 2 ≤ n) (K : Matrix (Fin n) (Fin n) ℂ) (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hS : S ≠ ⊥) :
    List.TFAE [
      (∀ t ≥ 0, ∀ rho : Matrix (Fin n) (Fin n) ℂ, QAlgorithms.IsDensityMatrix rho →
        orthogonalProjector S * semigroupEvolution (cpGenerator K V) t (orthogonalProjector S * rho * orthogonalProjector S) * orthogonalProjector S =
          semigroupEvolution (cpGenerator K V) t (orthogonalProjector S * rho * orthogonalProjector S)),
      (∀ rho : Matrix (Fin n) (Fin n) ℂ, QAlgorithms.IsDensityMatrix rho →
        orthogonalProjector S * cpGenerator K V (orthogonalProjector S * rho * orthogonalProjector S) * orthogonalProjector S =
          cpGenerator K V (orthogonalProjector S * rho * orthogonalProjector S)),
      invariant (extendedAlgebra K V : Set (Matrix (Fin n) (Fin n) ℂ)) S] := by
  have hP := X7CS_proj_idem S
  have hH := X7CS_proj_herm S
  tfae_have 1 → 2 := by
    intro h rho hrho
    exact X7CS_i_ii K V _ _ (fun t ht => h t ht rho hrho)
  tfae_have 2 → 3 := by
    intro h
    obtain ⟨htr, hd⟩ := X7CS_density _ hP hH (X7CS_P_ne S hS)
    have e := h _ hd
    have hPPP : orthogonalProjector S * ((orthogonalProjector S).trace⁻¹ • orthogonalProjector S) *
        orthogonalProjector S = (orthogonalProjector S).trace⁻¹ • orthogonalProjector S := by
      rw [Matrix.mul_smul, Matrix.smul_mul, hP, hP]
    rw [hPPP, map_smul, Matrix.mul_smul, Matrix.smul_mul] at e
    have E := smul_right_injective _ (inv_ne_zero htr) e
    obtain ⟨hK, hV⟩ := X7CS_ii_iii K V _ hP hH E
    apply X7CS_adjoin_inv
    intro X hX
    rcases hX with rfl | ⟨k, rfl⟩
    · exact (X7CS_inv_iff S _).mpr hK
    · exact (X7CS_inv_iff S _).mpr (hV k)
  tfae_have 3 → 1 := by
    intro h t _ rho _
    have hK := (X7CS_inv_iff S K).mp (h K (Algebra.subset_adjoin (Set.mem_insert _ _)))
    have hV : ∀ k, _ := fun k => (X7CS_inv_iff S (V k)).mp
      (h (V k) (Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨k, rfl⟩)))
    exact X7CS_iii_i K V _ hP hH hK hV t rho
  tfae_finish

end
