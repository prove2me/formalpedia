-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P18.isotropic_projection_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Imine
-- created : 2026-10-20T18:10:31.375099+00:00
-- url     : https://prove2.me/submissions/77017406-65b1-41e4-ad9b-a7877a41c572

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18
noncomputable section

open scoped Matrix RealInnerProductSpace InnerProductSpace BigOperators

open QAlgorithms.Papers.Independent.Claimed50.P35 (physicalCommutationMatrix)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

open QAlgorithms.Papers.Independent.Next46.P18

private abbrev Om (s : ℕ) : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ :=
  physicalCommutationMatrix s 1

private lemma om_transpose (s : ℕ) : (Om s).transpose = - Om s := by
  ext i j
  obtain ⟨a, b⟩ := i
  obtain ⟨c, d⟩ := j
  fin_cases b <;> fin_cases d <;>
    simp [Om, physicalCommutationMatrix, eq_comm]
  all_goals
    by_cases h : a = c <;> simp [h]

private lemma om_mul_self (s : ℕ) : Om s * Om s = -1 := by
  ext i j
  obtain ⟨a, b⟩ := i
  obtain ⟨c, d⟩ := j
  fin_cases b <;> fin_cases d <;>
    simp [Om, physicalCommutationMatrix, Matrix.mul_apply, Fintype.sum_prod_type,
      eq_comm]
  all_goals
    by_cases h : a = c <;> simp [h, Matrix.one_apply]

private lemma ring_decomp {A : Type*} [Ring A] (P O Q R : A)
    (hQ : Q = -(O * P * O)) (hR : R = 1 - P - Q)
    (hP : P * P = P) (hO : O * O = -1) (hPOP : P * O * P = 0) :
    Q * Q = Q ∧ R * R = R ∧ P * Q = 0 ∧ P * R = 0 ∧ Q * R = 0 ∧
      P + Q + R = 1 := by
  have hQid : Q * Q = Q := by
    rw [hQ]
    have h1 : (-(O * P * O)) * (-(O * P * O)) = O * P * (O * O) * P * O := by
      noncomm_ring
    rw [h1, hO]
    have h2 : O * P * (-1 : A) * P * O = -(O * (P * P) * O) := by
      noncomm_ring
    rw [h2, hP]
  have hPQ : P * Q = 0 := by
    rw [hQ]
    have h1 : P * (-(O * P * O)) = -((P * O * P) * O) := by
      noncomm_ring
    rw [h1, hPOP]
    simp
  have hQP : Q * P = 0 := by
    rw [hQ]
    have h1 : (-(O * P * O)) * P = -(O * (P * O * P)) := by
      noncomm_ring
    rw [h1, hPOP]
    simp
  refine ⟨hQid, ?_, hPQ, ?_, ?_, ?_⟩
  · rw [hR]
    have h1 : (1 - P - Q) * (1 - P - Q) =
        1 - P - Q - P + P * P + P * Q - Q + Q * P + Q * Q := by
      noncomm_ring
    rw [h1, hP, hPQ, hQP, hQid]
    noncomm_ring
  · rw [hR]
    have h1 : P * (1 - P - Q) = P - P * P - P * Q := by
      noncomm_ring
    rw [h1, hP, hPQ]
    noncomm_ring
  · rw [hR]
    have h1 : Q * (1 - P - Q) = Q - Q * P - Q * Q := by
      noncomm_ring
    rw [h1, hQP, hQid]
    noncomm_ring
  · rw [hR]
    noncomm_ring

theorem solution {s t : ℕ} (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (hK : K.transpose * Om s * K = 0) :
    ∃ P Q R : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ,
      P.IsSymm ∧ Q.IsSymm ∧ R.IsSymm ∧
      P * P = P ∧ Q * Q = Q ∧ R * R = R ∧
      P * Q = 0 ∧ P * R = 0 ∧ Q * R = 0 ∧
      P + Q + R = 1 ∧
      Q = -(Om s) * P * (Om s) ∧
      K.transpose * P * K = K.transpose * K ∧
      K.transpose * Q * K = 0 ∧
      K.transpose * R * K = 0 := by
  let E := EuclideanSpace ℝ (QuadratureIndex s)
  let F := EuclideanSpace ℝ (QuadratureIndex t)
  let A : F →ₗ[ℝ] E := Matrix.toEuclideanLin K
  let V : Submodule ℝ E := LinearMap.range A
  let T : E →L[ℝ] E := V.starProjection
  let e : E ≃ₗ[ℝ] (QuadratureIndex s → ℝ) := WithLp.linearEquiv 2 ℝ (QuadratureIndex s → ℝ)
  let et : F ≃ₗ[ℝ] (QuadratureIndex t → ℝ) := WithLp.linearEquiv 2 ℝ (QuadratureIndex t → ℝ)
  let S : (QuadratureIndex s → ℝ) →ₗ[ℝ] (QuadratureIndex s → ℝ) :=
    e.toLinearMap ∘ₗ T.toLinearMap ∘ₗ e.symm.toLinearMap
  let P : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ := LinearMap.toMatrix' S
  have hP : Matrix.toLin' P = S := by
    simp [P]
  have hPsym : P.IsSymm := by
    rw [Matrix.IsSymm]
    ext i j
    have hbasis : ∀ (k : QuadratureIndex s) (v : E),
        (e v) k = ⟪e.symm (Pi.single k 1), v⟫_ℝ := by
      intro k v
      rw [PiLp.inner_apply]
      change v k = ∑ x, v.ofLp x * (Pi.single k 1 : QuadratureIndex s → ℝ) x
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ k) h
    have hPij : P i j = ⟪e.symm (Pi.single i 1), T (e.symm (Pi.single j 1))⟫_ℝ := by
      simp only [P, LinearMap.toMatrix'_apply]
      change (e (T (e.symm (Pi.single j 1)))) i = _
      rw [hbasis]
    have hPji : P j i = ⟪e.symm (Pi.single j 1), T (e.symm (Pi.single i 1))⟫_ℝ := by
      simp only [P, LinearMap.toMatrix'_apply]
      change (e (T (e.symm (Pi.single i 1)))) j = _
      rw [hbasis]
    have hadj : T.adjoint = T := (isSelfAdjoint_starProjection V).adjoint_eq
    change P j i = P i j
    calc
      P j i = ⟪e.symm (Pi.single j 1), T (e.symm (Pi.single i 1))⟫_ℝ := hPji
      _ = ⟪T (e.symm (Pi.single j 1)), e.symm (Pi.single i 1)⟫_ℝ := by
            rw [← ContinuousLinearMap.adjoint_inner_left, hadj]
      _ = ⟪e.symm (Pi.single i 1), T (e.symm (Pi.single j 1))⟫_ℝ := real_inner_comm _ _
      _ = P i j := hPij.symm
  have hPidem : P * P = P := by
    refine (Matrix.toLin'.injective ?_)
    rw [Matrix.toLin'_mul, hP]
    have hidem : T * T = T := Submodule.isIdempotentElem_starProjection V
    have hS : S ∘ₗ S = S := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply]
      change e (T (e.symm (e (T (e.symm x))))) = e (T (e.symm x))
      rw [LinearEquiv.symm_apply_apply]
      have h2 : T (T (e.symm x)) = T (e.symm x) := by
        simpa using congrArg (fun f : E →L[ℝ] E => f (e.symm x)) hidem
      rw [h2]
    simpa [Module.End.mul_eq_comp] using hS
  -- bridge matrix to Euclidean linear map
  have hbridgeK : ∀ y : QuadratureIndex t → ℝ, e (A (et.symm y)) = Matrix.toLin' K y := by
    intro y
    change (Matrix.toEuclideanLin K (WithLp.toLp 2 y)).ofLp = Matrix.toLin' K y
    rw [Matrix.ofLp_toLpLin]
  have hSK : S ∘ₗ Matrix.toLin' K = Matrix.toLin' K := by
    apply LinearMap.ext
    intro y
    change e (T (e.symm (Matrix.toLin' K y))) = Matrix.toLin' K y
    have hy : e.symm (Matrix.toLin' K y) = A (et.symm y) := by
      rw [← hbridgeK y, LinearEquiv.symm_apply_apply]
    rw [hy]
    rw [Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self A (et.symm y))]
    exact hbridgeK y
  have hPK : P * K = K := by
    refine (Matrix.toLin'.injective ?_)
    rw [Matrix.toLin'_mul, hP]
    exact hSK
  -- isotropy of the range
  have hiso : ∀ a b : QuadratureIndex t → ℝ,
      (K *ᵥ a) ⬝ᵥ (Om s *ᵥ (K *ᵥ b)) = 0 := by
    intro a b
    calc
      (K *ᵥ a) ⬝ᵥ (Om s *ᵥ (K *ᵥ b))
          = (K *ᵥ a) ᵥ* Om s ⬝ᵥ (K *ᵥ b) := by
            rw [Matrix.dotProduct_mulVec]
      _ = (a ᵥ* (Kᵀ * Om s)) ⬝ᵥ (K *ᵥ b) := by
            rw [Matrix.vecMul_mulVec]
      _ = a ⬝ᵥ ((Kᵀ * Om s) *ᵥ (K *ᵥ b)) := by
            exact (Matrix.dotProduct_mulVec a (Kᵀ * Om s) (K *ᵥ b)).symm
      _ = a ⬝ᵥ (((Kᵀ * Om s) * K) *ᵥ b) := by
            congr 1
            exact Matrix.mulVec_mulVec b (Kᵀ * Om s) K
      _ = a ⬝ᵥ ((Kᵀ * Om s * K) *ᵥ b) := by rfl
      _ = 0 := by rw [hK]; simp
  let OmE : E →ₗ[ℝ] E := Matrix.toEuclideanLin (Om s)
  have hbridgeOm : ∀ x : QuadratureIndex s → ℝ, e (OmE (e.symm x)) = Matrix.toLin' (Om s) x := by
    intro x
    change (Matrix.toEuclideanLin (Om s) (WithLp.toLp 2 x)).ofLp = Matrix.toLin' (Om s) x
    rw [Matrix.ofLp_toLpLin]
  have horth : ∀ x y : E, x ∈ V → y ∈ V → ⟪x, OmE y⟫_ℝ = 0 := by
    intro x y hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    change (Om s *ᵥ (K *ᵥ WithLp.ofLp b)) ⬝ᵥ (K *ᵥ WithLp.ofLp a) = 0
    rw [dotProduct_comm]
    exact hiso (WithLp.ofLp a) (WithLp.ofLp b)
  have hTOT : (T.toLinearMap ∘ₗ OmE) ∘ₗ T.toLinearMap = 0 := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    have hzV : T (OmE (T x)) ∈ V := Submodule.starProjection_apply_mem V _
    have hzOrth : T (OmE (T x)) ∈ Vᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      have huT : T u = u := Submodule.starProjection_eq_self_iff.mpr hu
      have hadj : T.adjoint = T := (isSelfAdjoint_starProjection V).adjoint_eq
      calc
        ⟪u, T (OmE (T x))⟫_ℝ = ⟪T u, OmE (T x)⟫_ℝ := by
          rw [← ContinuousLinearMap.adjoint_inner_left, hadj]
        _ = ⟪u, OmE (T x)⟫_ℝ := by rw [huT]
        _ = 0 := horth u (T x) hu (Submodule.starProjection_apply_mem V x)
    have hz : T (OmE (T x)) = 0 := by
      have hmem : T (OmE (T x)) ∈ V ⊓ Vᗮ := ⟨hzV, hzOrth⟩
      rw [Submodule.inf_orthogonal_eq_bot] at hmem
      simpa using hmem
    exact hz
  have hPOP : P * Om s * P = 0 := by
    refine (Matrix.toLin'.injective ?_)
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, hP]
    have hOmLin : Matrix.toLin' (Om s) = e.toLinearMap ∘ₗ OmE ∘ₗ e.symm.toLinearMap := by
      apply LinearMap.ext
      intro x
      exact (hbridgeOm x).symm
    rw [hOmLin]
    apply LinearMap.ext
    intro x
    simp only [S, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply]
    have h := congrArg (fun f : E →ₗ[ℝ] E => f (e.symm x)) hTOT
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
    simpa using congrArg e h
  let Q : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ := -(Om s * P * Om s)
  let R : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ := 1 - P - Q
  have hQsym : Q.IsSymm := by
    rw [Matrix.IsSymm]
    change (Matrix.transpose (-(Om s * P * Om s))) = -(Om s * P * Om s)
    rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_mul, hPsym, om_transpose]
    noncomm_ring
  have hRsym : R.IsSymm := by
    rw [Matrix.IsSymm]
    change (Matrix.transpose (1 - P - Q)) = 1 - P - Q
    rw [Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_one, hPsym, hQsym]
  have hring := ring_decomp P (Om s) Q R rfl rfl hPidem (om_mul_self s) hPOP
  have hKPK : K.transpose * P * K = K.transpose * K := by
    rw [Matrix.mul_assoc, hPK]
  have hKQK : K.transpose * Q * K = 0 := by
    change K.transpose * (-(Om s * P * Om s)) * K = 0
    rw [Matrix.mul_neg, Matrix.neg_mul]
    have hpos : K.transpose * (Om s * P * Om s) * K = 0 := by
      calc
        K.transpose * (Om s * P * Om s) * K
            = K.transpose * Om s * P * Om s * (P * K) := by
              rw [hPK]
              simp only [Matrix.mul_assoc]
        _ = K.transpose * Om s * (P * Om s * P) * K := by
              simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hPOP]; simp
    rw [hpos, neg_zero]
  have hKRK : K.transpose * R * K = 0 := by
    change K.transpose * (1 - P - Q) * K = 0
    have h1 : K.transpose * (1 - P - Q) * K =
        K.transpose * K - K.transpose * P * K - K.transpose * Q * K := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [h1, hKPK, hKQK]
    simp
  refine ⟨P, Q, R, hPsym, hQsym, hRsym, hPidem, hring.1, hring.2.1,
    hring.2.2.1, hring.2.2.2.1, hring.2.2.2.2.1, hring.2.2.2.2.2, ?_, hKPK, hKQK, hKRK⟩
  -- Q has the exact negated-left form required by the statement
  change -(Om s * P * Om s) = -(Om s) * P * (Om s)
  noncomm_ring

