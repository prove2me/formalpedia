-- Prove2me | solution 1 for PatakiRank.Mult.eq_4_31
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T18:45:52.169063+00:00
-- url     : https://prove2.me/submissions/1cb92f8b-f6dc-468b-86da-dc061471b084

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting

/-!
(4.31) of Pataki (Math. Oper. Res. 23(2), 1998, p. 349). With `A(x*) = Q diag(λ) Qᵀ`, every optimal
`(z, V, W)` of (3.14) has `z ∈ [λ_{k+1}, λ_k]`, `V = Q diag(v*(z)) Qᵀ`, `W = Q diag(w*(z)) Qᵀ`
(conjugate by `Q`, read the diagonal, and use that a PSD matrix with a zero diagonal entry has a
zero row), and every such point is optimal. So `F*` is the affine image of the segment
`[λ_{k+1}, λ_k]` under an injective affine map: a segment (dim 1) or a point (dim 0).
-/

set_option autoImplicit false

open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

theorem l431_aff_symm {n m : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA0 : A0.IsSymm) (hA : ∀ i, (A i).IsSymm)
    (x : Fin m → ℝ) : (PatakiRank.Mult.Aff A0 A x).IsSymm := by
  unfold PatakiRank.Mult.Aff Matrix.IsSymm
  rw [transpose_add, transpose_sum]
  simp only [transpose_smul, (hA _).eq, hA0.eq]

theorem l431_eig_decomp {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ, Qᵀ * Q = 1 ∧ Antitone (fun i => eig B i) ∧
      B = Q * diagonal (fun i => eig B i) * Qᵀ := by
  have hH : B.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hB
  have heig : ∀ i, eig B i = hH.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i) := by
    intro i
    unfold eig
    rw [dif_pos hH]
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin n ≃ Fin n, ∀ i, hH.eigenvalues i = eig B (τ i) := by
    refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)).symm.trans
      (finCongr (Fintype.card_fin n)), fun i => ?_⟩
    rw [heig]
    simp [Matrix.IsHermitian.eigenvalues]
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    with hUdef
  have hU : Uᵀ * U = 1 := by
    have h := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h
  have hS : B = U * diagonal (fun i => eig B (τ i)) * Uᵀ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hd : (RCLike.ofReal ∘ hH.eigenvalues : Fin n → ℝ) = fun i => eig B (τ i) := by
      funext i
      simp [hτ]
    rw [hd, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
    exact h
  set Q : Matrix (Fin n) (Fin n) ℝ := U.submatrix id τ.symm with hQdef
  refine ⟨Q, ?_, ?_, hS.trans ?_⟩
  · ext i j
    have h := congrFun (congrFun hU (τ.symm i)) (τ.symm j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hQdef, Matrix.submatrix_apply, id] at h ⊢
    rw [h, Matrix.one_apply, Matrix.one_apply]
    simp
  · intro i j hij
    show eig B j ≤ eig B i
    rw [heig, heig]
    apply hH.eigenvalues₀_antitone
    rw [Fin.le_def] at hij ⊢
    simpa using hij
  · ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hQdef, Matrix.submatrix_apply, id,
      Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    exact Fintype.sum_equiv τ _ _ (fun x => by simp)

theorem l431_frob_one {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) : frob 1 V = V.trace := by
  unfold frob
  simp

theorem l431_card {n k : ℕ} (hkn : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  have h := Fin.card_filter_val_lt (n := n) (m := k)
  rw [h]
  omega

/-- Lower bound: every feasible point of (3.14) has objective at least `f_k(B)`. -/
theorem l431_lb {n k : ℕ} (hkn : k ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (p : ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (hp : PatakiRank.Mult.sdpFeas B p) :
    PatakiRank.Mult.fk k B ≤ PatakiRank.Mult.sdpObj k p := by
  obtain ⟨z, V, W⟩ := p
  obtain ⟨hV, hW, hEq⟩ := hp
  simp only at hV hW hEq
  obtain ⟨Q, hQ, -, hBQ⟩ := l431_eig_decomp B hB
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have hV' : (Qᵀ * V * Q).PosSemidef := by
    have := hV.conjTranspose_mul_mul_same Q
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have hW' : (Qᵀ * W * Q).PosSemidef := by
    have := hW.conjTranspose_mul_mul_same Q
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have h1 : Qᵀ * B * Q = diagonal (fun i => eig B i) := by
    conv_lhs => rw [hBQ]
    rw [show Qᵀ * (Q * diagonal (fun i => eig B i) * Qᵀ) * Q
        = (Qᵀ * Q) * diagonal (fun i => eig B i) * (Qᵀ * Q) by simp only [Matrix.mul_assoc]]
    rw [hQ, Matrix.one_mul, Matrix.mul_one]
  have h2 : Qᵀ * (z • (1 : Matrix (Fin n) (Fin n) ℝ) + V - W) * Q
      = z • (1 : Matrix (Fin n) (Fin n) ℝ) + Qᵀ * V * Q - Qᵀ * W * Q := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ]
  rw [hEq, h1] at h2
  have hdiag : ∀ i, eig B i = z + (Qᵀ * V * Q) i i - (Qᵀ * W * Q) i i := by
    intro i
    have := congrFun (congrFun h2 i) i
    simpa [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq] using this
  have htr : V.trace = (Qᵀ * V * Q).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQ', Matrix.one_mul]
  unfold PatakiRank.Mult.fk PatakiRank.Mult.sdpObj
  simp only
  rw [l431_frob_one, htr]
  set S := Finset.univ.filter (fun i : Fin n => i.val < k) with hS
  have hsum : ∑ i : Fin n with i.val < k, eig B i = ∑ i ∈ S, eig B i := rfl
  rw [hsum]
  calc ∑ i ∈ S, eig B i ≤ ∑ i ∈ S, (z + (Qᵀ * V * Q) i i) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hdiag i]
        have := hW'.diag_nonneg (i := i)
        linarith
    _ = (k : ℝ) * z + ∑ i ∈ S, (Qᵀ * V * Q) i i := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hS, l431_card hkn]
    _ ≤ (k : ℝ) * z + (Qᵀ * V * Q).trace := by
        have : ∑ i ∈ S, (Qᵀ * V * Q) i i ≤ ∑ i, (Qᵀ * V * Q) i i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => hV'.diag_nonneg)
        unfold Matrix.trace
        simp only [Matrix.diag_apply]
        linarith

theorem l431_psd_row {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef) {i : Fin n}
    (hii : M i i = 0) (j : Fin n) : M i j = 0 ∧ M j i = 0 := by
  have h0 : star (Pi.single i (1 : ℝ)) ⬝ᵥ M *ᵥ Pi.single i 1 = 0 := by
    simp [dotProduct, mulVec, Pi.single_apply, hii]
  have h := (hM.dotProduct_mulVec_zero_iff (Pi.single i (1 : ℝ))).mp h0
  have hc : M j i = 0 := by
    have := congrFun h j
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  have hs : M i j = M j i := by
    have := hM.isHermitian.apply i j
    simpa using this.symm
  exact ⟨hs ▸ hc, hc⟩

/-- Every `z ∈ [λ_{k+1}, λ_k]` gives a feasible point of (3.14) with objective at most `f_k(B)`. -/
theorem l431_attain_z {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) (B Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) (hanti : Antitone (fun i => eig B i))
    (hBQ : B = Q * diagonal (fun i => eig B i) * Qᵀ) (z : ℝ)
    (hz1 : eig B ⟨k, hkn⟩ ≤ z) (hz2 : z ≤ eig B ⟨k - 1, by omega⟩) :
    PatakiRank.Mult.sdpFeas B (z, Q * diagonal (PatakiRank.Mult.vStar k (fun i => eig B i) z) * Qᵀ,
        Q * diagonal (PatakiRank.Mult.wStar k (fun i => eig B i) z) * Qᵀ) ∧
      PatakiRank.Mult.sdpObj k (z, Q * diagonal (PatakiRank.Mult.vStar k (fun i => eig B i) z) * Qᵀ,
        Q * diagonal (PatakiRank.Mult.wStar k (fun i => eig B i) z) * Qᵀ) ≤
        PatakiRank.Mult.fk k B := by
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  set lam : Fin n → ℝ := fun i => eig B i with hlamdef
  set v : Fin n → ℝ := PatakiRank.Mult.vStar k lam z with hvdef
  set w : Fin n → ℝ := PatakiRank.Mult.wStar k lam z with hwdef
  have hv : ∀ i, 0 ≤ v i := by
    intro i
    simp only [hvdef, PatakiRank.Mult.vStar]
    split_ifs with h
    · have : lam ⟨k - 1, by omega⟩ ≤ lam i := hanti (by rw [Fin.le_def]; simp; omega)
      simp only [hlamdef] at this ⊢
      linarith
    · exact le_refl 0
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    simp only [hwdef, PatakiRank.Mult.wStar]
    split_ifs with h
    · exact le_refl 0
    · have : lam i ≤ lam ⟨k, hkn⟩ := hanti (by rw [Fin.le_def]; simp; omega)
      simp only [hlamdef] at this ⊢
      linarith
  have hlam : lam = fun i => z + v i - w i := by
    funext i
    simp only [hvdef, hwdef, PatakiRank.Mult.vStar, PatakiRank.Mult.wStar]
    split_ifs <;> ring
  have hdg : diagonal (fun i => z + v i - w i)
      = z • (1 : Matrix (Fin n) (Fin n) ℝ) + diagonal v - diagonal w := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hpsd : ∀ u : Fin n → ℝ, (∀ i, 0 ≤ u i) → (Q * diagonal u * Qᵀ).PosSemidef := by
    intro u hu
    have h0 : (diagonal u).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr hu
    have := h0.mul_mul_conjTranspose_same Q
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  refine ⟨⟨hpsd v hv, hpsd w hw, ?_⟩, ?_⟩
  · show z • (1 : Matrix (Fin n) (Fin n) ℝ) + Q * diagonal v * Qᵀ - Q * diagonal w * Qᵀ = B
    symm
    calc B = Q * diagonal lam * Qᵀ := hBQ
      _ = Q * (z • (1 : Matrix (Fin n) (Fin n) ℝ) + diagonal v - diagonal w) * Qᵀ := by
          rw [← hdg, ← hlam]
      _ = z • (1 : Matrix (Fin n) (Fin n) ℝ) + Q * diagonal v * Qᵀ - Q * diagonal w * Qᵀ := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ']
  · apply le_of_eq
    unfold PatakiRank.Mult.sdpObj PatakiRank.Mult.fk
    simp only
    rw [l431_frob_one]
    have htr : (Q * diagonal v * Qᵀ).trace = ∑ i, v i := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQ, Matrix.one_mul, Matrix.trace_diagonal]
    rw [htr]
    have hsv : ∑ i, v i = ∑ i : Fin n with i.val < k, (lam i - z) := by
      rw [Finset.sum_filter]
      rfl
    rw [hsv, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, l431_card hkn.le]
    ring

/-- Characterisation: an optimal point of (3.14) lies on the segment. -/
theorem l431_char {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) (B Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) (hBQ : B = Q * diagonal (fun i => eig B i) * Qᵀ)
    (z : ℝ) (V W : Matrix (Fin n) (Fin n) ℝ) (hfeas : PatakiRank.Mult.sdpFeas B (z, V, W))
    (hobj : PatakiRank.Mult.sdpObj k (z, V, W) ≤ PatakiRank.Mult.fk k B) :
    eig B ⟨k, hkn⟩ ≤ z ∧ z ≤ eig B ⟨k - 1, by omega⟩ ∧
      V = Q * diagonal (PatakiRank.Mult.vStar k (fun i => eig B i) z) * Qᵀ ∧
      W = Q * diagonal (PatakiRank.Mult.wStar k (fun i => eig B i) z) * Qᵀ := by
  obtain ⟨hV, hW, hEq⟩ := hfeas
  simp only at hV hW hEq
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have hV' : (Qᵀ * V * Q).PosSemidef := by
    have := hV.conjTranspose_mul_mul_same Q
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have hW' : (Qᵀ * W * Q).PosSemidef := by
    have := hW.conjTranspose_mul_mul_same Q
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have h1 : Qᵀ * B * Q = diagonal (fun i => eig B i) := by
    conv_lhs => rw [hBQ]
    rw [show Qᵀ * (Q * diagonal (fun i => eig B i) * Qᵀ) * Q
        = (Qᵀ * Q) * diagonal (fun i => eig B i) * (Qᵀ * Q) by simp only [Matrix.mul_assoc]]
    rw [hQ, Matrix.one_mul, Matrix.mul_one]
  have h2 : Qᵀ * (z • (1 : Matrix (Fin n) (Fin n) ℝ) + V - W) * Q
      = z • (1 : Matrix (Fin n) (Fin n) ℝ) + Qᵀ * V * Q - Qᵀ * W * Q := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ]
  rw [hEq, h1] at h2
  set V' := Qᵀ * V * Q with hV'def
  set W' := Qᵀ * W * Q with hW'def
  have hdiag : ∀ i, eig B i = z + V' i i - W' i i := by
    intro i
    have := congrFun (congrFun h2 i) i
    simpa [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq] using this
  have hoff : ∀ i j, i ≠ j → V' i j = W' i j := by
    intro i j hij
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
      Matrix.diagonal_apply_ne _ hij, smul_eq_mul, mul_zero, zero_add] at this
    linarith
  have htr : V.trace = V'.trace := by
    rw [hV'def, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQ', Matrix.one_mul]
  unfold PatakiRank.Mult.fk PatakiRank.Mult.sdpObj at hobj
  simp only at hobj
  rw [l431_frob_one, htr] at hobj
  set S := Finset.univ.filter (fun i : Fin n => i.val < k) with hS
  set Sc := Finset.univ.filter (fun i : Fin n => ¬ i.val < k) with hSc
  have hsum : ∑ i : Fin n with i.val < k, eig B i = ∑ i ∈ S, eig B i := rfl
  rw [hsum] at hobj
  have hfk : ∑ i ∈ S, eig B i
      = (k : ℝ) * z + ∑ i ∈ S, V' i i - ∑ i ∈ S, W' i i := by
    rw [Finset.sum_congr rfl (fun i _ => hdiag i), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul, hS, l431_card hkn.le]
  have htrsplit : V'.trace = ∑ i ∈ S, V' i i + ∑ i ∈ Sc, V' i i := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply]
    rw [hS, hSc, Finset.sum_filter_add_sum_filter_not]
  rw [hfk, htrsplit] at hobj
  have hVnn : 0 ≤ ∑ i ∈ Sc, V' i i := Finset.sum_nonneg (fun i _ => hV'.diag_nonneg)
  have hWnn : 0 ≤ ∑ i ∈ S, W' i i := Finset.sum_nonneg (fun i _ => hW'.diag_nonneg)
  have hV0 : ∑ i ∈ Sc, V' i i = 0 := by linarith
  have hW0 : ∑ i ∈ S, W' i i = 0 := by linarith
  have hVz : ∀ i : Fin n, ¬ i.val < k → V' i i = 0 := by
    intro i hi
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hV'.diag_nonneg)).mp hV0 i
      (by simp [hSc]; omega)
  have hWz : ∀ i : Fin n, i.val < k → W' i i = 0 := by
    intro i hi
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hW'.diag_nonneg)).mp hW0 i
      (by simp [hS, hi])
  have hb1 : eig B ⟨k, hkn⟩ ≤ z := by
    have h := hdiag ⟨k, hkn⟩
    rw [hVz _ (by simp)] at h
    have := hW'.diag_nonneg (i := ⟨k, hkn⟩)
    linarith
  have hb2 : z ≤ eig B ⟨k - 1, by omega⟩ := by
    have h := hdiag ⟨k - 1, by omega⟩
    rw [hWz _ (by simp; omega)] at h
    have := hV'.diag_nonneg (i := ⟨k - 1, by omega⟩)
    linarith
  have hVd : V' = diagonal (PatakiRank.Mult.vStar k (fun i => eig B i) z) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      unfold PatakiRank.Mult.vStar
      split_ifs with h
      · have := hdiag i
        rw [hWz i h] at this
        linarith
      · exact hVz i h
    · rw [Matrix.diagonal_apply_ne _ hij]
      by_cases hi : i.val < k
      · by_cases hj : j.val < k
        · rw [hoff i j hij]
          exact (l431_psd_row hW' (hWz i hi) j).1
        · exact (l431_psd_row hV' (hVz j hj) i).2
      · exact (l431_psd_row hV' (hVz i hi) j).1
  have hWd : W' = diagonal (PatakiRank.Mult.wStar k (fun i => eig B i) z) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      unfold PatakiRank.Mult.wStar
      split_ifs with h
      · exact hWz i h
      · have := hdiag i
        rw [hVz i h] at this
        linarith
    · rw [Matrix.diagonal_apply_ne _ hij]
      by_cases hi : i.val < k
      · exact (l431_psd_row hW' (hWz i hi) j).1
      · by_cases hj : j.val < k
        · exact (l431_psd_row hW' (hWz j hj) i).2
        · rw [← hoff i j hij]
          exact (l431_psd_row hV' (hVz i hi) j).1
  have hback : ∀ X : Matrix (Fin n) (Fin n) ℝ, X = Q * (Qᵀ * X * Q) * Qᵀ := by
    intro X
    rw [show Q * (Qᵀ * X * Q) * Qᵀ = (Q * Qᵀ) * X * (Q * Qᵀ) by simp only [Matrix.mul_assoc],
      hQ', Matrix.one_mul, Matrix.mul_one]
  refine ⟨hb1, hb2, ?_, ?_⟩
  · rw [hback V, ← hV'def, hVd]
  · rw [hback W, ← hW'def, hWd]

theorem l431_diag_aff {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (u e : Fin n → ℝ) (z : ℝ) :
    Q * diagonal (u + z • e) * Qᵀ = Q * diagonal u * Qᵀ + z • (Q * diagonal e * Qᵀ) := by
  have h : diagonal (u + z • e) = diagonal u + z • diagonal e := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- The dimension of a subset of a line segment that contains both endpoints. -/
theorem l431_convDim_line {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (S : Set E) (c d : E) (hd : d ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hsub : ∀ x ∈ S, ∃ z, a ≤ z ∧ z ≤ b ∧ x = c + z • d)
    (ha : c + a • d ∈ S) (hb : c + b • d ∈ S) :
    PatakiRank.Mult.convDim S = if a < b then 1 else 0 := by
  unfold PatakiRank.Mult.convDim
  set T := {p : ℕ | ∃ v : Fin p → E, (∀ i, v i ∈ S) ∧ AffineIndependent ℝ v} with hT
  let f : ℝ →ᵃ[ℝ] E := AffineMap.lineMap c (c + d)
  have hf : ∀ z, f z = c + z • d := by
    intro z
    simp only [f, AffineMap.lineMap_apply_module', add_sub_cancel_left]
    abel
  have hub : ∀ p ∈ T, p ≤ if a < b then 2 else 1 := by
    rintro p ⟨v, hvS, hv⟩
    choose t ht1 ht2 htv using fun i => hsub (v i) (hvS i)
    have hvt : v = f ∘ t := funext fun i => by simp [hf, htv i]
    have ht : AffineIndependent ℝ t := AffineIndependent.of_comp f (hvt ▸ hv)
    split_ifs with hlt
    · have h0 := ht.card_le_finrank_succ
      have h1 := Submodule.finrank_le (vectorSpan ℝ (Set.range t))
      rw [Module.finrank_self] at h1
      simp only [Fintype.card_fin] at h0
      omega
    · have hab' : a = b := le_antisymm hab (not_lt.mp hlt)
      have hconst : ∀ i, t i = a := fun i => le_antisymm (hab' ▸ ht2 i) (ht1 i)
      by_contra hp
      push Not at hp
      have := ht.injective (a₁ := ⟨0, by omega⟩) (a₂ := ⟨1, by omega⟩) (by rw [hconst, hconst])
      simp at this
  have hmem : (if a < b then 2 else 1) ∈ T := by
    split_ifs with hlt
    · refine ⟨![c + a • d, c + b • d], ?_, ?_⟩
      · intro i
        fin_cases i
        · simpa using ha
        · simpa using hb
      · apply affineIndependent_of_ne
        intro h
        have h' : a • d = b • d := add_left_cancel h
        have := smul_left_injective ℝ hd h'
        exact hlt.ne this
    · refine ⟨![c + a • d], ?_, affineIndependent_of_subsingleton _ _⟩
      intro i
      fin_cases i
      simpa using ha
  have hs : sSup T = if a < b then 2 else 1 :=
    le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨_, hub⟩ hmem)
  rw [hs]
  split_ifs <;> norm_num

open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral PatakiRank.Mult in
theorem solution {n m k : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA0 : A0.IsSymm) (hA : ∀ i, (A i).IsSymm)
    (hind : LinearIndependent ℝ (Fin.cons A0 A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ))
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkn : k < n)
    (xs : Fin m → ℝ) :
    convDim (Fstar k A0 A xs) =
      if eig (Aff A0 A xs) ⟨k, hkn⟩ < eig (Aff A0 A xs) ⟨k - 1, by omega⟩ then 1 else 0 := by
  have hB : (Aff A0 A xs).IsSymm := l431_aff_symm A0 A hA0 hA xs
  set B := Aff A0 A xs with hBdef
  obtain ⟨Q, hQ, hanti, hBQ⟩ := l431_eig_decomp B hB
  have hlohi : eig B ⟨k, hkn⟩ ≤ eig B ⟨k - 1, by omega⟩ :=
    hanti (by rw [Fin.le_def]; simp)
  set ev : Fin n → ℝ := fun i => if i.val < k then -1 else 0 with hevdef
  set ew : Fin n → ℝ := fun i => if i.val < k then 0 else 1 with hewdef
  set c : (Fin m → ℝ) × ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ :=
    (xs, 0, Q * diagonal (vStar k (fun i => eig B i) 0) * Qᵀ,
      Q * diagonal (wStar k (fun i => eig B i) 0) * Qᵀ) with hcdef
  set d : (Fin m → ℝ) × ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ :=
    (0, 1, Q * diagonal ev * Qᵀ, Q * diagonal ew * Qᵀ) with hddef
  have hcd : ∀ z : ℝ, c + z • d = (xs, z, Q * diagonal (vStar k (fun i => eig B i) z) * Qᵀ,
      Q * diagonal (wStar k (fun i => eig B i) z) * Qᵀ) := by
    intro z
    have hv : vStar k (fun i => eig B i) z = vStar k (fun i => eig B i) 0 + z • ev := by
      funext i
      simp only [vStar, hevdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> ring
    have hw : wStar k (fun i => eig B i) z = wStar k (fun i => eig B i) 0 + z • ew := by
      funext i
      simp only [wStar, hewdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> ring
    rw [hv, hw, l431_diag_aff, l431_diag_aff]
    simp only [hcdef, hddef, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, smul_eq_mul,
      mul_one, zero_add]
  have hd : d ≠ 0 := by
    intro h
    have := congrArg (fun p => p.2.1) h
    simp [hddef] at this
  have hopt : ∀ z, eig B ⟨k, hkn⟩ ≤ z → z ≤ eig B ⟨k - 1, by omega⟩ → c + z • d ∈ Fstar k A0 A xs := by
    intro z hz1 hz2
    rw [hcd]
    obtain ⟨hf, hle⟩ := l431_attain_z hk hkn B Q hQ hanti hBQ z hz1 hz2
    exact ⟨rfl, hf, fun q hq => hle.trans (l431_lb hkn.le B hB q hq)⟩
  apply l431_convDim_line _ c d hd _ _ hlohi
  · rintro ⟨x, z, V, W⟩ ⟨hx, hfeas, hmin⟩
    simp only at hx
    obtain ⟨hq, hqle⟩ := l431_attain_z hk hkn B Q hQ hanti hBQ _ hlohi le_rfl
    obtain ⟨h1, h2, hV, hW⟩ := l431_char hk hkn B Q hQ hBQ z V W hfeas ((hmin _ hq).trans hqle)
    refine ⟨z, h1, h2, ?_⟩
    rw [hcd, hx, hV, hW]
  · exact hopt _ le_rfl hlohi
  · exact hopt _ hlohi le_rfl
