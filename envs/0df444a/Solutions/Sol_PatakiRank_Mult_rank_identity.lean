-- Prove2me | solution 1 for PatakiRank.Mult.rank_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T18:58:03.909274+00:00
-- url     : https://prove2.me/submissions/00fca18b-9b14-49d7-9daf-a559c41e9aa2

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting

/-!
The rank identity of Pataki (Math. Oper. Res. 23(2), 1998, p. 348) when `λ_k = λ_{k+1}`.
With `B = Q diag(λ) Qᵀ`, an optimal `(z, V, W)` has `V = Q diag(v*(z)) Qᵀ`, `W = Q diag(w*(z)) Qᵀ`.
For `z = λ_k`, `rank V = #{i : λ_i > z}`, `rank W = #{i : λ_i < z}` and the multiplicity of `λ_k`
is `#{i : λ_i = z}` (a contiguous run since `λ` is sorted), so the three add up to `n`.
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

theorem pr43_rank_conj {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1)
    (v : Fin n → ℝ) :
    (Q * diagonal v * Qᵀ).rank = Fintype.card {i // v i ≠ 0} := by
  have hd : Qᵀ.det * Q.det = 1 := by rw [← det_mul, hQ, det_one]
  have hQd : Q.det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hd
    exact zero_ne_one hd
  have hQtd : Qᵀ.det ≠ 0 := by rw [det_transpose]; exact hQd
  rw [rank_mul_eq_left_of_det_ne_zero _ _ hQtd, rank_mul_eq_right_of_det_ne_zero _ _ hQd]
  exact rank_diagonal v

theorem pr43_card_ge {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (a c : ℕ) (hc : a + c ≤ n)
    (h : ∀ i : Fin n, a ≤ i.val → i.val < a + c → P i) : c ≤ Fintype.card {i // P i} := by
  have := Fintype.card_le_of_injective
    (fun j : Fin c => (⟨⟨a + j.val, by omega⟩, h _ (by simp) (by simp)⟩ : {i // P i}))
    (by
      intro j1 j2 hj
      simp only [Subtype.mk.injEq, Fin.mk.injEq] at hj
      exact Fin.ext (by omega))
  simpa using this

theorem pr43_card_le {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (a c : ℕ)
    (h : ∀ i : Fin n, P i → a ≤ i.val ∧ i.val < a + c) : Fintype.card {i // P i} ≤ c := by
  have := Fintype.card_le_of_injective
    (fun i : {i // P i} => (⟨i.1.val - a, by have := h i.1 i.2; omega⟩ : Fin c))
    (by
      intro i1 i2 hi
      have h1 := h i1.1 i1.2
      have h2 := h i2.1 i2.2
      simp only [Fin.mk.injEq] at hi
      exact Subtype.ext (Fin.ext (by omega)))
  simpa using this

theorem ri_down {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ i j : Fin n, i ≤ j → P j → P i) (i : Fin n) :
    P i ↔ i.val < Fintype.card {i // P i} := by
  constructor
  · intro h
    have := pr43_card_ge P 0 (i.val + 1) (by omega)
      (fun i' _ hi' => hP i' i (Fin.le_def.2 (by omega)) h)
    omega
  · intro h
    by_contra hc
    have := pr43_card_le P 0 i.val (fun i' hi' => ⟨Nat.zero_le _, by
      by_contra hc'
      exact hc (hP i i' (Fin.le_def.2 (by omega)) hi')⟩)
    omega

open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral PatakiRank.Mult in
theorem solution {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (hk : 1 ≤ k) (hkn : k < n)
    (heq : eig B ⟨k - 1, by omega⟩ = eig B ⟨k, hkn⟩)
    (p : ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (hp : p ∈ Omega k B)
    (hz : p.1 = (1 / 2 : ℝ) * (eig B ⟨k - 1, by omega⟩ + eig B ⟨k, hkn⟩)) :
    p.2.1.rank + p.2.2.rank + mult B ⟨k - 1, by omega⟩ = n := by
  obtain ⟨z, V, W⟩ := p
  simp only at hz ⊢
  obtain ⟨Q, hQ, hanti, hBQ⟩ := l431_eig_decomp B hB
  have hlohi : eig B ⟨k, hkn⟩ ≤ eig B ⟨k - 1, by omega⟩ := hanti (by rw [Fin.le_def]; simp)
  obtain ⟨hfeas, hmin⟩ := hp
  obtain ⟨hq, hqle⟩ := l431_attain_z hk hkn B Q hQ hanti hBQ _ hlohi le_rfl
  obtain ⟨-, -, hV, hW⟩ := l431_char hk hkn B Q hQ hBQ z V W hfeas ((hmin _ hq).trans hqle)
  have hmono : ∀ i j : Fin n, i ≤ j → eig B j ≤ eig B i := fun i j h => hanti h
  set L := eig B ⟨k - 1, by omega⟩ with hL
  have hzL : z = L := by rw [hz, ← heq]; ring
  set a := Fintype.card {i : Fin n // L < eig B i} with ha
  set a' := Fintype.card {i : Fin n // L ≤ eig B i} with ha'
  have hD : ∀ i : Fin n, L < eig B i ↔ i.val < a :=
    ri_down _ (fun i j hij h => lt_of_lt_of_le h (hmono i j hij))
  have hD' : ∀ i : Fin n, L ≤ eig B i ↔ i.val < a' :=
    ri_down _ (fun i j hij h => le_trans h (hmono i j hij))
  have hka : ¬ (k - 1 < a) := fun h => lt_irrefl L ((hD ⟨k - 1, by omega⟩).2 h)
  have hk' : k < a' := (hD' ⟨k, hkn⟩).1 (le_of_eq heq)
  have ha'n : a' ≤ n := by
    have := Fintype.card_subtype_le (fun i : Fin n => L ≤ eig B i)
    simpa using this
  have hrV : V.rank = a := by
    rw [hV, pr43_rank_conj Q hQ]
    apply le_antisymm
    · apply pr43_card_le _ 0 a
      intro i hi
      simp only [vStar] at hi
      split_ifs at hi with hik
      · have h1 : L ≤ eig B i := hmono _ _ (Fin.le_def.2 (by simp; omega))
        rw [hzL] at hi
        have h2 := (hD i).1 (lt_of_le_of_ne h1 (fun h => hi (by rw [← h]; ring)))
        exact ⟨Nat.zero_le _, by omega⟩
      · exact absurd rfl hi
    · apply pr43_card_ge _ 0 a (by omega)
      intro i _ hi
      have h1 := (hD i).2 (by omega)
      have hik : i.val < k := by omega
      simp only [vStar, if_pos hik, hzL]
      exact sub_ne_zero.2 (ne_of_gt h1)
  have hrW : W.rank = n - a' := by
    rw [hW, pr43_rank_conj Q hQ]
    apply le_antisymm
    · apply pr43_card_le _ a' (n - a')
      intro i hi
      simp only [wStar] at hi
      split_ifs at hi with hik
      · exact absurd rfl hi
      · refine ⟨?_, by omega⟩
        have h1 : eig B i ≤ L := by
          rw [heq]; exact hmono _ _ (Fin.le_def.2 (by simp; omega))
        rw [hzL] at hi
        have h2 : eig B i < L := lt_of_le_of_ne h1 (fun h => hi (by rw [h]; ring))
        by_contra hc
        exact absurd ((hD' i).2 (by omega)) (not_le.2 h2)
    · apply pr43_card_ge _ a' (n - a') (by omega)
      intro i hi _
      have h1 : ¬ L ≤ eig B i := fun h => by have := (hD' i).1 h; omega
      have hik : ¬ i.val < k := by omega
      simp only [wStar, if_neg hik, hzL]
      exact sub_ne_zero.2 (ne_of_gt (not_le.1 h1))
  have hbdd : BddAbove {p : ℕ | 1 ≤ p ∧ ∃ j : ℕ, j ≤ ((⟨k - 1, by omega⟩ : Fin n) : ℕ) ∧
      ((⟨k - 1, by omega⟩ : Fin n) : ℕ) ≤ j + p - 1 ∧ j + p ≤ n ∧
      ∀ l : ℕ, ∀ hl : l < n, j ≤ l → l < j + p → eig B ⟨l, hl⟩ = eig B ⟨k - 1, by omega⟩} := by
    refine ⟨n, fun p hp => ?_⟩
    obtain ⟨_, j, _, _, h, _⟩ := hp
    omega
  have hmult : mult B ⟨k - 1, by omega⟩ = a' - a := by
    unfold mult
    apply le_antisymm
    · apply csSup_le ⟨a' - a, ?_⟩
      · rintro p ⟨hp1, j, hj1, hj2, hj3, hall⟩
        have hjL : eig B ⟨j, by omega⟩ = L := hall j (by omega) le_rfl (by omega)
        have hjpL : eig B ⟨j + p - 1, by omega⟩ = L := hall (j + p - 1) (by omega) (by omega) (by omega)
        have h1 : ¬ j < a := fun h => by
          have := (hD ⟨j, by omega⟩).2 h
          rw [hjL] at this
          exact lt_irrefl L this
        have h2 : j + p - 1 < a' := (hD' ⟨j + p - 1, by omega⟩).1 (le_of_eq hjpL.symm)
        omega
      · refine ⟨by omega, a, by simp; omega, by simp; omega, by omega, ?_⟩
        intro l hl h1 h2
        apply le_antisymm
        · by_contra hc
          have := (hD ⟨l, hl⟩).1 (lt_of_not_ge hc)
          simp at this
          omega
        · exact (hD' ⟨l, hl⟩).2 (by simp; omega)
    · apply le_csSup hbdd
      refine ⟨by omega, a, by simp; omega, by simp; omega, by omega, ?_⟩
      intro l hl h1 h2
      apply le_antisymm
      · by_contra hc
        have := (hD ⟨l, hl⟩).1 (lt_of_not_ge hc)
        simp at this
        omega
      · exact (hD' ⟨l, hl⟩).2 (by simp; omega)
  rw [hrV, hrW, hmult]
  omega
