-- Prove2me | solution 1 for PatakiRank.Mult.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T18:51:00.033142+00:00
-- url     : https://prove2.me/submissions/ed8ab566-b21f-429a-9256-f8e4b1fe9d71

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting

/-!
Theorem 3.3 of Pataki (Math. Oper. Res. 23(2), 1998, p. 347). Conjugating a feasible `(z, V, W)` of
(3.14) by `Q` gives `V' = QᵀVQ ⪰ 0`, `W' = QᵀWQ ⪰ 0` with `z I + V' - W' = diag λ`; reading the
diagonal gives `k z + tr V ≥ ∑_{i<k} λ_i`, with equality forcing zero diagonal entries, hence
(PSD) zero rows, so `V' = diag v*`, `W' = diag w*` and `λ_{k+1} ≤ z ≤ λ_k`. Conversely such points
are feasible with objective `∑_{i<k} λ_i`.
-/

set_option autoImplicit false

open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

theorem t33_frob_one {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) : frob 1 V = V.trace := by
  unfold frob
  simp

theorem t33_card {n k : ℕ} (hkn : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  have h := Fin.card_filter_val_lt (n := n) (m := k)
  rw [h]
  omega

theorem t33_lb {n k : ℕ} (hkn : k ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (lam : Fin n → ℝ) (hQ : Qᵀ * Q = 1) (hBQ : B = Q * diagonal lam * Qᵀ)
    (p : ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (hp : PatakiRank.Mult.sdpFeas B p) :
    (∑ i : Fin n with i.val < k, lam i) ≤ PatakiRank.Mult.sdpObj k p := by
  obtain ⟨z, V, W⟩ := p
  obtain ⟨hV, hW, hEq⟩ := hp
  simp only at hV hW hEq
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have hV' : (Qᵀ * V * Q).PosSemidef := by
    have := hV.conjTranspose_mul_mul_same Q
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have hW' : (Qᵀ * W * Q).PosSemidef := by
    have := hW.conjTranspose_mul_mul_same Q
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have h1 : Qᵀ * B * Q = diagonal lam := by
    conv_lhs => rw [hBQ]
    rw [show Qᵀ * (Q * diagonal lam * Qᵀ) * Q
        = (Qᵀ * Q) * diagonal lam * (Qᵀ * Q) by simp only [Matrix.mul_assoc]]
    rw [hQ, Matrix.one_mul, Matrix.mul_one]
  have h2 : Qᵀ * (z • (1 : Matrix (Fin n) (Fin n) ℝ) + V - W) * Q
      = z • (1 : Matrix (Fin n) (Fin n) ℝ) + Qᵀ * V * Q - Qᵀ * W * Q := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ]
  rw [hEq, h1] at h2
  have hdiag : ∀ i, lam i = z + (Qᵀ * V * Q) i i - (Qᵀ * W * Q) i i := by
    intro i
    have := congrFun (congrFun h2 i) i
    simpa [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq] using this
  have htr : V.trace = (Qᵀ * V * Q).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQ', Matrix.one_mul]
  unfold PatakiRank.Mult.sdpObj
  simp only
  rw [t33_frob_one, htr]
  set S := Finset.univ.filter (fun i : Fin n => i.val < k) with hS
  have hsum : ∑ i : Fin n with i.val < k, lam i = ∑ i ∈ S, lam i := rfl
  rw [hsum]
  calc ∑ i ∈ S, lam i ≤ ∑ i ∈ S, (z + (Qᵀ * V * Q) i i) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hdiag i]
        have := hW'.diag_nonneg (i := i)
        linarith
    _ = (k : ℝ) * z + ∑ i ∈ S, (Qᵀ * V * Q) i i := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hS, t33_card hkn]
    _ ≤ (k : ℝ) * z + (Qᵀ * V * Q).trace := by
        have : ∑ i ∈ S, (Qᵀ * V * Q) i i ≤ ∑ i, (Qᵀ * V * Q) i i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => hV'.diag_nonneg)
        unfold Matrix.trace
        simp only [Matrix.diag_apply]
        linarith

theorem t33_psd_row {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef) {i : Fin n}
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
theorem t33_attain_z {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) (B Q : Matrix (Fin n) (Fin n) ℝ)
    (lam : Fin n → ℝ)
    (hQ : Qᵀ * Q = 1) (hanti : Antitone lam)
    (hBQ : B = Q * diagonal lam * Qᵀ) (z : ℝ)
    (hz1 : lam ⟨k, hkn⟩ ≤ z) (hz2 : z ≤ lam ⟨k - 1, by omega⟩) :
    PatakiRank.Mult.sdpFeas B (z, Q * diagonal (PatakiRank.Mult.vStar k lam z) * Qᵀ,
        Q * diagonal (PatakiRank.Mult.wStar k lam z) * Qᵀ) ∧
      PatakiRank.Mult.sdpObj k (z, Q * diagonal (PatakiRank.Mult.vStar k lam z) * Qᵀ,
        Q * diagonal (PatakiRank.Mult.wStar k lam z) * Qᵀ) ≤
        (∑ i : Fin n with i.val < k, lam i) := by
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  set v : Fin n → ℝ := PatakiRank.Mult.vStar k lam z with hvdef
  set w : Fin n → ℝ := PatakiRank.Mult.wStar k lam z with hwdef
  have hv : ∀ i, 0 ≤ v i := by
    intro i
    simp only [hvdef, PatakiRank.Mult.vStar]
    split_ifs with h
    · have : lam ⟨k - 1, by omega⟩ ≤ lam i := hanti (by rw [Fin.le_def]; simp; omega)
      linarith
    · exact le_refl 0
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    simp only [hwdef, PatakiRank.Mult.wStar]
    split_ifs with h
    · exact le_refl 0
    · have : lam i ≤ lam ⟨k, hkn⟩ := hanti (by rw [Fin.le_def]; simp; omega)
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
    unfold PatakiRank.Mult.sdpObj
    simp only
    rw [t33_frob_one]
    have htr : (Q * diagonal v * Qᵀ).trace = ∑ i, v i := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQ, Matrix.one_mul, Matrix.trace_diagonal]
    rw [htr]
    have hsv : ∑ i, v i = ∑ i : Fin n with i.val < k, (lam i - z) := by
      rw [Finset.sum_filter]
      rfl
    rw [hsv, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, t33_card hkn.le]
    ring

/-- Characterisation: an optimal point of (3.14) lies on the segment. -/
theorem t33_char {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) (B Q : Matrix (Fin n) (Fin n) ℝ)
    (lam : Fin n → ℝ)
    (hQ : Qᵀ * Q = 1) (hBQ : B = Q * diagonal lam * Qᵀ)
    (z : ℝ) (V W : Matrix (Fin n) (Fin n) ℝ) (hfeas : PatakiRank.Mult.sdpFeas B (z, V, W))
    (hobj : PatakiRank.Mult.sdpObj k (z, V, W) ≤ (∑ i : Fin n with i.val < k, lam i)) :
    lam ⟨k, hkn⟩ ≤ z ∧ z ≤ lam ⟨k - 1, by omega⟩ ∧
      V = Q * diagonal (PatakiRank.Mult.vStar k lam z) * Qᵀ ∧
      W = Q * diagonal (PatakiRank.Mult.wStar k lam z) * Qᵀ := by
  obtain ⟨hV, hW, hEq⟩ := hfeas
  simp only at hV hW hEq
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have hV' : (Qᵀ * V * Q).PosSemidef := by
    have := hV.conjTranspose_mul_mul_same Q
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have hW' : (Qᵀ * W * Q).PosSemidef := by
    have := hW.conjTranspose_mul_mul_same Q
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have h1 : Qᵀ * B * Q = diagonal lam := by
    conv_lhs => rw [hBQ]
    rw [show Qᵀ * (Q * diagonal lam * Qᵀ) * Q
        = (Qᵀ * Q) * diagonal lam * (Qᵀ * Q) by simp only [Matrix.mul_assoc]]
    rw [hQ, Matrix.one_mul, Matrix.mul_one]
  have h2 : Qᵀ * (z • (1 : Matrix (Fin n) (Fin n) ℝ) + V - W) * Q
      = z • (1 : Matrix (Fin n) (Fin n) ℝ) + Qᵀ * V * Q - Qᵀ * W * Q := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ]
  rw [hEq, h1] at h2
  set V' := Qᵀ * V * Q with hV'def
  set W' := Qᵀ * W * Q with hW'def
  have hdiag : ∀ i, lam i = z + V' i i - W' i i := by
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
  unfold PatakiRank.Mult.sdpObj at hobj
  simp only at hobj
  rw [t33_frob_one, htr] at hobj
  set S := Finset.univ.filter (fun i : Fin n => i.val < k) with hS
  set Sc := Finset.univ.filter (fun i : Fin n => ¬ i.val < k) with hSc
  have hsum : ∑ i : Fin n with i.val < k, lam i = ∑ i ∈ S, lam i := rfl
  rw [hsum] at hobj
  have hfk : ∑ i ∈ S, lam i
      = (k : ℝ) * z + ∑ i ∈ S, V' i i - ∑ i ∈ S, W' i i := by
    rw [Finset.sum_congr rfl (fun i _ => hdiag i), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul, hS, t33_card hkn.le]
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
  have hb1 : lam ⟨k, hkn⟩ ≤ z := by
    have h := hdiag ⟨k, hkn⟩
    rw [hVz _ (by simp)] at h
    have := hW'.diag_nonneg (i := ⟨k, hkn⟩)
    linarith
  have hb2 : z ≤ lam ⟨k - 1, by omega⟩ := by
    have h := hdiag ⟨k - 1, by omega⟩
    rw [hWz _ (by simp; omega)] at h
    have := hV'.diag_nonneg (i := ⟨k - 1, by omega⟩)
    linarith
  have hVd : V' = diagonal (PatakiRank.Mult.vStar k lam z) := by
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
          exact (t33_psd_row hW' (hWz i hi) j).1
        · exact (t33_psd_row hV' (hVz j hj) i).2
      · exact (t33_psd_row hV' (hVz i hi) j).1
  have hWd : W' = diagonal (PatakiRank.Mult.wStar k lam z) := by
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
      · exact (t33_psd_row hW' (hWz i hi) j).1
      · by_cases hj : j.val < k
        · exact (t33_psd_row hW' (hWz j hj) i).2
        · rw [← hoff i j hij]
          exact (t33_psd_row hV' (hVz i hi) j).1
  have hback : ∀ X : Matrix (Fin n) (Fin n) ℝ, X = Q * (Qᵀ * X * Q) * Qᵀ := by
    intro X
    rw [show Q * (Qᵀ * X * Q) * Qᵀ = (Q * Qᵀ) * X * (Q * Qᵀ) by simp only [Matrix.mul_assoc],
      hQ', Matrix.one_mul, Matrix.mul_one]
  refine ⟨hb1, hb2, ?_, ?_⟩
  · rw [hback V, ← hV'def, hVd]
  · rw [hback W, ← hW'def, hWd]

open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral PatakiRank.Mult in
theorem solution {n k : ℕ} (B Q : Matrix (Fin n) (Fin n) ℝ) (lam : Fin n → ℝ)
    (hQ : Qᵀ * Q = 1) (hlam : Antitone lam) (hB : B = Q * diagonal lam * Qᵀ)
    (hk : 1 ≤ k) (hkn : k < n) :
    IsLeast (sdpObj k '' {p | sdpFeas B p}) (∑ i : Fin n with i.val < k, lam i) ∧
    ∀ p : ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ,
      IsOptimal (sdpFeas B) (sdpObj k) p ↔
        ((lam ⟨k, hkn⟩ ≤ p.1 ∧ p.1 ≤ lam ⟨k - 1, by omega⟩) ∧
          p.2.1 = Q * diagonal (vStar k lam p.1) * Qᵀ ∧
          p.2.2 = Q * diagonal (wStar k lam p.1) * Qᵀ) := by
  have hlb : ∀ q, sdpFeas B q → (∑ i : Fin n with i.val < k, lam i) ≤ sdpObj k q :=
    fun q hq => t33_lb hkn.le B Q lam hQ hB q hq
  have h0 := t33_attain_z hk hkn B Q lam hQ hlam hB (lam ⟨k, hkn⟩) le_rfl
    (hlam (by rw [Fin.le_def]; simp))
  refine ⟨⟨⟨_, h0.1, le_antisymm h0.2 (hlb _ h0.1)⟩, ?_⟩, fun p => ⟨?_, ?_⟩⟩
  · rintro y ⟨q, hq, rfl⟩
    exact hlb q hq
  · rintro ⟨hf, hopt⟩
    obtain ⟨z, V, W⟩ := p
    have hle := (hopt _ h0.1).trans h0.2
    obtain ⟨hb1, hb2, hV, hW⟩ := t33_char hk hkn B Q lam hQ hB z V W hf hle
    exact ⟨⟨hb1, hb2⟩, hV, hW⟩
  · rintro ⟨⟨hb1, hb2⟩, hV, hW⟩
    obtain ⟨z, V, W⟩ := p
    simp only at hb1 hb2 hV hW
    subst hV hW
    have h1 := t33_attain_z hk hkn B Q lam hQ hlam hB z hb1 hb2
    exact ⟨h1.1, fun q hq => h1.2.trans (hlb q hq)⟩
