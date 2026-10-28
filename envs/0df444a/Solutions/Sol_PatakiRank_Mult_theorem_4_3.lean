-- Prove2me | solution 1 for PatakiRank.Mult.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T19:16:37.421989+00:00
-- url     : https://prove2.me/submissions/c102d11e-cb5a-456e-9ac8-a49601d595db

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting
import Theorems.Thm_PatakiRank_Mult_lemma_4_2
import Theorems.Thm_PatakiRank_Mult_theorem_2_2
import Theorems.Thm_PatakiRank_Mult_eq_4_31
import Theorems.Thm_PatakiRank_Mult_theorem_3_3
import Theorems.Thm_PatakiRank_Mult_rank_identity

/-!
Theorem 4.3 of Pataki (Math. Oper. Res. 23(2), 1998, p. 349), reduced to Lemma 4.2
(`lemma_4_2`), Theorem 2.2 (`theorem_2_2`), (4.31) (`eq_4_31`), Theorem 3.3 (`theorem_3_3`)
and the rank identity behind (4.30) (`rank_identity`). The glue proved here: the feasible set
(4.26) is a `multiFeas` instance (p = 2 blocks, q = m + 1 free variables, one matrix equation)
up to a linear isomorphism, faces and `convDim` transfer along it, the sorted spectral
decomposition of `A(x*)`, rank counts of `Q diag(v) Qᵀ`, and the triangular-number arithmetic.
-/

set_option autoImplicit false

open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

open PatakiRank.Mult in
theorem pr43_isFace_preimage {E E' : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup E']
    [Module ℝ E'] (e : E ≃ₗ[ℝ] E') {S F : Set E'} (h : IsFace S F) :
    IsFace (e ⁻¹' S) (e ⁻¹' F) := by
  obtain ⟨hFS, hconv, hface⟩ := h
  refine ⟨Set.preimage_mono hFS, hconv.linear_preimage e.toLinearMap, ?_⟩
  intro x hx y hy z hz hxyz
  have h2 : e x = (1 / 2 : ℝ) • (e y + e z) := by rw [hxyz, map_smul, map_add]
  exact hface (e x) hx (e y) hy (e z) hz h2

open PatakiRank.Mult in
theorem pr43_convDim_preimage {E E' : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup E'] [Module ℝ E'] [FiniteDimensional ℝ E']
    (e : E ≃ₗ[ℝ] E') (S : Set E') : convDim (e ⁻¹' S) = convDim S := by
  have hset : {p : ℕ | ∃ v : Fin p → E, (∀ i, v i ∈ e ⁻¹' S) ∧ AffineIndependent ℝ v} =
      {p : ℕ | ∃ v : Fin p → E', (∀ i, v i ∈ S) ∧ AffineIndependent ℝ v} := by
    ext p
    constructor
    · rintro ⟨v, hv, hai⟩
      exact ⟨e ∘ v, fun i => hv i, hai.map' e.toLinearMap.toAffineMap e.injective⟩
    · rintro ⟨v, hv, hai⟩
      refine ⟨e.symm ∘ v, fun i => by simpa using hv i, ?_⟩
      exact hai.map' e.symm.toLinearMap.toAffineMap e.symm.injective
  unfold convDim
  rw [hset]

theorem pr43_psi (n m : ℕ) :
    ∃ ψ : ((Fin 2 → Matrix (Fin n) (Fin n) ℝ) × (Fin (m + 1) → ℝ)) ≃ₗ[ℝ]
      ((Fin m → ℝ) × ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ),
    ∀ p, ψ p = (Fin.tail p.2, p.2 0, p.1 0, p.1 1) := by
  refine ⟨{ toFun := fun p => (Fin.tail p.2, p.2 0, p.1 0, p.1 1)
            invFun := fun q => (![q.2.2.1, q.2.2.2], Fin.cons q.2.1 q.1)
            map_add' := fun p q => rfl
            map_smul' := fun c p => rfl
            left_inv := ?_
            right_inv := ?_ }, fun p => rfl⟩
  · rintro ⟨X, y⟩
    refine Prod.ext ?_ (Fin.cons_self_tail y)
    funext i
    fin_cases i <;> rfl
  · rintro ⟨x, z, V, W⟩
    exact Prod.ext (by show Fin.tail (Fin.cons z x : Fin (m + 1) → ℝ) = x; exact Fin.tail_cons _ _) rfl

open PatakiRank.Mult in
theorem pr43_multiFeas_eq {n m : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (ψ : ((Fin 2 → Matrix (Fin n) (Fin n) ℝ) × (Fin (m + 1) → ℝ)) ≃ₗ[ℝ]
      ((Fin m → ℝ) × ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ))
    (hψ : ∀ p, ψ p = (Fin.tail p.2, p.2 0, p.1 0, p.1 1)) :
    multiFeas (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)
      (fun _ : Fin 1 => ![(1 : ℝ), -1])
      (fun _ : Fin 1 => (Fin.cons 1 (fun i => -A i) : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ))
      (fun _ : Fin 1 => A0) = ψ ⁻¹' feas426 A0 A := by
  ext ⟨X, y⟩
  have key : ∑ j : Fin 2, ![(1 : ℝ), -1] j • X j +
      ∑ j : Fin (m + 1), y j • (Fin.cons 1 (fun i => -A i) : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) j
        - A0 =
      y 0 • (1 : Matrix (Fin n) (Fin n) ℝ) + X 0 - X 1 - (A0 + ∑ i, Fin.tail y i • A i) := by
    rw [Fin.sum_univ_two, Fin.sum_univ_succ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.cons_zero,
      Fin.cons_succ, one_smul, neg_one_smul, smul_neg, Finset.sum_neg_distrib, Fin.tail]
    abel
  have key' : (∑ j : Fin 2, ![(1 : ℝ), -1] j • X j +
      ∑ j : Fin (m + 1), y j • (Fin.cons 1 (fun i => -A i) : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) j
        = A0) ↔
      (y 0 • (1 : Matrix (Fin n) (Fin n) ℝ) + X 0 - X 1 = A0 + ∑ i, Fin.tail y i • A i) := by
    rw [← sub_eq_zero, key, sub_eq_zero]
  simp only [multiFeas, feas426, sdpFeas, Aff, Set.mem_setOf_eq, Set.mem_preimage, hψ,
    Fin.forall_fin_two, Fin.forall_fin_one, IsEmpty.forall_iff, true_and, key']
  tauto

theorem pr43_aff_symm {n m : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA0 : A0.IsSymm) (hA : ∀ i, (A i).IsSymm)
    (x : Fin m → ℝ) : (PatakiRank.Mult.Aff A0 A x).IsSymm := by
  unfold PatakiRank.Mult.Aff Matrix.IsSymm
  rw [transpose_add, transpose_sum]
  simp only [transpose_smul, (hA _).eq, hA0.eq]

theorem pr43_eig_decomp {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
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

theorem pr43_tri_two (i : ℕ) : 2 * PatakiRank.Mult.tri i = i * (i + 1) := by
  unfold PatakiRank.Mult.tri
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self i).two_dvd

theorem pr43_tri_mono {a b : ℕ} (h : a ≤ b) : PatakiRank.Mult.tri a ≤ PatakiRank.Mult.tri b := by
  unfold PatakiRank.Mult.tri
  exact Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

theorem pr43_tri_split (a c : ℕ) :
    PatakiRank.Mult.tri (a + c) = PatakiRank.Mult.tri a + PatakiRank.Mult.tri c + a * c := by
  have h1 := pr43_tri_two (a + c)
  have h2 := pr43_tri_two a
  have h3 := pr43_tri_two c
  have h4 : (a + c) * (a + c + 1) = a * (a + 1) + c * (c + 1) + 2 * (a * c) := by ring
  omega

open PatakiRank.Mult in
theorem solution {n m k : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA0 : A0.IsSymm) (hA : ∀ i, (A i).IsSymm)
    (hind : LinearIndependent ℝ (Fin.cons A0 A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ))
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkn : k < n)
    (xs : Fin m → ℝ) (hx : IsExtremePt (Theta k A0 A) xs) (hmk : k * (n - k) < m) :
    eig (Aff A0 A xs) ⟨k - 1, by omega⟩ = eig (Aff A0 A xs) ⟨k, hkn⟩ ∧
      (n : ℤ) - (tau ((tri n : ℤ) - m - 1) (k - 1) (n - k - 1) : ℤ) ≤
        (mult (Aff A0 A xs) ⟨k - 1, by omega⟩ : ℤ) := by
  have hBs : (Aff A0 A xs).IsSymm := pr43_aff_symm A0 A hA0 hA xs
  obtain ⟨Q, hQ, hanti, hBQ⟩ := pr43_eig_decomp (Aff A0 A xs) hBs
  have hmono : ∀ i j : Fin n, i ≤ j → eig (Aff A0 A xs) j ≤ eig (Aff A0 A xs) i :=
    fun i j h => hanti h
  have T33 := theorem_3_3 (Aff A0 A xs) Q (fun i => eig (Aff A0 A xs) i) hQ hanti hBQ hk hkn
  have hle : eig (Aff A0 A xs) ⟨k, hkn⟩ ≤ eig (Aff A0 A xs) ⟨k - 1, by omega⟩ :=
    hmono _ _ (Fin.le_def.2 (show k - 1 ≤ k by omega))
  set lk := eig (Aff A0 A xs) ⟨k - 1, by omega⟩ with hlk
  set lk1 := eig (Aff A0 A xs) ⟨k, hkn⟩ with hlk1
  set z : ℝ := (1 / 2 : ℝ) * (lk + lk1) with hz
  set V := Q * diagonal (vStar k (fun i => eig (Aff A0 A xs) i) z) * Qᵀ with hV
  set W := Q * diagonal (wStar k (fun i => eig (Aff A0 A xs) i) z) * Qᵀ with hW
  have hopt : IsOptimal (sdpFeas (Aff A0 A xs)) (sdpObj k) (z, V, W) :=
    (T33.2 (z, V, W)).2 ⟨⟨by simp only; linarith, by simp only; linarith⟩, rfl, rfl⟩
  -- the rank bound of Theorem 2.2 on the face `F*` of (4.26)
  obtain ⟨ψ, hψ⟩ := pr43_psi n m
  have hface := lemma_4_2 A0 A hA0 hA hind hm hk hkn xs hx
  have hface' := pr43_isFace_preimage ψ hface
  rw [← pr43_multiFeas_eq A0 A ψ hψ] at hface'
  have hmem : ((![V, W] : Fin 2 → Matrix (Fin n) (Fin n) ℝ), (Fin.cons z xs : Fin (m + 1) → ℝ)) ∈
      ψ ⁻¹' Fstar k A0 A xs := by
    rw [Set.mem_preimage, hψ]
    exact ⟨by show Fin.tail (Fin.cons z xs : Fin (m + 1) → ℝ) = xs; exact Fin.tail_cons _ _, hopt⟩
  have hD : ∀ (i : Fin 1) (j : Fin (m + 1)),
      ((Fin.cons 1 (fun i => -A i) : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) j).IsSymm := by
    intro _ j
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [Fin.cons_zero]; exact isSymm_one
    · rw [Fin.cons_succ]; exact (hA i).neg
  have T22 := theorem_2_2 _ _ _ _ _ (fun i => i.elim0) hD (fun _ => hA0) _ hface' _ _ hmem
  rw [pr43_convDim_preimage, eq_4_31 A0 A hA0 hA hind hm hk hkn xs, Fin.sum_univ_two] at T22
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at T22
  -- (4.29)
  have heq : lk = lk1 := by
    by_contra hne
    have hlt : lk1 < lk := lt_of_le_of_ne hle (Ne.symm hne)
    rw [if_pos hlt] at T22
    have hVr : k ≤ V.rank := by
      rw [hV, pr43_rank_conj Q hQ]
      apply pr43_card_ge _ 0 k (by omega)
      intro i _ hi
      have h1 : lk ≤ eig (Aff A0 A xs) i := hmono _ _ (Fin.le_def.2 (show (i : ℕ) ≤ k - 1 by omega))
      simp only [vStar, if_pos (show (i : ℕ) < k by omega)]
      intro h0
      linarith
    have hWr : n - k ≤ W.rank := by
      rw [hW, pr43_rank_conj Q hQ]
      apply pr43_card_ge _ k (n - k) (by omega)
      intro i hi _
      have h1 : eig (Aff A0 A xs) i ≤ lk1 := hmono _ _ (Fin.le_def.2 (show k ≤ (i : ℕ) by omega))
      simp only [wStar, if_neg (show ¬ (i : ℕ) < k by omega)]
      intro h0
      linarith
    have t1 := pr43_tri_mono hVr
    have t2 := pr43_tri_mono hWr
    have hid : tri n = tri k + tri (n - k) + k * (n - k) := by
      have := pr43_tri_split k (n - k)
      rwa [Nat.add_sub_cancel' hkn.le] at this
    push_cast at T22
    omega
  refine ⟨heq, ?_⟩
  rw [if_neg (show ¬ lk1 < lk by rw [heq]; exact lt_irrefl _)] at T22
  have hzk : z = lk := by rw [hz, heq]; ring
  have hRI := rank_identity (Aff A0 A xs) hBs hk hkn heq (z, V, W) hopt rfl
  have hVr : V.rank ≤ k - 1 := by
    rw [hV, pr43_rank_conj Q hQ]
    apply pr43_card_le _ 0 (k - 1)
    intro i hi
    simp only [vStar] at hi
    split_ifs at hi with hik
    · refine ⟨Nat.zero_le _, ?_⟩
      by_contra hcon
      have hiv : i = ⟨k - 1, by omega⟩ := Fin.ext (by simp; omega)
      apply hi
      rw [hiv, hzk]
      simp [hlk]
    · exact absurd rfl hi
  have hWr : W.rank ≤ n - k - 1 := by
    rw [hW, pr43_rank_conj Q hQ]
    apply pr43_card_le _ (k + 1) (n - k - 1)
    intro i hi
    simp only [wStar] at hi
    split_ifs at hi with hik
    · exact absurd rfl hi
    · refine ⟨?_, by omega⟩
      by_contra hcon
      have hiv : i = ⟨k, hkn⟩ := Fin.ext (by simp; omega)
      apply hi
      rw [hiv, hzk, heq]
      simp [hlk1]
  have htau : V.rank + W.rank ≤ tau ((tri n : ℤ) - m - 1) (k - 1) (n - k - 1) := by
    unfold tau
    apply Finset.le_sup (f := fun ij : ℕ × ℕ => ij.1 + ij.2) (b := (V.rank, W.rank))
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    push_cast at T22 ⊢
    omega
  simp only at hRI
  omega
