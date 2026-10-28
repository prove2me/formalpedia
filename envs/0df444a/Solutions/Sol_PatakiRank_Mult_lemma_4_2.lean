-- Prove2me | solution 1 for PatakiRank.Mult.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T18:18:20.185157+00:00
-- url     : https://prove2.me/submissions/3d850d9b-0403-44a7-a47f-ee9d8ccbf422

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting

/-!
Lemma 4.2 of Pataki (Math. Oper. Res. 23(2), 1998, p. 349). The optimal value of the SDP (3.14)
for a symmetric `B` equals `f_k(B)`: every feasible `(z, V, W)` has `k z + tr V ≥ f_k(B)`
(conjugate by the eigenvector matrix and read off the diagonal), and the point
`z = λ_k`, `V = Q diag(v*) Qᵀ`, `W = Q diag(w*) Qᵀ` attains it. Then a midpoint argument on the
linear objective and the extremality of `x*` in `Θ` gives the face property.
-/

set_option autoImplicit false

open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

theorem l42_aff_symm {n m : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA0 : A0.IsSymm) (hA : ∀ i, (A i).IsSymm)
    (x : Fin m → ℝ) : (PatakiRank.Mult.Aff A0 A x).IsSymm := by
  unfold PatakiRank.Mult.Aff Matrix.IsSymm
  rw [transpose_add, transpose_sum]
  simp only [transpose_smul, (hA _).eq, hA0.eq]

theorem l42_eig_decomp {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
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

theorem l42_frob_one {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) : frob 1 V = V.trace := by
  unfold frob
  simp

theorem l42_card {n k : ℕ} (hkn : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  have h := Fin.card_filter_val_lt (n := n) (m := k)
  rw [h]
  omega

/-- Lower bound: every feasible point of (3.14) has objective at least `f_k(B)`. -/
theorem l42_lb {n k : ℕ} (hkn : k ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (p : ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (hp : PatakiRank.Mult.sdpFeas B p) :
    PatakiRank.Mult.fk k B ≤ PatakiRank.Mult.sdpObj k p := by
  obtain ⟨z, V, W⟩ := p
  obtain ⟨hV, hW, hEq⟩ := hp
  simp only at hV hW hEq
  obtain ⟨Q, hQ, -, hBQ⟩ := l42_eig_decomp B hB
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
  rw [l42_frob_one, htr]
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
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hS, l42_card hkn]
    _ ≤ (k : ℝ) * z + (Qᵀ * V * Q).trace := by
        have : ∑ i ∈ S, (Qᵀ * V * Q) i i ≤ ∑ i, (Qᵀ * V * Q) i i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => hV'.diag_nonneg)
        unfold Matrix.trace
        simp only [Matrix.diag_apply]
        linarith

/-- Attainment: the point `z = λ_k`, `V = Q diag(v*) Qᵀ`, `W = Q diag(w*) Qᵀ` is feasible with
objective at most `f_k(B)`. -/
theorem l42_attain {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsSymm) :
    ∃ p, PatakiRank.Mult.sdpFeas B p ∧ PatakiRank.Mult.sdpObj k p ≤ PatakiRank.Mult.fk k B := by
  obtain ⟨Q, hQ, hanti, hBQ⟩ := l42_eig_decomp B hB
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  set lam : Fin n → ℝ := fun i => eig B i with hlamdef
  set z : ℝ := lam ⟨k - 1, by omega⟩ with hzdef
  set v : Fin n → ℝ := PatakiRank.Mult.vStar k lam z with hvdef
  set w : Fin n → ℝ := PatakiRank.Mult.wStar k lam z with hwdef
  have hv : ∀ i, 0 ≤ v i := by
    intro i
    simp only [hvdef, PatakiRank.Mult.vStar]
    split_ifs with h
    · have : lam ⟨k - 1, by omega⟩ ≤ lam i := hanti (by rw [Fin.le_def]; simp; omega)
      simp only [hzdef]
      linarith
    · exact le_refl 0
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    simp only [hwdef, PatakiRank.Mult.wStar]
    split_ifs with h
    · exact le_refl 0
    · have : lam i ≤ lam ⟨k - 1, by omega⟩ := hanti (by rw [Fin.le_def]; simp; omega)
      simp only [hzdef]
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
  refine ⟨(z, Q * diagonal v * Qᵀ, Q * diagonal w * Qᵀ), ⟨hpsd v hv, hpsd w hw, ?_⟩, ?_⟩
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
    rw [l42_frob_one]
    have htr : (Q * diagonal v * Qᵀ).trace = ∑ i, v i := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQ, Matrix.one_mul, Matrix.trace_diagonal]
    rw [htr]
    have hsv : ∑ i, v i = ∑ i : Fin n with i.val < k, (lam i - z) := by
      rw [Finset.sum_filter]
      rfl
    rw [hsv, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, l42_card hkn]
    have : ∑ i : Fin n with i.val < k, lam i = ∑ i : Fin n with i.val < k, eig B i := rfl
    rw [this]
    ring

theorem l42_aff_comb {n m : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (x y : Fin m → ℝ) (a b : ℝ) (hab : a + b = 1) :
    PatakiRank.Mult.Aff A0 A (a • x + b • y)
      = a • PatakiRank.Mult.Aff A0 A x + b • PatakiRank.Mult.Aff A0 A y := by
  unfold PatakiRank.Mult.Aff
  have h0 : A0 = a • A0 + b • A0 := by rw [← add_smul, hab, one_smul]
  conv_lhs => rw [h0]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
  abel

theorem l42_feas_comb {n m : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (x y : Fin m → ℝ)
    (p q : ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (hp : PatakiRank.Mult.sdpFeas (PatakiRank.Mult.Aff A0 A x) p)
    (hq : PatakiRank.Mult.sdpFeas (PatakiRank.Mult.Aff A0 A y) q)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    PatakiRank.Mult.sdpFeas (PatakiRank.Mult.Aff A0 A (a • x + b • y)) (a • p + b • q) := by
  obtain ⟨z1, V1, W1⟩ := p
  obtain ⟨z2, V2, W2⟩ := q
  obtain ⟨hV1, hW1, hE1⟩ := hp
  obtain ⟨hV2, hW2, hE2⟩ := hq
  simp only at hV1 hW1 hE1 hV2 hW2 hE2
  refine ⟨?_, ?_, ?_⟩
  · exact (hV1.smul ha).add (hV2.smul hb)
  · exact (hW1.smul ha).add (hW2.smul hb)
  · show (a * z1 + b * z2) • (1 : Matrix (Fin n) (Fin n) ℝ) + (a • V1 + b • V2)
        - (a • W1 + b • W2) = PatakiRank.Mult.Aff A0 A (a • x + b • y)
    rw [l42_aff_comb A0 A x y a b hab, ← hE1, ← hE2]
    simp only [add_smul, mul_smul, smul_add, smul_sub]
    abel

theorem l42_obj_comb {n k : ℕ} (p q : ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (a b : ℝ) :
    PatakiRank.Mult.sdpObj k (a • p + b • q)
      = a * PatakiRank.Mult.sdpObj k p + b * PatakiRank.Mult.sdpObj k q := by
  obtain ⟨z1, V1, W1⟩ := p
  obtain ⟨z2, V2, W2⟩ := q
  unfold PatakiRank.Mult.sdpObj
  show (k : ℝ) * (a * z1 + b * z2) + frob 1 (a • V1 + b • V2)
    = a * ((k : ℝ) * z1 + frob 1 V1) + b * ((k : ℝ) * z2 + frob 1 V2)
  rw [l42_frob_one, l42_frob_one, l42_frob_one, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  ring

open PatakiRank.Mult in
theorem solution {n m k : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA0 : A0.IsSymm) (hA : ∀ i, (A i).IsSymm)
    (hind : LinearIndependent ℝ (Fin.cons A0 A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ))
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkn : k < n)
    (xs : Fin m → ℝ) (hx : IsExtremePt (Theta k A0 A) xs) :
    IsFace (feas426 A0 A) (Fstar k A0 A xs) := by
  have hkn' : k ≤ n := hkn.le
  have hsymm : ∀ x, (Aff A0 A x).IsSymm := fun x => l42_aff_symm A0 A hA0 hA x
  have hxs : xs ∈ Theta k A0 A := hx.1 (Set.mem_singleton xs)
  have hval : ∀ x, ∀ p ∈ Omega k (Aff A0 A x), sdpObj k p = fk k (Aff A0 A x) := by
    intro x p hp
    obtain ⟨q, hq, hqle⟩ := l42_attain hk hkn' _ (hsymm x)
    exact le_antisymm (le_trans (hp.2 q hq) hqle) (l42_lb hkn' _ (hsymm x) p hp.1)
  have hlb : ∀ x p, sdpFeas (Aff A0 A x) p → fk k (Aff A0 A x) ≤ sdpObj k p :=
    fun x p hp => l42_lb hkn' _ (hsymm x) p hp
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨h1, h2⟩ := hp
    show sdpFeas (Aff A0 A p.1) p.2
    rw [h1]
    exact h2.1
  · intro p hp q hq a b ha hb hab
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hq1, hq2⟩ := hq
    have hfst : (a • p + b • q).1 = xs := by
      simp only [Prod.fst_add, Prod.smul_fst, hp1, hq1, ← add_smul, hab, one_smul]
    refine ⟨hfst, ?_, ?_⟩
    · have h := l42_feas_comb A0 A xs xs p.2 q.2 hp2.1 hq2.1 a b ha hb hab
      rw [← add_smul, hab, one_smul] at h
      simpa only [Prod.snd_add, Prod.smul_snd] using h
    · intro r hr
      have hobj : sdpObj k (a • p + b • q).2 = fk k (Aff A0 A xs) := by
        simp only [Prod.snd_add, Prod.smul_snd]
        rw [l42_obj_comb, hval xs p.2 hp2, hval xs q.2 hq2, ← add_mul, hab, one_mul]
      rw [hobj]
      exact hlb xs r hr
  · intro p hp q hq r hr hpqr
    obtain ⟨hp1, hp2⟩ := hp
    have hq' : sdpFeas (Aff A0 A q.1) q.2 := hq
    have hr' : sdpFeas (Aff A0 A r.1) r.2 := hr
    have hmid1 : xs = (1 / 2 : ℝ) • (q.1 + r.1) := by
      rw [← hp1, hpqr]
      simp only [Prod.smul_fst, Prod.fst_add]
    have hmid2 : p.2 = (1 / 2 : ℝ) • q.2 + (1 / 2 : ℝ) • r.2 := by
      rw [hpqr]
      simp only [Prod.smul_snd, Prod.snd_add, smul_add]
    have hpv := hval xs p.2 hp2
    have hcomb := l42_obj_comb (k := k) q.2 r.2 (1 / 2 : ℝ) (1 / 2 : ℝ)
    rw [← hmid2, hpv] at hcomb
    have hq_lb := hlb q.1 q.2 hq'
    have hr_lb := hlb r.1 r.2 hr'
    have hqm := hxs q.1
    have hrm := hxs r.1
    have hqT : q.1 ∈ Theta k A0 A := fun y => by
      have := hxs y
      linarith
    have hrT : r.1 ∈ Theta k A0 A := fun y => by
      have := hxs y
      linarith
    obtain ⟨hqs, hrs⟩ := hx.2.2 xs (Set.mem_singleton xs) q.1 hqT r.1 hrT hmid1
    rw [Set.mem_singleton_iff] at hqs hrs
    refine ⟨⟨hqs, ?_, ?_⟩, ⟨hrs, ?_, ?_⟩⟩
    · rw [← hqs]; exact hq'
    · intro s hs
      have := hlb xs s hs
      linarith
    · rw [← hrs]; exact hr'
    · intro s hs
      have := hlb xs s hs
      linarith
