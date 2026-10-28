-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.homogeneous_moment_hierarchy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:54:47.551876+00:00
-- url     : https://prove2.me/submissions/a784c99b-31ae-4ea4-a37a-79517973e79b

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
noncomputable section


open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

section HMHB_PS
open Matrix Finset WithLp

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma HMHB_tr_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A ^ 2).trace = ∑ i, ((hA.eigenvalues i : ℂ)) ^ 2 := by
  have h := hA.spectral_theorem
  conv_lhs => rw [h]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, diagonal_pow, trace_diagonal]
  simp

lemma HMHB_adj_expand {q : ℕ} (w : Fin q → ℝ) (u : Fin q → n → ℂ) (v : Fin q → m → ℂ)
    (R : Matrix n m ℂ) (hR : R = ∑ j, (w j : ℂ) • Matrix.of (fun i k => u j i * v j k))
    (x : n → ℂ) :
    Rᴴ *ᵥ x = ∑ j, ((w j : ℂ) * (x ⬝ᵥ star (u j))) • star (v j) := by
  ext k
  subst hR
  simp only [mulVec, dotProduct, conjTranspose_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.star_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, star_sum,
    star_mul', Complex.star_def, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  ring

lemma HMHB_gram (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i k : n) :
    inner ℂ (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i))) (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis k)))
      = (hM.eigenvalues k : ℂ) * inner ℂ (hM.eigenvectorBasis i) (hM.eigenvectorBasis k) := by
  rw [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_eq_star_dotProduct, star_mulVec,
    dotProduct_comm, ← dotProduct_mulVec, conjTranspose_conjTranspose, mulVec_mulVec,
    hM.mulVec_eigenvectorBasis, dotProduct_comm]
  rw [smul_dotProduct, Complex.real_smul]

lemma HMHB_ccnr {q : ℕ} (w : Fin q → ℝ) (hw : ∀ j, 0 ≤ w j) (u : Fin q → n → ℂ)
    (v : Fin q → m → ℂ)
    (hu : ∀ j, ‖(toLp 2 (u j) : EuclideanSpace ℂ n)‖ ≤ 1)
    (hv : ∀ j, ‖(toLp 2 (star (v j)) : EuclideanSpace ℂ m)‖ ≤ 1)
    (R : Matrix n m ℂ) (hR : R = ∑ j, (w j : ℂ) • Matrix.of (fun i k => u j i * v j k))
    (hM : (R * Rᴴ).IsHermitian) :
    ∑ i, ‖(toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ m)‖ ≤ ∑ j, w j := by
  set e := hM.eigenvectorBasis with he
  set g : n → EuclideanSpace ℂ m := fun i => toLp 2 (Rᴴ *ᵥ ⇑(e i)) with hg
  set U : Fin q → EuclideanSpace ℂ n := fun j => toLp 2 (u j) with hU
  set Vb : Fin q → EuclideanSpace ℂ m := fun j => toLp 2 (star (v j)) with hVb
  have hgexp : ∀ i, g i = ∑ j, ((w j : ℂ) * inner ℂ (U j) (e i)) • Vb j := by
    intro i
    simp only [hg, hU, hVb]
    rw [HMHB_adj_expand w u v R hR]
    apply (WithLp.equiv 2 _).injective
    ext k
    simp [EuclideanSpace.inner_eq_star_dotProduct]
  have hgg : ∀ i k, inner ℂ (g i) (g k) = (hM.eigenvalues k : ℂ) * inner ℂ (e i) (e k) :=
    HMHB_gram R hM
  have hon := orthonormal_iff_ite.mp e.orthonormal
  have hnorm : ∀ i, ‖g i‖ ^ 2 = hM.eigenvalues i := by
    intro i
    have := hgg i i
    rw [inner_self_eq_norm_sq_to_K, hon i i, if_pos rfl, mul_one] at this
    have h := congrArg Complex.re this
    simpa [← Complex.ofReal_pow] using h
  set s := (univ : Finset n).filter (fun i => hM.eigenvalues i ≠ 0) with hs
  have hpos : ∀ i : s, ‖g i‖ ≠ 0 := by
    intro i h
    have := hnorm i
    rw [h] at this
    exact (Finset.mem_filter.mp i.2).2 (by rw [← this]; ring)
  set f : s → EuclideanSpace ℂ m := fun i => ((‖g i‖ : ℂ)⁻¹) • g i with hf
  have hfon : Orthonormal ℂ f := by
    rw [orthonormal_iff_ite]
    intro i k
    simp only [hf, inner_smul_left, inner_smul_right, hgg, hon]
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl, if_pos rfl, mul_one]
      have h2 : ((hM.eigenvalues i : ℝ) : ℂ) = (‖g i‖ : ℂ) ^ 2 := by
        rw [← hnorm]; push_cast; rfl
      rw [h2]
      have : (‖g i‖ : ℂ) ≠ 0 := by exact_mod_cast hpos i
      simp only [map_inv₀, Complex.conj_ofReal]
      field_simp
    · rw [if_neg (fun h => hik (Subtype.ext h)), if_neg hik]; ring
  have hes : Orthonormal ℂ (fun i : s => e i) :=
    e.orthonormal.comp (fun i : s => (i : n)) Subtype.val_injective
  -- per-index bound
  have hi : ∀ i : s, ‖g i‖ ≤ ∑ j, w j * (‖inner ℂ (e i) (U j)‖ * ‖inner ℂ (f i) (Vb j)‖) := by
    intro i
    have h1 : inner ℂ (f i) (g i) = (‖g i‖ : ℂ) := by
      simp only [hf, inner_smul_left, inner_self_eq_norm_sq_to_K, map_inv₀, Complex.conj_ofReal]
      have : (‖g i‖ : ℂ) ≠ 0 := by exact_mod_cast hpos i
      field_simp
      rfl
    have h2 : ‖g i‖ = ‖inner ℂ (f i) (g i)‖ := by
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [h2, hgexp, inner_sum]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun j _ => ?_)))
    rw [inner_smul_right, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hw j), norm_inner_symm]
    ring
  have hsum : ∑ i, ‖g i‖ = ∑ i : s, ‖g i‖ := by
    rw [Finset.sum_coe_sort s (fun i => ‖g i‖), hs, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with h
    · rfl
    · rw [ne_eq, not_not] at h
      have := hnorm i
      rw [h] at this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  change ∑ i, ‖g i‖ ≤ _
  rw [hsum]
  calc ∑ i : s, ‖g i‖ ≤ ∑ i : s, ∑ j, w j * (‖inner ℂ (e i) (U j)‖ * ‖inner ℂ (f i) (Vb j)‖) :=
        Finset.sum_le_sum (fun i _ => hi i)
    _ = ∑ j, w j * ∑ i : s, ‖inner ℂ (e i) (U j)‖ * ‖inner ℂ (f i) (Vb j)‖ := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ j, w j * 1 := by
        refine Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left ?_ (hw j))
        refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
        have b1 := hes.sum_inner_products_le (x := U j) (s := univ)
        have b2 := hfon.sum_inner_products_le (x := Vb j) (s := univ)
        have c1 : ‖U j‖ ^ 2 ≤ 1 := by
          have := hu j; have := norm_nonneg (U j); nlinarith
        have c2 : ‖Vb j‖ ^ 2 ≤ 1 := by
          have := hv j; have := norm_nonneg (Vb j); nlinarith
        have d1 : Real.sqrt (∑ i : s, ‖inner ℂ (e i) (U j)‖ ^ 2) ≤ 1 :=
          Real.sqrt_le_one.mpr (b1.trans c1)
        have d2 : Real.sqrt (∑ i : s, ‖inner ℂ (f i) (Vb j)‖ ^ 2) ≤ 1 :=
          Real.sqrt_le_one.mpr (b2.trans c2)
        calc _ ≤ 1 * 1 := mul_le_mul d1 d2 (Real.sqrt_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = ∑ j, w j := by simp



lemma HMHB_offsum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ι → ℝ) :
    ∑ p ∈ (univ : Finset ι).offDiag, f p.1 p.2 = (∑ i, ∑ j, f i j) - ∑ i, f i i := by
  have h := Finset.diag_union_offDiag (univ : Finset ι)
  have hd := Finset.disjoint_diag_offDiag (univ : Finset ι)
  have : ∑ p ∈ (univ : Finset ι) ×ˢ univ, f p.1 p.2 =
      ∑ p ∈ (univ : Finset ι).diag, f p.1 p.2 + ∑ p ∈ (univ : Finset ι).offDiag, f p.1 p.2 := by
    rw [← h, Finset.sum_union hd]
  rw [Finset.sum_product] at this
  have hdiag : ∑ p ∈ (univ : Finset ι).diag, f p.1 p.2 = ∑ i, f i i := by
    rw [Finset.diag, Finset.sum_map]; rfl
  linarith

lemma HMHB_scalar {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (t : ℝ) (ht : ∑ i, σ i ≤ t) :
    2 * ((∑ i, σ i ^ 2) ^ 2 - ∑ i, (σ i ^ 2) ^ 2) ≤ (t ^ 2 - ∑ i, σ i ^ 2) ^ 2 := by
  set D := (univ : Finset ι).offDiag
  set x : ι × ι → ℝ := fun p => σ p.1 * σ p.2
  have hx : ∀ p, 0 ≤ x p := fun p => mul_nonneg (hσ _) (hσ _)
  have hQ : ∑ p ∈ D, x p = (∑ i, σ i) ^ 2 - ∑ i, σ i ^ 2 := by
    rw [HMHB_offsum (fun i j => σ i * σ j), sq, Finset.sum_mul_sum]; simp [sq]
  have hQ2 : ∑ p ∈ D, x p ^ 2 = (∑ i, σ i ^ 2) ^ 2 - ∑ i, (σ i ^ 2) ^ 2 := by
    rw [HMHB_offsum (fun i j => (σ i * σ j) ^ 2), sq (∑ i, σ i ^ 2), Finset.sum_mul_sum]
    congr 1
    · simp [mul_pow]
    · simp [sq]
  have key : 2 * ∑ p ∈ D, x p ^ 2 ≤ (∑ p ∈ D, x p) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp' : p.swap ∈ D := by simpa [D, Finset.mem_offDiag, eq_comm] using hp
    have hne : p ≠ p.swap := by
      intro h; simp [D, Finset.mem_offDiag] at hp
      exact hp (by simpa using congrArg Prod.fst h)
    have hsub : ({p, p.swap} : Finset (ι × ι)) ⊆ D := by
      intro q hq; simp at hq; rcases hq with rfl | rfl <;> assumption
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun q => x p * x q) (fun q _ _ => mul_nonneg (hx p) (hx q))
    rw [Finset.sum_pair hne] at this
    have hs : x p.swap = x p := by simp [x, mul_comm]
    rw [hs] at this; nlinarith
  have hs0 : 0 ≤ ∑ p ∈ D, x p := Finset.sum_nonneg (fun p _ => hx p)
  have hst : (∑ i, σ i) ^ 2 ≤ t ^ 2 := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ univ) => hσ i)
    nlinarith
  rw [← hQ2]
  have : (∑ p ∈ D, x p) ^ 2 ≤ (t ^ 2 - ∑ i, σ i ^ 2) ^ 2 := by
    apply pow_le_pow_left₀ hs0; linarith
  linarith

lemma HMHB_gnorm (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i : n) :
    ‖(toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ m)‖ ^ 2 = hM.eigenvalues i := by
  have := HMHB_gram R hM i i
  rw [inner_self_eq_norm_sq_to_K, orthonormal_iff_ite.mp (hM.eigenvectorBasis).orthonormal i i,
    if_pos rfl, mul_one] at this
  have h := congrArg Complex.re this
  simpa [← Complex.ofReal_pow] using h

lemma HMHB_frob {A : Matrix n n ℂ} (hA : A.PosSemidef) (htr : A.trace = 1) :
    ∑ i, ∑ k, ‖A i k‖ ^ 2 ≤ 1 := by
  have hH := hA.1
  have e1 : ((A ^ 2).trace).re = ∑ i, ∑ k, ‖A i k‖ ^ 2 := by
    have : A ^ 2 = A * Aᴴ := by rw [hH.eq, sq]
    rw [this]
    simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
  rw [← e1, HMHB_tr_sq hH]
  have hl : ∀ i, 0 ≤ hH.eigenvalues i := hA.eigenvalues_nonneg
  have hs : ∑ i, hH.eigenvalues i = 1 := by
    have := congrArg Complex.re (hH.trace_eq_sum_eigenvalues)
    rw [htr] at this; simpa using this.symm
  have : ∑ i, hH.eigenvalues i ^ 2 ≤ (∑ i, hH.eigenvalues i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hl i)
  rw [hs] at this
  simpa [← Complex.ofReal_pow] using this

omit [DecidableEq n] in
lemma HMHB_euc_norm (x : n → ℂ) (h : ∑ i, ‖x i‖ ^ 2 ≤ 1) :
    ‖(toLp 2 x : EuclideanSpace ℂ n)‖ ≤ 1 := by
  rw [EuclideanSpace.norm_eq]
  exact Real.sqrt_le_one.mpr (by simpa using h)

end HMHB_PS

namespace QAlgorithms.Papers.Independent.Information100.P19
lemma HMHB_Fab : alphaPerm 2 (0 : Fin 4) = 3 ∧ alphaPerm 2 (1 : Fin 4) = 2 ∧ alphaPerm 2 (2 : Fin 4) = 1 ∧
  alphaPerm 2 (3 : Fin 4) = 0 ∧ betaPerm 2 (0 : Fin 4) = 1 ∧ betaPerm 2 (1 : Fin 4) = 0 ∧
  betaPerm 2 (2 : Fin 4) = 3 ∧ betaPerm 2 (3 : Fin 4) = 2 := by decide

lemma HMHB_Fprod4 (f : Fin 4 → ℂ) : ∏ r, f r = f 0 * f 1 * f 2 * f 3 := Fin.prod_univ_four f

lemma HMHB_Frmom {a b : ℕ} (X : Bip a b) (hH : X.IsHermitian) :
    Matrix.trace ((realign X * (realign X).conjTranspose)^2) = tensorTrace (alphaPerm 2, betaPerm 2) X := by
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := HMHB_Fab
  simp only [sq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, realign,
    Finset.sum_mul_sum]
  simp only [← Fintype.sum_prod_type']
  unfold tensorTrace
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective
    (fun ij : (Fin 4 → Fin a) × (Fin 4 → Fin b) =>
      ((ij.1 0, ij.1 3), (ij.1 2, ij.1 1), (ij.2 0, ij.2 1), (ij.2 2, ij.2 3)))
    (Function.bijective_iff_has_inverse.mpr ⟨fun q =>
      (![q.1.1, q.2.1.2, q.2.1.1, q.1.2], ![q.2.2.1.1, q.2.2.1.2, q.2.2.2.1, q.2.2.2.2]),
      fun ij => by
        rcases ij with ⟨i, j⟩
        refine Prod.ext ?_ ?_ <;> (ext r; fin_cases r <;> rfl), fun q => rfl⟩) _ _ (fun ij => ?_)
  rcases ij with ⟨i, j⟩
  rw [HMHB_Fprod4]
  simp only [c0, c1, c2, c3, d0, d1, d2, d3, hH.apply]
  ring

/-- Four-index contraction of the Gram factor. -/
def HMHB_FQ {a b : ℕ} (B : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (κ : Fin 4 → Fin a × Fin b) : ℂ :=
  ∑ x : Fin a × Fin b × Fin a × Fin b, star (B (κ 0) (x.1, x.2.1)) * B (κ 1) (x.2.2.1, x.2.1) *
    star (B (κ 2) (x.2.2.1, x.2.2.2)) * B (κ 3) (x.1, x.2.2.2)

lemma HMHB_Fsep_psd {a b : ℕ} {X : Bip a b} (h : QAlgorithms.Entanglement.IsSeparablePositive X) :
    X.PosSemidef := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := h
  exact Matrix.posSemidef_sum _ (fun j _ =>
    ((hAB j).1.1.kronecker (hAB j).2.1).smul (Complex.zero_le_real.mpr (hw j)))


lemma HMHB_tt {n a b : ℕ} (σ : Equiv.Perm (Fin n)) (X : Bip a b) :
    tensorTrace (σ, σ) X = ∑ κ : Fin n → Fin a × Fin b, ∏ r, X (κ r) (κ (σ r)) := by
  unfold tensorTrace
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ (fun ij => rfl)

lemma HMHB_four {T : Type*} [Fintype T] (F : (Fin 4 → T) → ℂ) :
    ∑ κ, F κ = ∑ k3, ∑ k2, ∑ k1, ∑ k0, F ![k0, k1, k2, k3] := by
  have : ∑ κ, F κ = ∑ x : T × T × T × T, F ![x.2.2.2, x.2.2.1, x.2.1, x.1] :=
    Fintype.sum_bijective (fun κ => (κ 3, κ 2, κ 1, κ 0))
      (Function.bijective_iff_has_inverse.mpr ⟨fun x => ![x.2.2.2, x.2.2.1, x.2.1, x.1],
        fun κ => by ext r; fin_cases r <;> rfl, fun x => rfl⟩) _ _
      (fun κ => by congr 1; ext r; fin_cases r <;> rfl)
  rw [this]; simp only [Fintype.sum_prod_type]

lemma HMHB_s12 : s12 0 = 1 ∧ s12 1 = 0 ∧ s12 2 = 2 ∧ s12 3 = 3 := by decide
lemma HMHB_s1234 : (s12*s34) 0 = 1 ∧ (s12*s34) 1 = 0 ∧ (s12*s34) 2 = 3 ∧ (s12*s34) 3 = 2 := by decide

lemma HMHB_t1 {a b : ℕ} (X : Bip a b) : tensorTrace ((1, 1) : Perms 4) X = (Matrix.trace X) ^ 4 := by
  rw [HMHB_tt, HMHB_four]
  simp only [Fin.prod_univ_four, Equiv.Perm.one_apply]
  simp only [Matrix.trace, Matrix.diag, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
  simp

lemma HMHB_t2 {a b : ℕ} (X : Bip a b) :
    tensorTrace (s12, s12) X = Matrix.trace (X * X) * (Matrix.trace X) ^ 2 := by
  obtain ⟨c0, c1, c2, c3⟩ := HMHB_s12
  rw [HMHB_tt, HMHB_four]
  simp only [Fin.prod_univ_four, c0, c1, c2, c3]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
  simp
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))))

lemma HMHB_t3 {a b : ℕ} (X : Bip a b) :
    tensorTrace (s12*s34, s12*s34) X = (Matrix.trace (X * X)) ^ 2 := by
  obtain ⟨c0, c1, c2, c3⟩ := HMHB_s1234
  rw [HMHB_tt, HMHB_four]
  simp only [Fin.prod_univ_four, c0, c1, c2, c3]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
  simp
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))))

lemma HMHB_trace_real {a b : ℕ} {X : Bip a b} (hH : X.IsHermitian) :
    Matrix.trace X = ((mass X : ℝ) : ℂ) := by
  rw [mass, powerTrace, pow_one]
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im, Matrix.trace, Matrix.diag, Complex.im_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have h := congrArg Complex.im (hH.apply i i)
    rw [Complex.star_def, Complex.conj_im] at h
    linarith

lemma HMHB_normsumC {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] (M : Matrix I J ℂ) :
    (M * Mᴴ).trace = ((∑ x : I × J, ‖M x.1 x.2‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ← Fintype.sum_prod_type']
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast

lemma HMHB_r1 {a b : ℕ} (X : Bip a b) :
    rMoment X 1 = ∑ x : (Fin a × Fin b) × (Fin a × Fin b), ‖X x.1 x.2‖ ^ 2 := by
  rw [rMoment, powerTrace, pow_one, HMHB_normsumC, Complex.ofReal_re]
  exact Fintype.sum_equiv
    { toFun := fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))
      invFun := fun y => ((y.1.1, y.2.1), (y.1.2, y.2.2))
      left_inv := fun x => rfl
      right_inv := fun y => rfl } _ _ (fun x => rfl)

lemma HMHB_trsq {a b : ℕ} {X : Bip a b} (hH : X.IsHermitian) :
    Matrix.trace (X * X) = ((rMoment X 1 : ℝ) : ℂ) := by
  rw [HMHB_r1, ← HMHB_normsumC, hH.eq]

lemma HMHB_ev_basis {n a b : ℕ} (p : Perms n) (X : Bip a b) :
    tensorEval (tensorBasis p) X = (tensorTrace p X).re := by
  unfold tensorEval tensorBasis
  simp

lemma HMHB_ev_add {n a b : ℕ} (f g : TensorCoeff n) (X : Bip a b) :
    tensorEval (f + g) X = tensorEval f X + tensorEval g X := by
  unfold tensorEval; simp [add_mul, Finset.sum_add_distrib]

lemma HMHB_ev_sub {n a b : ℕ} (f g : TensorCoeff n) (X : Bip a b) :
    tensorEval (f - g) X = tensorEval f X - tensorEval g X := by
  unfold tensorEval; simp [sub_mul, Finset.sum_sub_distrib]

lemma HMHB_ev_smul {n a b : ℕ} (c : ℝ) (f : TensorCoeff n) (X : Bip a b) :
    tensorEval (c • f) X = c * tensorEval f X := by
  unfold tensorEval; simp [Finset.mul_sum, mul_assoc]

lemma HMHB_smul_mem {n : ℕ} {c : ℝ} (hc : 0 ≤ c) {f : TensorCoeff n} (hf : f ∈ sepCone n) :
    c • f ∈ sepCone n := by
  intro a b ha hb X hX
  rw [HMHB_ev_smul]
  exact mul_nonneg hc (hf a b ha hb X hX)

lemma HMHB_formulas {a b : ℕ} (X : Bip a b) (hH : X.IsHermitian) :
    tensorEval wM X = mass X ^ 4 - (3/2 : ℝ) * mass X ^ 2 * rMoment X 1 + (1/2 : ℝ) * rMoment X 2 ∧
    tensorEval wS X = mass X ^ 4 - 2 * (mass X ^ 2 * rMoment X 1) - rMoment X 1 ^ 2 +
      2 * rMoment X 2 ∧
    tensorEval wRemainder X = 3 * mass X ^ 4 - 4 * (mass X ^ 2 * rMoment X 1) + rMoment X 1 ^ 2 := by
  have h1 : (tensorTrace ((1, 1) : Perms 4) X).re = mass X ^ 4 := by
    rw [HMHB_t1, HMHB_trace_real hH, ← Complex.ofReal_pow, Complex.ofReal_re]
  have h2 : (tensorTrace (s12, s12) X).re = mass X ^ 2 * rMoment X 1 := by
    rw [HMHB_t2, HMHB_trace_real hH, HMHB_trsq hH, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]; ring
  have h3 : (tensorTrace (s12 * s34, s12 * s34) X).re = rMoment X 1 ^ 2 := by
    rw [HMHB_t3, HMHB_trsq hH, ← Complex.ofReal_pow, Complex.ofReal_re]
  have h4 : (tensorTrace (alphaPerm 2, betaPerm 2) X).re = rMoment X 2 := by
    rw [rMoment, powerTrace, HMHB_Frmom X hH]
  refine ⟨?_, ?_, ?_⟩
  · simp only [wM, HMHB_ev_add, HMHB_ev_sub, HMHB_ev_smul, HMHB_ev_basis, h1, h2, h4]; ring
  · simp only [wS, HMHB_ev_add, HMHB_ev_sub, HMHB_ev_smul, HMHB_ev_basis, h1, h2, h3, h4]
  · simp only [wRemainder, HMHB_ev_add, HMHB_ev_sub, HMHB_ev_smul, HMHB_ev_basis, h1, h2, h3]

lemma HMHB_psd {a b : ℕ} (X : Bip a b) (hX : X.PosSemidef) :
    0 ≤ rMoment X 1 ∧ rMoment X 1 ≤ mass X ^ 2 := by
  have hH := hX.1
  refine ⟨by rw [HMHB_r1]; positivity, ?_⟩
  have e1 : rMoment X 1 = ∑ i, hH.eigenvalues i ^ 2 := by
    have h := HMHB_trsq hH
    rw [← sq, HMHB_tr_sq hH] at h
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re] at h'
    rw [← h']
    simp [← Complex.ofReal_pow]
  have e2 : mass X = ∑ i, hH.eigenvalues i := by
    have h := HMHB_trace_real hH
    rw [hH.trace_eq_sum_eigenvalues] at h
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re] at h'
    rw [← h']
    simp
  rw [e1, e2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hX.eigenvalues_nonneg i)

open Matrix WithLp in
lemma HMHB_sepdata {a b : ℕ} (X : Bip a b)
    (hX : QAlgorithms.Entanglement.IsSeparablePositive X) :
    ∃ σ : Fin a × Fin a → ℝ, (∀ i, 0 ≤ σ i) ∧ ∑ i, σ i ≤ mass X ∧
      rMoment X 1 = ∑ i, σ i ^ 2 ∧ rMoment X 2 = ∑ i, (σ i ^ 2) ^ 2 := by
  obtain ⟨q, w, A, B, hw, hAB, hXe⟩ := hX
  set R := realign X with hRdef
  set u : Fin q → Fin a × Fin a → ℂ := fun j i => A j i.1 i.2
  set v : Fin q → Fin b × Fin b → ℂ := fun j k => B j k.1 k.2
  have hR : R = ∑ j, (w j : ℂ) • Matrix.of (fun i k => u j i * v j k) := by
    ext i k
    simp [hRdef, realign, hXe, Matrix.sum_apply, kronecker, kroneckerMap, u, v]
  have hu : ∀ j, ‖(toLp 2 (u j) : EuclideanSpace ℂ (Fin a × Fin a))‖ ≤ 1 := by
    intro j; apply HMHB_euc_norm
    rw [Fintype.sum_prod_type]
    exact HMHB_frob (hAB j).1.1 (hAB j).1.2
  have hv : ∀ j, ‖(toLp 2 (star (v j)) : EuclideanSpace ℂ (Fin b × Fin b))‖ ≤ 1 := by
    intro j; apply HMHB_euc_norm
    rw [Fintype.sum_prod_type]
    simpa [v] using HMHB_frob (hAB j).2.1 (hAB j).2.2
  have hM : (R * Rᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self R
  have hc := HMHB_ccnr w hw u v hu hv R hR hM
  set σ : Fin a × Fin a → ℝ :=
    fun i => ‖(toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ (Fin b × Fin b))‖
  have hσ2 : ∀ i, σ i ^ 2 = hM.eigenvalues i := HMHB_gnorm R hM
  have hr1 : rMoment X 1 = ∑ i, σ i ^ 2 := by
    simp only [hσ2]
    rw [rMoment, powerTrace, pow_one, ← hRdef, hM.trace_eq_sum_eigenvalues]
    simp
  have hr2 : rMoment X 2 = ∑ i, (σ i ^ 2) ^ 2 := by
    simp only [hσ2]
    rw [rMoment, powerTrace, ← hRdef, HMHB_tr_sq hM]
    simp [← Complex.ofReal_pow]
  have hmass : mass X = ∑ j, w j := by
    rw [mass, powerTrace, pow_one, hXe, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [trace_smul, Matrix.kronecker, trace_kronecker, (hAB j).1.2, (hAB j).2.2]
    simp
  exact ⟨σ, fun i => norm_nonneg _, by rw [hmass]; exact hc, hr1, hr2⟩

lemma HMHB_scalarM {ι : Type*} [Fintype ι] (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (t : ℝ) (ht : ∑ i, σ i ≤ t) :
    0 ≤ t ^ 4 - (3/2 : ℝ) * t ^ 2 * ∑ i, σ i ^ 2 + (1/2 : ℝ) * ∑ i, (σ i ^ 2) ^ 2 := by
  have hs0 : 0 ≤ ∑ i, σ i := Finset.sum_nonneg (fun i _ => hσ i)
  have ht0 : 0 ≤ t := hs0.trans ht
  have hle : ∀ i, σ i ≤ t := fun i =>
    (Finset.single_le_sum (fun j _ => hσ j) (Finset.mem_univ i)).trans ht
  have key : ∀ i, (3/2 : ℝ) * t ^ 2 * σ i ^ 2 - (1/2 : ℝ) * (σ i ^ 2) ^ 2 ≤ t ^ 3 * σ i := by
    intro i
    nlinarith [mul_nonneg (mul_nonneg (hσ i) (sq_nonneg (t - σ i)))
      (by linarith [hσ i] : (0:ℝ) ≤ 2 * t + σ i)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  nlinarith [mul_le_mul_of_nonneg_left ht (pow_nonneg ht0 3)]


end QAlgorithms.Papers.Independent.Information100.P19




open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

section HMHD_gen
open Matrix Finset WithLp

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma HMHD_tr_pow {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, ((hA.eigenvalues i : ℂ)) ^ k := by
  have h := hA.spectral_theorem
  conv_lhs => rw [h]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, diagonal_pow, trace_diagonal]
  simp

lemma HMHD_tr_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℂ)) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal]
  simp

omit [DecidableEq m] in
lemma HMHD_gram (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i k : n) :
    inner ℂ (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i))) (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis k)))
      = (hM.eigenvalues k : ℂ) * inner ℂ (hM.eigenvectorBasis i) (hM.eigenvectorBasis k) := by
  rw [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_eq_star_dotProduct, star_mulVec,
    dotProduct_comm, ← dotProduct_mulVec, conjTranspose_conjTranspose, mulVec_mulVec,
    hM.mulVec_eigenvectorBasis, dotProduct_comm]
  rw [smul_dotProduct, Complex.real_smul]

lemma HMHD_gnorm (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i : n) :
    ‖(toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ m)‖ ^ 2 = hM.eigenvalues i := by
  have := HMHD_gram R hM i i
  rw [inner_self_eq_norm_sq_to_K, orthonormal_iff_ite.mp (hM.eigenvectorBasis).orthonormal i i,
    if_pos rfl, mul_one] at this
  have h := congrArg Complex.re this
  simpa [← Complex.ofReal_pow] using h

lemma HMHD_trnorm (M : Matrix n n ℂ) (hM : (Mᴴ * Mᴴᴴ).IsHermitian) :
    QAlgorithms.traceNorm M = ∑ i, ‖(toLp 2 (Mᴴᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ n)‖ := by
  unfold QAlgorithms.traceNorm
  have e : Mᴴ * M = Mᴴ * Mᴴᴴ := by rw [conjTranspose_conjTranspose]
  rw [e, HMHD_tr_cfc hM, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.ofReal_re, ← HMHD_gnorm Mᴴ hM i, Real.sqrt_sq (norm_nonneg _)]

lemma HMHD_powtr (M : Matrix n n ℂ) (hM : (Mᴴ * Mᴴᴴ).IsHermitian) (k : ℕ) :
    ((Mᴴ * M) ^ k).trace.re =
      ∑ i, ‖(toLp 2 (Mᴴᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ n)‖ ^ (2 * k) := by
  have e : Mᴴ * M = Mᴴ * Mᴴᴴ := by rw [conjTranspose_conjTranspose]
  rw [e, HMHD_tr_pow hM, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pow_mul, HMHD_gnorm Mᴴ hM i, ← Complex.ofReal_pow, Complex.ofReal_re]


lemma HMHD_cyc (A : Matrix m n ℂ) (B : Matrix n m ℂ) (k : ℕ) :
    ((A * B) ^ (k + 1)).trace = ((B * A) ^ (k + 1)).trace := by
  have h : ∀ k : ℕ, (A * B) ^ (k + 1) = A * (B * A) ^ k * B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [h, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

lemma HMHD_adj_expand {Q : Type*} [Fintype Q] (w : Q → ℝ) (u : Q → n → ℂ) (v : Q → m → ℂ)
    (R : Matrix n m ℂ) (hR : R = ∑ j, (w j : ℂ) • Matrix.of (fun i k => u j i * v j k))
    (x : n → ℂ) :
    Rᴴ *ᵥ x = ∑ j, ((w j : ℂ) * (x ⬝ᵥ star (u j))) • star (v j) := by
  ext k
  subst hR
  simp only [mulVec, dotProduct, conjTranspose_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.star_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, star_sum,
    star_mul', Complex.star_def, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  ring

lemma HMHD_ccnr {Q : Type*} [Fintype Q] (w : Q → ℝ) (hw : ∀ j, 0 ≤ w j) (u : Q → n → ℂ)
    (v : Q → m → ℂ) (α β : Q → ℝ)
    (hu : ∀ j, ‖(toLp 2 (u j) : EuclideanSpace ℂ n)‖ ≤ α j)
    (hv : ∀ j, ‖(toLp 2 (star (v j)) : EuclideanSpace ℂ m)‖ ≤ β j)
    (R : Matrix n m ℂ) (hR : R = ∑ j, (w j : ℂ) • Matrix.of (fun i k => u j i * v j k))
    (hM : (R * Rᴴ).IsHermitian) :
    ∑ i, ‖(toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ m)‖ ≤
      ∑ j, w j * (α j * β j) := by
  set e := hM.eigenvectorBasis with he
  set g : n → EuclideanSpace ℂ m := fun i => toLp 2 (Rᴴ *ᵥ ⇑(e i)) with hg
  set U : Q → EuclideanSpace ℂ n := fun j => toLp 2 (u j) with hU
  set Vb : Q → EuclideanSpace ℂ m := fun j => toLp 2 (star (v j)) with hVb
  have hgexp : ∀ i, g i = ∑ j, ((w j : ℂ) * inner ℂ (U j) (e i)) • Vb j := by
    intro i
    simp only [hg, hU, hVb]
    rw [HMHD_adj_expand w u v R hR]
    apply (WithLp.equiv 2 _).injective
    ext k
    simp [EuclideanSpace.inner_eq_star_dotProduct]
  have hgg : ∀ i k, inner ℂ (g i) (g k) = (hM.eigenvalues k : ℂ) * inner ℂ (e i) (e k) :=
    HMHD_gram R hM
  have hon := orthonormal_iff_ite.mp e.orthonormal
  have hnorm : ∀ i, ‖g i‖ ^ 2 = hM.eigenvalues i := by
    intro i
    have := hgg i i
    rw [inner_self_eq_norm_sq_to_K, hon i i, if_pos rfl, mul_one] at this
    have h := congrArg Complex.re this
    simpa [← Complex.ofReal_pow] using h
  set s := (univ : Finset n).filter (fun i => hM.eigenvalues i ≠ 0) with hs
  have hpos : ∀ i : s, ‖g i‖ ≠ 0 := by
    intro i h
    have := hnorm i
    rw [h] at this
    exact (Finset.mem_filter.mp i.2).2 (by rw [← this]; ring)
  set f : s → EuclideanSpace ℂ m := fun i => ((‖g i‖ : ℂ)⁻¹) • g i with hf
  have hfon : Orthonormal ℂ f := by
    rw [orthonormal_iff_ite]
    intro i k
    simp only [hf, inner_smul_left, inner_smul_right, hgg, hon]
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl, if_pos rfl, mul_one]
      have h2 : ((hM.eigenvalues i : ℝ) : ℂ) = (‖g i‖ : ℂ) ^ 2 := by
        rw [← hnorm]; push_cast; rfl
      rw [h2]
      have : (‖g i‖ : ℂ) ≠ 0 := by exact_mod_cast hpos i
      simp only [map_inv₀, Complex.conj_ofReal]
      field_simp
    · rw [if_neg (fun h => hik (Subtype.ext h)), if_neg hik]; ring
  have hes : Orthonormal ℂ (fun i : s => e i) :=
    e.orthonormal.comp (fun i : s => (i : n)) Subtype.val_injective
  have hi : ∀ i : s, ‖g i‖ ≤ ∑ j, w j * (‖inner ℂ (e i) (U j)‖ * ‖inner ℂ (f i) (Vb j)‖) := by
    intro i
    have h1 : inner ℂ (f i) (g i) = (‖g i‖ : ℂ) := by
      simp only [hf, inner_smul_left, inner_self_eq_norm_sq_to_K, map_inv₀, Complex.conj_ofReal]
      have : (‖g i‖ : ℂ) ≠ 0 := by exact_mod_cast hpos i
      field_simp
      rfl
    have h2 : ‖g i‖ = ‖inner ℂ (f i) (g i)‖ := by
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [h2, hgexp, inner_sum]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun j _ => ?_)))
    rw [inner_smul_right, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hw j), norm_inner_symm]
    ring
  have hsum : ∑ i, ‖g i‖ = ∑ i : s, ‖g i‖ := by
    rw [Finset.sum_coe_sort s (fun i => ‖g i‖), hs, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with h
    · rfl
    · rw [ne_eq, not_not] at h
      have := hnorm i
      rw [h] at this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  change ∑ i, ‖g i‖ ≤ _
  rw [hsum]
  calc ∑ i : s, ‖g i‖ ≤ ∑ i : s, ∑ j, w j * (‖inner ℂ (e i) (U j)‖ * ‖inner ℂ (f i) (Vb j)‖) :=
        Finset.sum_le_sum (fun i _ => hi i)
    _ = ∑ j, w j * ∑ i : s, ‖inner ℂ (e i) (U j)‖ * ‖inner ℂ (f i) (Vb j)‖ := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ j, w j * (α j * β j) := by
        refine Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left ?_ (hw j))
        refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
        have b1 := hes.sum_inner_products_le (x := U j) (s := univ)
        have b2 := hfon.sum_inner_products_le (x := Vb j) (s := univ)
        have d1 : Real.sqrt (∑ i : s, ‖inner ℂ (e i) (U j)‖ ^ 2) ≤ α j :=
          (Real.sqrt_le_sqrt b1).trans (by rw [Real.sqrt_sq (norm_nonneg _)]; exact hu j)
        have d2 : Real.sqrt (∑ i : s, ‖inner ℂ (f i) (Vb j)‖ ^ 2) ≤ β j :=
          (Real.sqrt_le_sqrt b2).trans (by rw [Real.sqrt_sq (norm_nonneg _)]; exact hv j)
        exact mul_le_mul d1 d2 (Real.sqrt_nonneg _) ((norm_nonneg _).trans (hu j))

end HMHD_gen

section HMHD_sc
open Matrix Finset

lemma HMHD_id {Q : Type*} [Fintype Q] (w : Q → ℝ) (α β : Q → ℂ) :
    ∑ p : Q × Q, ((w p.1 * w p.2 / 2 : ℝ) : ℂ) * ((α p.1 - α p.2) * (β p.1 - β p.2)) =
      (∑ j, (w j : ℂ)) * (∑ j, (w j : ℂ) * (α j * β j)) -
        (∑ j, (w j : ℂ) * α j) * (∑ j, (w j : ℂ) * β j) := by
  rw [Fintype.sum_prod_type]
  have h : ∀ j k, ((w j * w k / 2 : ℝ) : ℂ) * ((α j - α k) * (β j - β k)) =
      (1/2 : ℂ) * (((w j : ℂ) * (α j * β j)) * (w k : ℂ)) +
      (1/2 : ℂ) * ((w j : ℂ) * ((w k : ℂ) * (α k * β k))) -
      (1/2 : ℂ) * (((w j : ℂ) * α j) * ((w k : ℂ) * β k)) -
      (1/2 : ℂ) * (((w j : ℂ) * β j) * ((w k : ℂ) * α k)) := by
    intro j k; push_cast; ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma HMHD_idn {Q : Type*} [Fintype Q] (w : Q → ℝ) (α : Q → ℂ) :
    ∑ p : Q × Q, (w p.1 * w p.2 / 2) * ‖α p.1 - α p.2‖ ^ 2 =
      (∑ j, w j) * (∑ j, w j * ‖α j‖ ^ 2) - ‖∑ j, (w j : ℂ) * α j‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj', map_sub, map_sum, map_mul, Complex.conj_ofReal]
  rw [← HMHD_id]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  push_cast; ring

lemma HMHD_tr_sq {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A ^ 2).trace.re = ∑ i, ∑ k, ‖A i k‖ ^ 2 := by
  have : A ^ 2 = A * Aᴴ := by rw [hA.eq, sq]
  rw [this]
  simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast

lemma HMHD_frob {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htr : A.trace = 1) : ∑ i, ∑ k, ‖A i k‖ ^ 2 ≤ 1 := by
  have hH := hA.1
  rw [← HMHD_tr_sq hH]
  have h := hH.spectral_theorem
  have e : (A ^ 2).trace = ∑ i, ((hH.eigenvalues i : ℂ)) ^ 2 := by
    conv_lhs => rw [h]
    rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
      Matrix.one_mul, diagonal_pow, trace_diagonal]
    simp
  rw [e]
  have hl : ∀ i, 0 ≤ hH.eigenvalues i := hA.eigenvalues_nonneg
  have hs : ∑ i, hH.eigenvalues i = 1 := by
    have := congrArg Complex.re (hH.trace_eq_sum_eigenvalues)
    rw [htr] at this; simpa using this.symm
  have : ∑ i, hH.eigenvalues i ^ 2 ≤ (∑ i, hH.eigenvalues i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hl i)
  rw [hs] at this
  simpa [← Complex.ofReal_pow] using this

end HMHD_sc

namespace QAlgorithms.Papers.Independent.Information100.P19
open Matrix WithLp

lemma HMHD_sq_gram {a b : ℕ} (Y : Bip a b) :
    (realignmentSquare Y)ᴴ * realignmentSquare Y =
      fromBlocks 0 0 0 ((realign Y)ᴴ * realign Y) := by
  simp [realignmentSquare, fromBlocks_conjTranspose, fromBlocks_multiply]

lemma HMHD_fb_pow {a b : ℕ} (D : Matrix (Fin b × Fin b) (Fin b × Fin b) ℂ) (k : ℕ) :
    (fromBlocks (0 : Matrix (Fin a × Fin a) (Fin a × Fin a) ℂ) 0 0 D) ^ (k + 1) =
      fromBlocks 0 0 0 (D ^ (k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, fromBlocks_multiply, pow_succ (n := k + 1)]; simp

lemma HMHD_fb_tr {a b : ℕ} (D : Matrix (Fin b × Fin b) (Fin b × Fin b) ℂ) :
    (fromBlocks (0 : Matrix (Fin a × Fin a) (Fin a × Fin a) ℂ) 0 0 D).trace = D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

lemma HMHD_spec {a b : ℕ} (Y : Bip a b) :
    ∃ σ : (Fin a × Fin a) ⊕ (Fin b × Fin b) → ℝ, (∀ i, 0 ≤ σ i) ∧
      QAlgorithms.traceNorm (realignmentSquare Y) = ∑ i, σ i ∧
      ∀ k : ℕ, rMoment Y (k + 1) = ∑ i, σ i ^ (2 * (k + 1)) := by
  set M := realignmentSquare Y with hMdef
  have hM : (Mᴴ * Mᴴᴴ).IsHermitian := isHermitian_mul_conjTranspose_self Mᴴ
  refine ⟨fun i => ‖(toLp 2 (Mᴴᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ _)‖,
    fun i => norm_nonneg _, HMHD_trnorm M hM, fun k => ?_⟩
  rw [← HMHD_powtr M hM, hMdef, HMHD_sq_gram, HMHD_fb_pow, HMHD_fb_tr, HMHD_cyc]
  rfl

lemma HMHD_bound {a b : ℕ} (Y : Bip a b) {Q : Type*} [Fintype Q] (w : Q → ℝ) (hw : ∀ j, 0 ≤ w j)
    (p : Q → Fin a × Fin a → ℂ) (r : Q → Fin b × Fin b → ℂ)
    (hY : realign Y = ∑ j, (w j : ℂ) • Matrix.of (fun x y => p j x * r j y)) :
    QAlgorithms.traceNorm (realignmentSquare Y) ≤
      ∑ j, w j * (Real.sqrt (∑ x, ‖p j x‖ ^ 2) * Real.sqrt (∑ y, ‖r j y‖ ^ 2)) := by
  set M := realignmentSquare Y with hMdef
  have hM : (Mᴴ * Mᴴᴴ).IsHermitian := isHermitian_mul_conjTranspose_self Mᴴ
  rw [HMHD_trnorm M hM]
  refine le_of_le_of_eq (HMHD_ccnr w hw (fun j => Sum.elim 0 (star (r j)))
    (fun j => Sum.elim (star (p j)) 0)
    (fun j => Real.sqrt (∑ y, ‖r j y‖ ^ 2)) (fun j => Real.sqrt (∑ x, ‖p j x‖ ^ 2))
    (fun j => ?_) (fun j => ?_) Mᴴ ?_ hM) (Finset.sum_congr rfl fun j _ => by ring)
  · simp [EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  · simp [EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  · ext i k
    rcases i with i | i <;> rcases k with k | k <;>
      simp [hMdef, realignmentSquare, hY, Matrix.sum_apply, mul_comm]

lemma HMHD_rsmul {a b : ℕ} (Y : Bip a b) (t : ℝ) (k : ℕ) :
    rMoment ((t : ℂ) • Y) k = (t ^ 2) ^ k * rMoment Y k := by
  have e : realign ((t : ℂ) • Y) = (t : ℂ) • realign Y := by ext i j; simp [realign]
  have e2 : realign ((t : ℂ) • Y) * (realign ((t : ℂ) • Y))ᴴ =
      ((t ^ 2 : ℝ) : ℂ) • (realign Y * (realign Y)ᴴ) := by
    rw [e, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    simp [Complex.conj_ofReal, sq]
  rw [rMoment, powerTrace, e2, smul_pow, trace_smul, ← Complex.ofReal_pow, smul_eq_mul,
    Complex.re_ofReal_mul]
  rfl

lemma HMHD_alpha {a b : ℕ} (Y : Bip a b) (m : ℕ) (c : ℝ) (hc : 0 < c)
    (hle : QAlgorithms.traceNorm (realignmentSquare Y) ≤ c) :
    alpha (fun k : Fin m => rMoment (((c : ℂ))⁻¹ • Y) (k.val + 1)) ≤
      ENNReal.ofReal (QAlgorithms.traceNorm (realignmentSquare Y) / c) := by
  obtain ⟨σ, hσ0, htn, hmom⟩ := HMHD_spec Y
  set e := Fintype.equivFin ((Fin a × Fin a) ⊕ (Fin b × Fin b))
  apply sInf_le
  refine ⟨_, fun t => σ (e.symm t) / c, ⟨fun i => ⟨div_nonneg (hσ0 _) hc.le, ?_⟩, fun k => ?_⟩, ?_⟩
  · rw [div_le_one hc]
    exact (Finset.single_le_sum (fun j _ => hσ0 j) (Finset.mem_univ _)).trans (htn ▸ hle)
  · simp only []
    rw [← Complex.ofReal_inv, HMHD_rsmul, hmom, e.symm.sum_comp (fun i => (σ i / c) ^ (2 * (k.val + 1))),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_pow, ← pow_mul, div_eq_mul_inv, mul_comm, inv_pow]
  · rw [e.symm.sum_comp (fun i => σ i / c), ← Finset.sum_div, htn]

section HMHD_S
variable {a b q : ℕ} (w : Fin q → ℝ) (A : Fin q → Matrix (Fin a) (Fin a) ℂ)
  (B : Fin q → Matrix (Fin b) (Fin b) ℂ)
  (hAB : ∀ j, QAlgorithms.IsDensityMatrix (A j) ∧ QAlgorithms.IsDensityMatrix (B j))

include hAB in
lemma HMHD_mass : mass (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) = ∑ j, w j := by
  rw [mass, powerTrace, pow_one, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [trace_smul, Matrix.kronecker, trace_kronecker, (hAB j).1.2, (hAB j).2.2]
  simp

include hAB in
lemma HMHD_margA : marginalA (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
    ∑ j, (w j : ℂ) • A j := by
  ext i i'
  have h : ∀ j, ∑ k, B j k k = 1 := fun j => (hAB j).2.2
  simp only [marginalA, Matrix.sum_apply, Matrix.smul_apply, kronecker, kroneckerMap_apply,
    smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.mul_sum, ← Finset.mul_sum, h, mul_one]

include hAB in
lemma HMHD_margB : marginalB (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
    ∑ j, (w j : ℂ) • B j := by
  ext i i'
  have h : ∀ j, ∑ k, A j k k = 1 := fun j => (hAB j).1.2
  simp only [marginalB, Matrix.sum_apply, Matrix.smul_apply, kronecker, kroneckerMap_apply,
    smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.mul_sum, ← Finset.sum_mul, h, one_mul]

lemma HMHD_real : realign (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
    ∑ j, (w j : ℂ) • Matrix.of (fun x y => A j x.1 x.2 * B j y.1 y.2) := by
  ext x y
  simp [realign, Matrix.sum_apply, kronecker]

include hAB in
lemma HMHD_realc : realign (centered (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j))) =
    ∑ p : Fin q × Fin q, ((w p.1 * w p.2 / 2 : ℝ) : ℂ) •
      Matrix.of (fun x y => (A p.1 x.1 x.2 - A p.2 x.1 x.2) * (B p.1 y.1 y.2 - B p.2 y.1 y.2)) := by
  ext x y
  rw [centered, HMHD_margA w A B hAB, HMHD_margB w A B hAB, HMHD_mass w A B hAB]
  simp only [realign, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply,
    smul_eq_mul, kronecker, kroneckerMap_apply]
  have := HMHD_id w (fun j => A j x.1 x.2) (fun j => B j y.1 y.2)
  rw [this]
  push_cast
  ring

include hAB in
lemma HMHD_purA : purityA (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
    ∑ x : Fin a × Fin a, ‖∑ j, (w j : ℂ) * A j x.1 x.2‖ ^ 2 := by
  rw [purityA, powerTrace, HMHD_margA w A B hAB, HMHD_tr_sq, Fintype.sum_prod_type]
  · simp [Matrix.sum_apply]
  · unfold Matrix.IsHermitian
    rw [conjTranspose_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [conjTranspose_smul, (hAB j).1.1.1.eq]
    simp

include hAB in
lemma HMHD_purB : purityB (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
    ∑ y : Fin b × Fin b, ‖∑ j, (w j : ℂ) * B j y.1 y.2‖ ^ 2 := by
  rw [purityB, powerTrace, HMHD_margB w A B hAB, HMHD_tr_sq, Fintype.sum_prod_type]
  · simp [Matrix.sum_apply]
  · unfold Matrix.IsHermitian
    rw [conjTranspose_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [conjTranspose_smul, (hAB j).2.1.1.eq]
    simp

omit hAB in
lemma HMHD_SA {d : ℕ} (C : Fin q → Matrix (Fin d) (Fin d) ℂ)
    (hC : ∀ j, QAlgorithms.IsDensityMatrix (C j)) (hw : ∀ j, 0 ≤ w j) :
    ∑ p : Fin q × Fin q, (w p.1 * w p.2 / 2) * ∑ x : Fin d × Fin d, ‖C p.1 x.1 x.2 - C p.2 x.1 x.2‖ ^ 2
      ≤ (∑ j, w j) ^ 2 - ∑ x : Fin d × Fin d, ‖∑ j, (w j : ℂ) * C j x.1 x.2‖ ^ 2 := by
  have e : ∑ p : Fin q × Fin q, (w p.1 * w p.2 / 2) *
      ∑ x : Fin d × Fin d, ‖C p.1 x.1 x.2 - C p.2 x.1 x.2‖ ^ 2 =
      (∑ j, w j) * (∑ j, w j * ∑ x : Fin d × Fin d, ‖C j x.1 x.2‖ ^ 2) -
        ∑ x : Fin d × Fin d, ‖∑ j, (w j : ℂ) * C j x.1 x.2‖ ^ 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have := fun x : Fin d × Fin d => HMHD_idn w (fun j => C j x.1 x.2)
    simp only [Finset.mul_sum] at this
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
  rw [e]
  have hF : ∀ j, ∑ x : Fin d × Fin d, ‖C j x.1 x.2‖ ^ 2 ≤ 1 := fun j => by
    rw [Fintype.sum_prod_type]; exact HMHD_frob (hC j).1 (hC j).2
  have h1 : ∑ j, w j * ∑ x : Fin d × Fin d, ‖C j x.1 x.2‖ ^ 2 ≤ ∑ j, w j :=
    Finset.sum_le_sum (fun j _ => by
      have := mul_le_mul_of_nonneg_left (hF j) (hw j); linarith)
  have h0 : 0 ≤ ∑ j, w j := Finset.sum_nonneg (fun j _ => hw j)
  have := mul_le_mul_of_nonneg_left h1 h0
  nlinarith

include hAB in
lemma HMHD_p3 (hw : ∀ j, 0 ≤ w j) :
    QAlgorithms.traceNorm (realignmentSquare (centered (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j))))
      ≤ Real.sqrt (G (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j))) := by
  set c : Fin q × Fin q → ℝ := fun p => w p.1 * w p.2 / 2 with hc
  have hc0 : ∀ p, 0 ≤ c p := fun p => by
    simp only [hc]; have := mul_nonneg (hw p.1) (hw p.2); linarith
  have hb := HMHD_bound _ c hc0 (fun p x => A p.1 x.1 x.2 - A p.2 x.1 x.2)
    (fun p y => B p.1 y.1 y.2 - B p.2 y.1 y.2) (HMHD_realc w A B hAB)
  set FA : Fin q × Fin q → ℝ := fun p => ∑ x : Fin a × Fin a, ‖A p.1 x.1 x.2 - A p.2 x.1 x.2‖ ^ 2
  set FB : Fin q × Fin q → ℝ := fun p => ∑ y : Fin b × Fin b, ‖B p.1 y.1 y.2 - B p.2 y.1 y.2‖ ^ 2
  have hSA := HMHD_SA w (fun j => A j) (fun j => (hAB j).1) hw
  have hSB := HMHD_SA w (fun j => B j) (fun j => (hAB j).2) hw
  have hFA : ∀ p, 0 ≤ FA p := fun p => Finset.sum_nonneg (fun _ _ => by positivity)
  have hFB : ∀ p, 0 ≤ FB p := fun p => Finset.sum_nonneg (fun _ _ => by positivity)
  have hcs : ∑ p, c p * (Real.sqrt (FA p) * Real.sqrt (FB p)) ≤
      Real.sqrt (∑ p, c p * FA p) * Real.sqrt (∑ p, c p * FB p) := by
    have e : ∀ p, c p * (Real.sqrt (FA p) * Real.sqrt (FB p)) =
        Real.sqrt (c p * FA p) * Real.sqrt (c p * FB p) := fun p => by
      rw [Real.sqrt_mul (hc0 p), Real.sqrt_mul (hc0 p)]
      have := Real.mul_self_sqrt (hc0 p)
      calc _ = (Real.sqrt (c p) * Real.sqrt (c p)) * (Real.sqrt (FA p) * Real.sqrt (FB p)) := by
            rw [this]
        _ = _ := by ring
    rw [Finset.sum_congr rfl (fun p _ => e p)]
    refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans (le_of_eq ?_)
    congr 2 <;> refine Finset.sum_congr rfl (fun p _ => Real.sq_sqrt (mul_nonneg (hc0 p) ?_))
    exacts [hFA p, hFB p]
  have hA0 : 0 ≤ ∑ p, c p * FA p := Finset.sum_nonneg (fun p _ => mul_nonneg (hc0 p) (hFA p))
  have hB0 : 0 ≤ ∑ p, c p * FB p := Finset.sum_nonneg (fun p _ => mul_nonneg (hc0 p) (hFB p))
  rw [G, HMHD_mass w A B hAB, HMHD_purA w A B hAB, HMHD_purB w A B hAB]
  refine hb.trans (hcs.trans ?_)
  rw [Real.sqrt_mul (hA0.trans hSA)]
  exact mul_le_mul (Real.sqrt_le_sqrt hSA) (Real.sqrt_le_sqrt hSB) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

include hAB in
lemma HMHD_p2 (hw : ∀ j, 0 ≤ w j) :
    QAlgorithms.traceNorm (realignmentSquare (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)))
      ≤ mass (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) := by
  refine (HMHD_bound _ w hw (fun j x => A j x.1 x.2) (fun j y => B j y.1 y.2)
    (HMHD_real w A B)).trans ?_
  rw [HMHD_mass w A B hAB]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hA : Real.sqrt (∑ x : Fin a × Fin a, ‖A j x.1 x.2‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by
    rw [Fintype.sum_prod_type]; exact HMHD_frob (hAB j).1.1 (hAB j).1.2)
  have hB : Real.sqrt (∑ y : Fin b × Fin b, ‖B j y.1 y.2‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by
    rw [Fintype.sum_prod_type]; exact HMHD_frob (hAB j).2.1 (hAB j).2.2)
  have := mul_le_mul hA hB (Real.sqrt_nonneg _) zero_le_one
  have := mul_le_mul_of_nonneg_left this (hw j)
  simpa using this

end HMHD_S

end QAlgorithms.Papers.Independent.Information100.P19


namespace HMH
open QAlgorithms.Papers.Independent.Information100.P19
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

theorem cs1 {ι : Type*} [Fintype ι] (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    (∑ i, σ i ^ 2) ^ 2 ≤ (∑ i, σ i) * ∑ i, σ i ^ 3 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (σ i))
    (fun i => Real.sqrt (σ i) * σ i)
  have e1 : ∀ i, Real.sqrt (σ i) * (Real.sqrt (σ i) * σ i) = σ i ^ 2 := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (hσ i)]; ring
  have e2 : ∀ i, Real.sqrt (σ i) ^ 2 = σ i := fun i => Real.sq_sqrt (hσ i)
  have e3 : ∀ i, (Real.sqrt (σ i) * σ i) ^ 2 = σ i ^ 3 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hσ i)]; ring
  simp only [e1, e2, e3] at h
  exact h

theorem cs2 {ι : Type*} [Fintype ι] (σ : ι → ℝ) :
    (∑ i, σ i ^ 3) ^ 2 ≤ (∑ i, σ i ^ 2) * ∑ i, (σ i ^ 2) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => σ i) (fun i => σ i ^ 2)
  have e1 : ∀ i, σ i * σ i ^ 2 = σ i ^ 3 := fun i => by ring
  simp only [e1] at h
  exact h

theorem S1 {ι : Type*} [Fintype ι] (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i) (c : ℝ)
    (hs : ∑ i, σ i ≤ c) :
    (∑ i, σ i ^ 2) ^ 3 ≤ (∑ i, (σ i ^ 2) ^ 2) * c ^ 2 := by
  have h1 := cs1 σ hσ
  have h2 := cs2 σ
  have s0 : 0 ≤ ∑ i, σ i := Finset.sum_nonneg fun i _ => hσ i
  have s2 : 0 ≤ ∑ i, σ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have s3 : 0 ≤ ∑ i, σ i ^ 3 := Finset.sum_nonneg fun i _ => pow_nonneg (hσ i) 3
  have s4 : 0 ≤ ∑ i, (σ i ^ 2) ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  set A := ∑ i, σ i; set B := ∑ i, σ i ^ 2; set C := ∑ i, σ i ^ 3; set D := ∑ i, (σ i ^ 2) ^ 2
  have hAc : A ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ s0 hs 2
  have h4 : B ^ 4 ≤ A ^ 2 * (B * D) := by
    calc B ^ 4 = (B ^ 2) ^ 2 := by ring
      _ ≤ (A * C) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
      _ = A ^ 2 * C ^ 2 := by ring
      _ ≤ A ^ 2 * (B * D) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  rcases eq_or_lt_of_le s2 with hB | hB
  · rw [← hB]; simp; positivity
  · have h3 : B ^ 3 ≤ A ^ 2 * D := by
      have : B * B ^ 3 ≤ B * (A ^ 2 * D) := by nlinarith
      exact le_of_mul_le_mul_left this hB
    calc B ^ 3 ≤ A ^ 2 * D := h3
      _ ≤ c ^ 2 * D := mul_le_mul_of_nonneg_right hAc s4
      _ = D * c ^ 2 := by ring

theorem S2 {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i) (c : ℝ)
    (hs : ∑ i, σ i ≤ c) :
    (∑ i, σ i ^ 2) ^ 2 + 2 * c ^ 2 * ∑ i, σ i ^ 2 ≤ 2 * ∑ i, (σ i ^ 2) ^ 2 + c ^ 4 := by
  have := HMHB_scalar σ hσ c hs
  nlinarith

theorem S3 {ι : Type*} [Fintype ι] (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i) (c : ℝ)
    (hs : ∑ i, σ i ≤ c) : ∑ i, σ i ^ 2 ≤ c ^ 2 := by
  have s0 : 0 ≤ ∑ i, σ i := Finset.sum_nonneg fun i _ => hσ i
  exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hσ i)).trans (pow_le_pow_left₀ s0 hs 2)

theorem S5 {ι : Type*} [Fintype ι] (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i) (c : ℝ) (hc : 0 ≤ c)
    (hs : ∑ i, σ i ≤ c) (m : ℕ) (hm : 1 ≤ m) (p : Fin m → ℝ)
    (hp : ∀ x ∈ Set.Icc (0:ℝ) 1, polynomialEval p x ≤ Real.sqrt x) :
    ∑ k : Fin m, p k * (∑ i, σ i ^ (2 * (k.val + 1))) * (c ^ 2) ^ (m - (k.val + 1)) ≤
      (c ^ 2) ^ m := by
  have hle : ∀ i, σ i ≤ c := fun i =>
    (Finset.single_le_sum (fun j _ => hσ j) (Finset.mem_univ i)).trans hs
  rcases eq_or_lt_of_le hc with h0 | hpos
  · subst h0
    have hz : ∀ i, σ i = 0 := fun i => le_antisymm (hle i) (hσ i)
    simp [hz]
  · set y : ι → ℝ := fun i => (σ i / c) ^ 2
    have hy : ∀ i, y i ∈ Set.Icc (0:ℝ) 1 := fun i => by
      refine ⟨sq_nonneg _, ?_⟩
      have : σ i / c ≤ 1 := (div_le_one hpos).mpr (hle i)
      have : 0 ≤ σ i / c := div_nonneg (hσ i) hc
      nlinarith
    have key : ∀ k : Fin m, ∀ i, σ i ^ (2 * (k.val + 1)) * (c ^ 2) ^ (m - (k.val + 1)) =
        (c ^ 2) ^ m * y i ^ (k.val + 1) := by
      intro k i
      have hk : k.val + 1 ≤ m := k.isLt
      rw [show (c ^ 2) ^ m = (c ^ 2) ^ (k.val + 1) * (c ^ 2) ^ (m - (k.val + 1)) by
        rw [← pow_add]; congr 1; omega]
      simp only [y]
      have hc2 : c ^ 2 ≠ 0 := by positivity
      rw [pow_mul, div_pow]
      calc (σ i ^ 2) ^ (k.val + 1) * (c ^ 2) ^ (m - (k.val + 1))
          = (c ^ 2 * (σ i ^ 2 / c ^ 2)) ^ (k.val + 1) * (c ^ 2) ^ (m - (k.val + 1)) := by
            rw [mul_div_cancel₀ _ hc2]
        _ = _ := by rw [mul_pow]; ring
    have hsq : ∀ i, Real.sqrt (y i) = σ i / c := fun i => Real.sqrt_sq (div_nonneg (hσ i) hc)
    calc ∑ k : Fin m, p k * (∑ i, σ i ^ (2 * (k.val + 1))) * (c ^ 2) ^ (m - (k.val + 1))
        = (c ^ 2) ^ m * ∑ i, polynomialEval p (y i) := by
          unfold polynomialEval
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
          rw [mul_assoc, key]; ring
      _ ≤ (c ^ 2) ^ m * ∑ i, Real.sqrt (y i) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hp _ (hy i)) (by positivity)
      _ = (c ^ 2) ^ m * ((∑ i, σ i) / c) := by simp_rw [hsq, Finset.sum_div]
      _ ≤ (c ^ 2) ^ m * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hpos).mpr hs) (by positivity)
      _ = (c ^ 2) ^ m := mul_one _

theorem atomsX {a b : ℕ} (X : Bip a b) (hX : QAlgorithms.Entanglement.IsSeparablePositive X) :
    ∃ σ : (Fin a × Fin a) ⊕ (Fin b × Fin b) → ℝ, (∀ i, 0 ≤ σ i) ∧ ∑ i, σ i ≤ mass X ∧
      ∀ k : ℕ, rMoment X (k + 1) = ∑ i, σ i ^ (2 * (k + 1)) := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := hX
  obtain ⟨σ, h0, htn, hm⟩ := HMHD_spec (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j))
  exact ⟨σ, h0, htn ▸ HMHD_p2 w A B hAB hw, hm⟩

theorem atomsC {a b : ℕ} (X : Bip a b) (hX : QAlgorithms.Entanglement.IsSeparablePositive X) :
    ∃ σ : (Fin a × Fin a) ⊕ (Fin b × Fin b) → ℝ, (∀ i, 0 ≤ σ i) ∧ ∑ i, σ i ≤ Real.sqrt (G X) ∧
      ∀ k : ℕ, rMoment (centered X) (k + 1) = ∑ i, σ i ^ (2 * (k + 1)) := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := hX
  obtain ⟨σ, h0, htn, hm⟩ := HMHD_spec (centered (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)))
  exact ⟨σ, h0, htn ▸ HMHD_p3 w A B hAB hw, hm⟩

theorem G_nonneg {a b : ℕ} (X : Bip a b) (hX : QAlgorithms.Entanglement.IsSeparablePositive X) :
    0 ≤ G X := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := hX
  rw [G, HMHD_mass w A B hAB, HMHD_purA w A B hAB, HMHD_purB w A B hAB]
  have hSA := HMHD_SA w (fun j => A j) (fun j => (hAB j).1) hw
  have hSB := HMHD_SA w (fun j => B j) (fun j => (hAB j).2) hw
  have n1 : 0 ≤ ∑ p : Fin q × Fin q, (w p.1 * w p.2 / 2) *
      ∑ x : Fin a × Fin a, ‖A p.1 x.1 x.2 - A p.2 x.1 x.2‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => mul_nonneg (div_nonneg (mul_nonneg (hw _) (hw _)) two_pos.le)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have n2 : 0 ≤ ∑ p : Fin q × Fin q, (w p.1 * w p.2 / 2) *
      ∑ x : Fin b × Fin b, ‖B p.1 x.1 x.2 - B p.2 x.1 x.2‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => mul_nonneg (div_nonneg (mul_nonneg (hw _) (hw _)) two_pos.le)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact mul_nonneg (n1.trans hSA) (n2.trans hSB)

theorem sep_part {a b : ℕ} (X : Bip a b) (hX : QAlgorithms.Entanglement.IsSeparablePositive X) :
      rMoment X 1^3 ≤ rMoment X 2*mass X^2 ∧
      rMoment X 1^2+2*mass X^2*rMoment X 1 ≤ 2*rMoment X 2+mass X^4 ∧
      rMoment X 1 ≤ mass X^2 ∧
      (3/2 : ℝ)*rMoment X 1*mass X^2-(1/2 : ℝ)*rMoment X 2 ≤ mass X^4 ∧
      rMoment (centered X) 1^3 ≤ rMoment (centered X) 2*G X ∧
      rMoment (centered X) 1^2+2*G X*rMoment (centered X) 1 ≤
        2*rMoment (centered X) 2+G X^2 ∧
      ∀ m : ℕ, 1 ≤ m → ∀ p : Fin m → ℝ,
        (∀ x ∈ Set.Icc (0:ℝ) 1, polynomialEval p x ≤ Real.sqrt x) →
        (∑ k, p k*rMoment X (k.val+1)*mass X^(2*(m-(k.val+1)))) ≤ mass X^(2*m) ∧
        (∑ k, p k*rMoment (centered X) (k.val+1)*G X^(m-(k.val+1))) ≤ G X^m := by
  obtain ⟨σ, hσ, hs, hmom⟩ := atomsX X hX
  obtain ⟨τ, hτ, ht, hmomc⟩ := atomsC X hX
  have hG := G_nonneg X hX
  have hT : 0 ≤ mass X := (Finset.sum_nonneg fun i _ => hσ i).trans hs
  have r1 : rMoment X 1 = ∑ i, σ i ^ 2 := by simpa using hmom 0
  have r2 : rMoment X 2 = ∑ i, (σ i ^ 2) ^ 2 := by
    rw [hmom 1]; exact Finset.sum_congr rfl fun i _ => by ring
  have c1 : rMoment (centered X) 1 = ∑ i, τ i ^ 2 := by simpa using hmomc 0
  have c2 : rMoment (centered X) 2 = ∑ i, (τ i ^ 2) ^ 2 := by
    rw [hmomc 1]; exact Finset.sum_congr rfl fun i _ => by ring
  have hcG : Real.sqrt (G X) ^ 2 = G X := Real.sq_sqrt hG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r1, r2]; exact S1 σ hσ _ hs
  · rw [r1, r2]; exact S2 σ hσ _ hs
  · rw [r1]; exact S3 σ hσ _ hs
  · rw [r1, r2]; have := HMHB_scalarM σ hσ _ hs; linarith
  · rw [c1, c2, ← hcG]; exact S1 τ hτ _ ht
  · rw [c1, c2, ← hcG]; have := S2 τ hτ _ ht; nlinarith
  · intro m hm p hp
    constructor
    · calc (∑ k : Fin m, p k * rMoment X (k.val+1) * mass X ^ (2 * (m - (k.val+1))))
          = ∑ k : Fin m, p k * (∑ i, σ i ^ (2 * (k.val + 1))) * (mass X ^ 2) ^ (m - (k.val + 1)) :=
            Finset.sum_congr rfl fun k _ => by rw [hmom, ← pow_mul]
        _ ≤ (mass X ^ 2) ^ m := S5 σ hσ _ hT hs m hm p hp
        _ = mass X ^ (2 * m) := by rw [pow_mul]
    · calc (∑ k : Fin m, p k * rMoment (centered X) (k.val+1) * G X ^ (m - (k.val+1)))
          = ∑ k : Fin m, p k * (∑ i, τ i ^ (2 * (k.val + 1))) *
              (Real.sqrt (G X) ^ 2) ^ (m - (k.val + 1)) :=
            Finset.sum_congr rfl fun k _ => by rw [hmomc, hcG]
        _ ≤ (Real.sqrt (G X) ^ 2) ^ m := S5 τ hτ _ (Real.sqrt_nonneg _) ht m hm p hp
        _ = G X ^ m := by rw [hcG]

def X1 : Bip 2 2 := Matrix.of fun p q => if p = (0, 0) ∧ q = (0, 0) then (1 : ℂ) else 0
def X2 : Bip 2 2 := Matrix.of fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (1/2 : ℂ) else 0

theorem X1_vals : mass X1 = 1 ∧ rMoment X1 1 = 1 ∧ rMoment X1 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [mass, rMoment, powerTrace, sq, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    realign, Fintype.sum_prod_type, Fin.sum_univ_two, X1]

theorem X2_vals : mass X2 = 1 ∧ rMoment X2 1 = 1 ∧ rMoment X2 2 = 1/4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [mass, rMoment, powerTrace, sq, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    realign, Fintype.sum_prod_type, Fin.sum_univ_two, X2] <;> norm_num

def F {α M : Type*} [Fintype α] [DecidableEq α] [Fintype M] [DecidableEq M]
    (Y : Matrix M M ℂ) (σ : Equiv.Perm α) : ℂ :=
  ∑ κ : α → M, ∏ r, Y (κ r) (κ (σ r))

theorem tt_diag {n a b : ℕ} (Y : Bip a b) (σ : Equiv.Perm (Fin n)) :
    tensorTrace (σ, σ) Y = F Y σ := by
  unfold tensorTrace F
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin a) (fun _ => Fin b)).symm.sum_comp,
    Fintype.sum_prod_type]
  rfl

theorem eval_embed {n a b : ℕ} (ppt : Bool) (f : Coeff n) (X : Bip a b) :
    tensorEval (embed ppt f) X = f.sum (fun l c => c *
      (tensorTrace (canonicalPerm l, if ppt then (canonicalPerm l)⁻¹ else canonicalPerm l) X).re) := by
  unfold tensorEval embed Finsupp.sum
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [ite_mul]

theorem F_rank1 {α M : Type*} [Fintype α] [DecidableEq α] [Fintype M] [DecidableEq M]
    (Y : Matrix M M ℂ) (v : M → ℝ) (hY : ∀ p q, Y p q = ((v p * v q : ℝ) : ℂ))
    (hv : ∑ x, v x ^ 2 = 1) (σ : Equiv.Perm α) : F Y σ = 1 := by
  unfold F
  have h : ∀ κ : α → M, ∏ r, Y (κ r) (κ (σ r)) = ((∏ r, v (κ r) ^ 2 : ℝ) : ℂ) := by
    intro κ
    simp only [hY]
    rw [← Complex.ofReal_prod, Finset.prod_mul_distrib, Equiv.prod_comp σ (fun r => v (κ r)),
      ← Finset.prod_mul_distrib]
    simp [sq]
  simp_rw [h]
  rw [← Complex.ofReal_sum, ← Fintype.prod_sum (fun (_ : α) (x : M) => v x ^ 2), hv]
  simp

theorem eval_rank1 {n a b : ℕ} (f : Coeff n) (Y : Bip a b) (v : Fin a × Fin b → ℝ)
    (hY : ∀ p q, Y p q = ((v p * v q : ℝ) : ℂ)) (hv : ∑ x, v x ^ 2 = 1) :
    tensorEval (embed false f) Y = f.sum (fun _ c => c) := by
  rw [eval_embed]
  simp only [Bool.false_eq_true, if_false, tt_diag, F_rank1 Y v hY hv, Complex.one_re, mul_one]

theorem X1_r1 : ∀ p q, X1 p q = (((if p = (0, 0) then (1:ℝ) else 0) *
    (if q = (0, 0) then (1:ℝ) else 0) : ℝ) : ℂ) := by
  intro p q; simp only [X1, Matrix.of_apply]; split_ifs <;> simp_all

theorem X2_r1 : ∀ p q, X2 p q = (((if p.1 = p.2 then Real.sqrt 2 / 2 else 0) *
    (if q.1 = q.2 then Real.sqrt 2 / 2 else 0) : ℝ) : ℂ) := by
  intro p q
  have h : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num
  simp only [X2, Matrix.of_apply]; split_ifs <;> simp_all

theorem v1_norm : ∑ x : Fin 2 × Fin 2, (if x = (0, 0) then (1:ℝ) else 0) ^ 2 = 1 := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_two]

theorem v2_norm : ∑ x : Fin 2 × Fin 2, (if x.1 = x.2 then Real.sqrt 2 / 2 else 0) ^ 2 = 1 := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, div_pow]
  norm_num

theorem X1_herm : X1.IsHermitian := by
  ext p q; simp only [Matrix.conjTranspose_apply, X1, Matrix.of_apply]; split_ifs <;> simp_all

theorem X2_herm : X2.IsHermitian := by
  ext p q; simp only [Matrix.conjTranspose_apply, X2, Matrix.of_apply]; split_ifs <;> simp_all

theorem nonexist : ¬ (∃ f ∈ psdCone 4, ∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.IsHermitian →
      tensorEval (embed false f) X = tensorEval wM X) := by
  rintro ⟨f, -, hf⟩
  have h1 := hf 2 2 (by norm_num) (by norm_num) X1 X1_herm
  have h2 := hf 2 2 (by norm_num) (by norm_num) X2 X2_herm
  rw [eval_rank1 f X1 _ X1_r1 v1_norm, (HMHB_formulas X1 X1_herm).1] at h1
  rw [eval_rank1 f X2 _ X2_r1 v2_norm, (HMHB_formulas X2 X2_herm).1] at h2
  obtain ⟨a1, b1, c1⟩ := X1_vals
  obtain ⟨a2, b2, c2⟩ := X2_vals
  rw [a1, b1, c1] at h1
  rw [a2, b2, c2] at h2
  rw [h1] at h2
  norm_num at h2

theorem b_mem : b11 - b2 ∈ psdCone 2 := by
  intro d hd x hx
  unfold pairing
  rw [Finsupp.sum_sub_index (fun _ _ _ => by ring)]
  simp only [b11, b2, bracket]
  erw [Finsupp.sum_single_index (by ring), Finsupp.sum_single_index (by ring)]
  simp only [spectralMoments, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, pow_one,
    mul_one, one_mul]
  have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => hx i)
  nlinarith

theorem wM_mem : wM ∈ sepCone 4 := by
  intro a b _ _ X hX
  rw [(HMHB_formulas X (HMHB_Fsep_psd hX).1).1]
  obtain ⟨σ, hσ, hs, hmom⟩ := atomsX X hX
  have r1 : rMoment X 1 = ∑ i, σ i ^ 2 := by simpa using hmom 0
  have r2 : rMoment X 2 = ∑ i, (σ i ^ 2) ^ 2 := by
    rw [hmom 1]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [r1, r2]
  exact HMHB_scalarM σ hσ _ hs

end HMH

end

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution  :
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b,
      QAlgorithms.Entanglement.IsSeparablePositive X →
      rMoment X 1^3 ≤ rMoment X 2*mass X^2 ∧
      rMoment X 1^2+2*mass X^2*rMoment X 1 ≤ 2*rMoment X 2+mass X^4 ∧
      rMoment X 1 ≤ mass X^2 ∧
      (3/2 : ℝ)*rMoment X 1*mass X^2-(1/2 : ℝ)*rMoment X 2 ≤ mass X^4 ∧
      rMoment (centered X) 1^3 ≤ rMoment (centered X) 2*G X ∧
      rMoment (centered X) 1^2+2*G X*rMoment (centered X) 1 ≤
        2*rMoment (centered X) 2+G X^2 ∧
      ∀ m : ℕ, 1 ≤ m → ∀ p : Fin m → ℝ,
        (∀ x ∈ Set.Icc (0:ℝ) 1, polynomialEval p x ≤ Real.sqrt x) →
        (∑ k, p k*rMoment X (k.val+1)*mass X^(2*(m-(k.val+1)))) ≤ mass X^(2*m) ∧
        (∑ k, p k*rMoment (centered X) (k.val+1)*G X^(m-(k.val+1))) ≤ G X^m) ∧
    b11-b2 ∈ psdCone 2 ∧ wM ∈ sepCone 4 ∧
    ¬ (∃ f ∈ psdCone 4, ∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.IsHermitian →
      tensorEval (embed false f) X = tensorEval wM X) :=
  ⟨fun _ _ _ _ X hX => HMH.sep_part X hX, HMH.b_mem, HMH.wM_mem, HMH.nonexist⟩

