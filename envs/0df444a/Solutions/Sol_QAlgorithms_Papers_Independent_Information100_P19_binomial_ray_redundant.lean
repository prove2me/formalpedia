-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.binomial_ray_redundant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:28:32.393985+00:00
-- url     : https://prove2.me/submissions/2c5bee2c-7b10-49cf-9ab2-345190636571

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

section BRR_PS
open Matrix Finset WithLp

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma BRR_tr_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A ^ 2).trace = ∑ i, ((hA.eigenvalues i : ℂ)) ^ 2 := by
  have h := hA.spectral_theorem
  conv_lhs => rw [h]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, diagonal_pow, trace_diagonal]
  simp

lemma BRR_adj_expand {q : ℕ} (w : Fin q → ℝ) (u : Fin q → n → ℂ) (v : Fin q → m → ℂ)
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

lemma BRR_gram (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i k : n) :
    inner ℂ (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i))) (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis k)))
      = (hM.eigenvalues k : ℂ) * inner ℂ (hM.eigenvectorBasis i) (hM.eigenvectorBasis k) := by
  rw [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_eq_star_dotProduct, star_mulVec,
    dotProduct_comm, ← dotProduct_mulVec, conjTranspose_conjTranspose, mulVec_mulVec,
    hM.mulVec_eigenvectorBasis, dotProduct_comm]
  rw [smul_dotProduct, Complex.real_smul]

lemma BRR_ccnr {q : ℕ} (w : Fin q → ℝ) (hw : ∀ j, 0 ≤ w j) (u : Fin q → n → ℂ)
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
    rw [BRR_adj_expand w u v R hR]
    apply (WithLp.equiv 2 _).injective
    ext k
    simp [EuclideanSpace.inner_eq_star_dotProduct]
  have hgg : ∀ i k, inner ℂ (g i) (g k) = (hM.eigenvalues k : ℂ) * inner ℂ (e i) (e k) :=
    BRR_gram R hM
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



lemma BRR_offsum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ι → ℝ) :
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

lemma BRR_scalar {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (t : ℝ) (ht : ∑ i, σ i ≤ t) :
    2 * ((∑ i, σ i ^ 2) ^ 2 - ∑ i, (σ i ^ 2) ^ 2) ≤ (t ^ 2 - ∑ i, σ i ^ 2) ^ 2 := by
  set D := (univ : Finset ι).offDiag
  set x : ι × ι → ℝ := fun p => σ p.1 * σ p.2
  have hx : ∀ p, 0 ≤ x p := fun p => mul_nonneg (hσ _) (hσ _)
  have hQ : ∑ p ∈ D, x p = (∑ i, σ i) ^ 2 - ∑ i, σ i ^ 2 := by
    rw [BRR_offsum (fun i j => σ i * σ j), sq, Finset.sum_mul_sum]; simp [sq]
  have hQ2 : ∑ p ∈ D, x p ^ 2 = (∑ i, σ i ^ 2) ^ 2 - ∑ i, (σ i ^ 2) ^ 2 := by
    rw [BRR_offsum (fun i j => (σ i * σ j) ^ 2), sq (∑ i, σ i ^ 2), Finset.sum_mul_sum]
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

lemma BRR_gnorm (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i : n) :
    ‖(toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ m)‖ ^ 2 = hM.eigenvalues i := by
  have := BRR_gram R hM i i
  rw [inner_self_eq_norm_sq_to_K, orthonormal_iff_ite.mp (hM.eigenvectorBasis).orthonormal i i,
    if_pos rfl, mul_one] at this
  have h := congrArg Complex.re this
  simpa [← Complex.ofReal_pow] using h

lemma BRR_frob {A : Matrix n n ℂ} (hA : A.PosSemidef) (htr : A.trace = 1) :
    ∑ i, ∑ k, ‖A i k‖ ^ 2 ≤ 1 := by
  have hH := hA.1
  have e1 : ((A ^ 2).trace).re = ∑ i, ∑ k, ‖A i k‖ ^ 2 := by
    have : A ^ 2 = A * Aᴴ := by rw [hH.eq, sq]
    rw [this]
    simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
  rw [← e1, BRR_tr_sq hH]
  have hl : ∀ i, 0 ≤ hH.eigenvalues i := hA.eigenvalues_nonneg
  have hs : ∑ i, hH.eigenvalues i = 1 := by
    have := congrArg Complex.re (hH.trace_eq_sum_eigenvalues)
    rw [htr] at this; simpa using this.symm
  have : ∑ i, hH.eigenvalues i ^ 2 ≤ (∑ i, hH.eigenvalues i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hl i)
  rw [hs] at this
  simpa [← Complex.ofReal_pow] using this

omit [DecidableEq n] in
lemma BRR_euc_norm (x : n → ℂ) (h : ∑ i, ‖x i‖ ^ 2 ≤ 1) :
    ‖(toLp 2 x : EuclideanSpace ℂ n)‖ ≤ 1 := by
  rw [EuclideanSpace.norm_eq]
  exact Real.sqrt_le_one.mpr (by simpa using h)

end BRR_PS

namespace QAlgorithms.Papers.Independent.Information100.P19
lemma BRR_Fab : alphaPerm 2 (0 : Fin 4) = 3 ∧ alphaPerm 2 (1 : Fin 4) = 2 ∧ alphaPerm 2 (2 : Fin 4) = 1 ∧
  alphaPerm 2 (3 : Fin 4) = 0 ∧ betaPerm 2 (0 : Fin 4) = 1 ∧ betaPerm 2 (1 : Fin 4) = 0 ∧
  betaPerm 2 (2 : Fin 4) = 3 ∧ betaPerm 2 (3 : Fin 4) = 2 := by decide

lemma BRR_Fprod4 (f : Fin 4 → ℂ) : ∏ r, f r = f 0 * f 1 * f 2 * f 3 := Fin.prod_univ_four f

lemma BRR_Frmom {a b : ℕ} (X : Bip a b) (hH : X.IsHermitian) :
    Matrix.trace ((realign X * (realign X).conjTranspose)^2) = tensorTrace (alphaPerm 2, betaPerm 2) X := by
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := BRR_Fab
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
  rw [BRR_Fprod4]
  simp only [c0, c1, c2, c3, d0, d1, d2, d3, hH.apply]
  ring

/-- Four-index contraction of the Gram factor. -/
def BRR_FQ {a b : ℕ} (B : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (κ : Fin 4 → Fin a × Fin b) : ℂ :=
  ∑ x : Fin a × Fin b × Fin a × Fin b, star (B (κ 0) (x.1, x.2.1)) * B (κ 1) (x.2.2.1, x.2.1) *
    star (B (κ 2) (x.2.2.1, x.2.2.2)) * B (κ 3) (x.1, x.2.2.2)

lemma BRR_Fsep_psd {a b : ℕ} {X : Bip a b} (h : QAlgorithms.Entanglement.IsSeparablePositive X) :
    X.PosSemidef := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := h
  exact Matrix.posSemidef_sum _ (fun j _ =>
    ((hAB j).1.1.kronecker (hAB j).2.1).smul (Complex.zero_le_real.mpr (hw j)))


lemma BRR_tt {n a b : ℕ} (σ : Equiv.Perm (Fin n)) (X : Bip a b) :
    tensorTrace (σ, σ) X = ∑ κ : Fin n → Fin a × Fin b, ∏ r, X (κ r) (κ (σ r)) := by
  unfold tensorTrace
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ (fun ij => rfl)

lemma BRR_four {T : Type*} [Fintype T] (F : (Fin 4 → T) → ℂ) :
    ∑ κ, F κ = ∑ k3, ∑ k2, ∑ k1, ∑ k0, F ![k0, k1, k2, k3] := by
  have : ∑ κ, F κ = ∑ x : T × T × T × T, F ![x.2.2.2, x.2.2.1, x.2.1, x.1] :=
    Fintype.sum_bijective (fun κ => (κ 3, κ 2, κ 1, κ 0))
      (Function.bijective_iff_has_inverse.mpr ⟨fun x => ![x.2.2.2, x.2.2.1, x.2.1, x.1],
        fun κ => by ext r; fin_cases r <;> rfl, fun x => rfl⟩) _ _
      (fun κ => by congr 1; ext r; fin_cases r <;> rfl)
  rw [this]; simp only [Fintype.sum_prod_type]

lemma BRR_s12 : s12 0 = 1 ∧ s12 1 = 0 ∧ s12 2 = 2 ∧ s12 3 = 3 := by decide
lemma BRR_s1234 : (s12*s34) 0 = 1 ∧ (s12*s34) 1 = 0 ∧ (s12*s34) 2 = 3 ∧ (s12*s34) 3 = 2 := by decide

lemma BRR_t1 {a b : ℕ} (X : Bip a b) : tensorTrace ((1, 1) : Perms 4) X = (Matrix.trace X) ^ 4 := by
  rw [BRR_tt, BRR_four]
  simp only [Fin.prod_univ_four, Equiv.Perm.one_apply]
  simp only [Matrix.trace, Matrix.diag, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
  simp

lemma BRR_t2 {a b : ℕ} (X : Bip a b) :
    tensorTrace (s12, s12) X = Matrix.trace (X * X) * (Matrix.trace X) ^ 2 := by
  obtain ⟨c0, c1, c2, c3⟩ := BRR_s12
  rw [BRR_tt, BRR_four]
  simp only [Fin.prod_univ_four, c0, c1, c2, c3]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
  simp
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))))

lemma BRR_t3 {a b : ℕ} (X : Bip a b) :
    tensorTrace (s12*s34, s12*s34) X = (Matrix.trace (X * X)) ^ 2 := by
  obtain ⟨c0, c1, c2, c3⟩ := BRR_s1234
  rw [BRR_tt, BRR_four]
  simp only [Fin.prod_univ_four, c0, c1, c2, c3]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
  simp
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))))

lemma BRR_trace_real {a b : ℕ} {X : Bip a b} (hH : X.IsHermitian) :
    Matrix.trace X = ((mass X : ℝ) : ℂ) := by
  rw [mass, powerTrace, pow_one]
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im, Matrix.trace, Matrix.diag, Complex.im_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have h := congrArg Complex.im (hH.apply i i)
    rw [Complex.star_def, Complex.conj_im] at h
    linarith

lemma BRR_normsumC {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] (M : Matrix I J ℂ) :
    (M * Mᴴ).trace = ((∑ x : I × J, ‖M x.1 x.2‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ← Fintype.sum_prod_type']
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast

lemma BRR_r1 {a b : ℕ} (X : Bip a b) :
    rMoment X 1 = ∑ x : (Fin a × Fin b) × (Fin a × Fin b), ‖X x.1 x.2‖ ^ 2 := by
  rw [rMoment, powerTrace, pow_one, BRR_normsumC, Complex.ofReal_re]
  exact Fintype.sum_equiv
    { toFun := fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))
      invFun := fun y => ((y.1.1, y.2.1), (y.1.2, y.2.2))
      left_inv := fun x => rfl
      right_inv := fun y => rfl } _ _ (fun x => rfl)

lemma BRR_trsq {a b : ℕ} {X : Bip a b} (hH : X.IsHermitian) :
    Matrix.trace (X * X) = ((rMoment X 1 : ℝ) : ℂ) := by
  rw [BRR_r1, ← BRR_normsumC, hH.eq]

lemma BRR_ev_basis {n a b : ℕ} (p : Perms n) (X : Bip a b) :
    tensorEval (tensorBasis p) X = (tensorTrace p X).re := by
  unfold tensorEval tensorBasis
  simp

lemma BRR_ev_add {n a b : ℕ} (f g : TensorCoeff n) (X : Bip a b) :
    tensorEval (f + g) X = tensorEval f X + tensorEval g X := by
  unfold tensorEval; simp [add_mul, Finset.sum_add_distrib]

lemma BRR_ev_sub {n a b : ℕ} (f g : TensorCoeff n) (X : Bip a b) :
    tensorEval (f - g) X = tensorEval f X - tensorEval g X := by
  unfold tensorEval; simp [sub_mul, Finset.sum_sub_distrib]

lemma BRR_ev_smul {n a b : ℕ} (c : ℝ) (f : TensorCoeff n) (X : Bip a b) :
    tensorEval (c • f) X = c * tensorEval f X := by
  unfold tensorEval; simp [Finset.mul_sum, mul_assoc]

lemma BRR_smul_mem {n : ℕ} {c : ℝ} (hc : 0 ≤ c) {f : TensorCoeff n} (hf : f ∈ sepCone n) :
    c • f ∈ sepCone n := by
  intro a b ha hb X hX
  rw [BRR_ev_smul]
  exact mul_nonneg hc (hf a b ha hb X hX)

lemma BRR_formulas {a b : ℕ} (X : Bip a b) (hH : X.IsHermitian) :
    tensorEval wM X = mass X ^ 4 - (3/2 : ℝ) * mass X ^ 2 * rMoment X 1 + (1/2 : ℝ) * rMoment X 2 ∧
    tensorEval wS X = mass X ^ 4 - 2 * (mass X ^ 2 * rMoment X 1) - rMoment X 1 ^ 2 +
      2 * rMoment X 2 ∧
    tensorEval wRemainder X = 3 * mass X ^ 4 - 4 * (mass X ^ 2 * rMoment X 1) + rMoment X 1 ^ 2 := by
  have h1 : (tensorTrace ((1, 1) : Perms 4) X).re = mass X ^ 4 := by
    rw [BRR_t1, BRR_trace_real hH, ← Complex.ofReal_pow, Complex.ofReal_re]
  have h2 : (tensorTrace (s12, s12) X).re = mass X ^ 2 * rMoment X 1 := by
    rw [BRR_t2, BRR_trace_real hH, BRR_trsq hH, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]; ring
  have h3 : (tensorTrace (s12 * s34, s12 * s34) X).re = rMoment X 1 ^ 2 := by
    rw [BRR_t3, BRR_trsq hH, ← Complex.ofReal_pow, Complex.ofReal_re]
  have h4 : (tensorTrace (alphaPerm 2, betaPerm 2) X).re = rMoment X 2 := by
    rw [rMoment, powerTrace, BRR_Frmom X hH]
  refine ⟨?_, ?_, ?_⟩
  · simp only [wM, BRR_ev_add, BRR_ev_sub, BRR_ev_smul, BRR_ev_basis, h1, h2, h4]; ring
  · simp only [wS, BRR_ev_add, BRR_ev_sub, BRR_ev_smul, BRR_ev_basis, h1, h2, h3, h4]
  · simp only [wRemainder, BRR_ev_add, BRR_ev_sub, BRR_ev_smul, BRR_ev_basis, h1, h2, h3]

lemma BRR_psd {a b : ℕ} (X : Bip a b) (hX : X.PosSemidef) :
    0 ≤ rMoment X 1 ∧ rMoment X 1 ≤ mass X ^ 2 := by
  have hH := hX.1
  refine ⟨by rw [BRR_r1]; positivity, ?_⟩
  have e1 : rMoment X 1 = ∑ i, hH.eigenvalues i ^ 2 := by
    have h := BRR_trsq hH
    rw [← sq, BRR_tr_sq hH] at h
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re] at h'
    rw [← h']
    simp [← Complex.ofReal_pow]
  have e2 : mass X = ∑ i, hH.eigenvalues i := by
    have h := BRR_trace_real hH
    rw [hH.trace_eq_sum_eigenvalues] at h
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re] at h'
    rw [← h']
    simp
  rw [e1, e2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hX.eigenvalues_nonneg i)

open Matrix WithLp in
lemma BRR_sepdata {a b : ℕ} (X : Bip a b)
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
    intro j; apply BRR_euc_norm
    rw [Fintype.sum_prod_type]
    exact BRR_frob (hAB j).1.1 (hAB j).1.2
  have hv : ∀ j, ‖(toLp 2 (star (v j)) : EuclideanSpace ℂ (Fin b × Fin b))‖ ≤ 1 := by
    intro j; apply BRR_euc_norm
    rw [Fintype.sum_prod_type]
    simpa [v] using BRR_frob (hAB j).2.1 (hAB j).2.2
  have hM : (R * Rᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self R
  have hc := BRR_ccnr w hw u v hu hv R hR hM
  set σ : Fin a × Fin a → ℝ :=
    fun i => ‖(toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ (Fin b × Fin b))‖
  have hσ2 : ∀ i, σ i ^ 2 = hM.eigenvalues i := BRR_gnorm R hM
  have hr1 : rMoment X 1 = ∑ i, σ i ^ 2 := by
    simp only [hσ2]
    rw [rMoment, powerTrace, pow_one, ← hRdef, hM.trace_eq_sum_eigenvalues]
    simp
  have hr2 : rMoment X 2 = ∑ i, (σ i ^ 2) ^ 2 := by
    simp only [hσ2]
    rw [rMoment, powerTrace, ← hRdef, BRR_tr_sq hM]
    simp [← Complex.ofReal_pow]
  have hmass : mass X = ∑ j, w j := by
    rw [mass, powerTrace, pow_one, hXe, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [trace_smul, Matrix.kronecker, trace_kronecker, (hAB j).1.2, (hAB j).2.2]
    simp
  exact ⟨σ, fun i => norm_nonneg _, by rw [hmass]; exact hc, hr1, hr2⟩

lemma BRR_scalarM {ι : Type*} [Fintype ι] (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i)
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

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution  :
    wM = (1/4 : ℝ) • wS + (1/4 : ℝ) • wRemainder ∧
    wM ∈ sepCone 4 ∧ wS ∈ sepCone 4 ∧ wRemainder ∈ sepCone 4 ∧
    ¬ Extreme (sepCone 4) wM ∧
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.IsHermitian →
      tensorEval wM X = defect 2 X ∧ tensorEval wS X = defect 3 X ∧
      tensorEval wRemainder X = (mass X^2-rMoment X 1)*(3*mass X^2-rMoment X 1)) ∧
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.PosSemidef → 0≤tensorEval wRemainder X) := by
  have hdec : wM = (1/4 : ℝ) • wS + (1/4 : ℝ) • wRemainder := by
    funext q
    simp only [wM, wS, wRemainder, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hRem : ∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.PosSemidef → 0≤tensorEval wRemainder X := by
    intro a b _ _ X hX
    rw [(BRR_formulas X hX.1).2.2]
    obtain ⟨h0, h1⟩ := BRR_psd X hX
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : 0 ≤ 3 * mass X ^ 2 - rMoment X 1)]
  have hMem : wM ∈ sepCone 4 := by
    intro a b _ _ X hX
    rw [(BRR_formulas X (BRR_Fsep_psd hX).1).1]
    obtain ⟨σ, hσ, ht, h1, h2⟩ := BRR_sepdata X hX
    rw [h1, h2]
    exact BRR_scalarM σ hσ _ ht
  have hSm : wS ∈ sepCone 4 := by
    intro a b _ _ X hX
    rw [(BRR_formulas X (BRR_Fsep_psd hX).1).2.1]
    obtain ⟨σ, hσ, ht, h1, h2⟩ := BRR_sepdata X hX
    have := BRR_scalar σ hσ _ ht
    rw [h1, h2]
    nlinarith
  have hRm : wRemainder ∈ sepCone 4 := fun a b ha hb X hX => hRem a b ha hb X (BRR_Fsep_psd hX)
  refine ⟨hdec, hMem, hSm, hRm, ?_, ?_, hRem⟩
  · rintro ⟨-, -, h⟩
    obtain ⟨c, d, -, -, hu, -⟩ := h _ (BRR_smul_mem (by norm_num : (0:ℝ) ≤ 1/4) hSm) _
      (BRR_smul_mem (by norm_num : (0:ℝ) ≤ 1/4) hRm) hdec.symm
    have e := congrFun hu (s12 * s34, s12 * s34)
    have n1 : ((s12 * s34, s12 * s34) : Perms 4) ≠ (1, 1) := by decide
    have n2 : ((s12 * s34, s12 * s34) : Perms 4) ≠ (s12, s12) := by decide
    have n3 : ((s12 * s34, s12 * s34) : Perms 4) ≠ (alphaPerm 2, betaPerm 2) := by decide
    simp only [wM, wS, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, tensorBasis,
      if_neg n1, if_neg n2, if_neg n3] at e
    norm_num at e
  · intro a b _ _ X hX
    obtain ⟨h1, h2, h3⟩ := BRR_formulas X hX
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]; simp [defect]
    · rw [h2]; simp [defect]; ring
    · rw [h3]; ring

end
