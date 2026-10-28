-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.pure_state_detection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:25:21.902701+00:00
-- url     : https://prove2.me/submissions/4bf9f48a-c666-4baf-9f74-4b312ca02030

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

section PSD_S180
open Matrix Finset WithLp
open scoped ComplexOrder

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma PSD_S180_tr_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A ^ 2).trace = ∑ i, ((hA.eigenvalues i : ℂ)) ^ 2 := by
  have h := hA.spectral_theorem
  conv_lhs => rw [h]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, diagonal_pow, trace_diagonal]
  simp

lemma PSD_S180_adj_expand {q : ℕ} (w : Fin q → ℝ) (u : Fin q → n → ℂ) (v : Fin q → m → ℂ)
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

lemma PSD_S180_gram (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i k : n) :
    inner ℂ (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i))) (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis k)))
      = (hM.eigenvalues k : ℂ) * inner ℂ (hM.eigenvectorBasis i) (hM.eigenvectorBasis k) := by
  rw [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_eq_star_dotProduct, star_mulVec,
    dotProduct_comm, ← dotProduct_mulVec, conjTranspose_conjTranspose, mulVec_mulVec,
    hM.mulVec_eigenvectorBasis, dotProduct_comm]
  rw [smul_dotProduct, Complex.real_smul]

lemma PSD_S180_ccnr {q : ℕ} (w : Fin q → ℝ) (hw : ∀ j, 0 ≤ w j) (u : Fin q → n → ℂ)
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
    rw [PSD_S180_adj_expand w u v R hR]
    apply (WithLp.equiv 2 _).injective
    ext k
    simp [EuclideanSpace.inner_eq_star_dotProduct]
  have hgg : ∀ i k, inner ℂ (g i) (g k) = (hM.eigenvalues k : ℂ) * inner ℂ (e i) (e k) :=
    PSD_S180_gram R hM
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



lemma PSD_S180_offsum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ι → ℝ) :
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

lemma PSD_S180_scalar {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (t : ℝ) (ht : ∑ i, σ i ≤ t) :
    2 * ((∑ i, σ i ^ 2) ^ 2 - ∑ i, (σ i ^ 2) ^ 2) ≤ (t ^ 2 - ∑ i, σ i ^ 2) ^ 2 := by
  set D := (univ : Finset ι).offDiag
  set x : ι × ι → ℝ := fun p => σ p.1 * σ p.2
  have hx : ∀ p, 0 ≤ x p := fun p => mul_nonneg (hσ _) (hσ _)
  have hQ : ∑ p ∈ D, x p = (∑ i, σ i) ^ 2 - ∑ i, σ i ^ 2 := by
    rw [PSD_S180_offsum (fun i j => σ i * σ j), sq, Finset.sum_mul_sum]; simp [sq]
  have hQ2 : ∑ p ∈ D, x p ^ 2 = (∑ i, σ i ^ 2) ^ 2 - ∑ i, (σ i ^ 2) ^ 2 := by
    rw [PSD_S180_offsum (fun i j => (σ i * σ j) ^ 2), sq (∑ i, σ i ^ 2), Finset.sum_mul_sum]
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

lemma PSD_S180_gnorm (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i : n) :
    ‖(toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ m)‖ ^ 2 = hM.eigenvalues i := by
  have := PSD_S180_gram R hM i i
  rw [inner_self_eq_norm_sq_to_K, orthonormal_iff_ite.mp (hM.eigenvectorBasis).orthonormal i i,
    if_pos rfl, mul_one] at this
  have h := congrArg Complex.re this
  simpa [← Complex.ofReal_pow] using h

lemma PSD_S180_frob {A : Matrix n n ℂ} (hA : A.PosSemidef) (htr : A.trace = 1) :
    ∑ i, ∑ k, ‖A i k‖ ^ 2 ≤ 1 := by
  have hH := hA.1
  have e1 : ((A ^ 2).trace).re = ∑ i, ∑ k, ‖A i k‖ ^ 2 := by
    have : A ^ 2 = A * Aᴴ := by rw [hH.eq, sq]
    rw [this]
    simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
  rw [← e1, PSD_S180_tr_sq hH]
  have hl : ∀ i, 0 ≤ hH.eigenvalues i := hA.eigenvalues_nonneg
  have hs : ∑ i, hH.eigenvalues i = 1 := by
    have := congrArg Complex.re (hH.trace_eq_sum_eigenvalues)
    rw [htr] at this; simpa using this.symm
  have : ∑ i, hH.eigenvalues i ^ 2 ≤ (∑ i, hH.eigenvalues i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hl i)
  rw [hs] at this
  simpa [← Complex.ofReal_pow] using this

omit [DecidableEq n] in
lemma PSD_S180_euc_norm (x : n → ℂ) (h : ∑ i, ‖x i‖ ^ 2 ≤ 1) :
    ‖(toLp 2 x : EuclideanSpace ℂ n)‖ ≤ 1 := by
  rw [EuclideanSpace.norm_eq]
  exact Real.sqrt_le_one.mpr (by simpa using h)

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem PSD_ccnr_sol (a b : ℕ) (ha : 0<a) (hb : 0<b) (X : Bip a b)
    (hX : QAlgorithms.Entanglement.IsSeparablePositive X) :
    2*(rMoment X 1^2-rMoment X 2) ≤ (mass X^2-rMoment X 1)^2 := by
  obtain ⟨q, w, A, B, hw, hAB, hXe⟩ := hX
  set R := realign X with hRdef
  set u : Fin q → Fin a × Fin a → ℂ := fun j i => A j i.1 i.2
  set v : Fin q → Fin b × Fin b → ℂ := fun j k => B j k.1 k.2
  have hR : R = ∑ j, (w j : ℂ) • Matrix.of (fun i k => u j i * v j k) := by
    ext i k
    simp [hRdef, realign, hXe, Matrix.sum_apply, kronecker, kroneckerMap, u, v]
  have hu : ∀ j, ‖(toLp 2 (u j) : EuclideanSpace ℂ (Fin a × Fin a))‖ ≤ 1 := by
    intro j; apply PSD_S180_euc_norm
    rw [Fintype.sum_prod_type]
    exact PSD_S180_frob (hAB j).1.1 (hAB j).1.2
  have hv : ∀ j, ‖(toLp 2 (star (v j)) : EuclideanSpace ℂ (Fin b × Fin b))‖ ≤ 1 := by
    intro j; apply PSD_S180_euc_norm
    rw [Fintype.sum_prod_type]
    simpa [v] using PSD_S180_frob (hAB j).2.1 (hAB j).2.2
  have hM : (R * Rᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self R
  have hc := PSD_S180_ccnr w hw u v hu hv R hR hM
  set σ : Fin a × Fin a → ℝ :=
    fun i => ‖(toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ (Fin b × Fin b))‖
  have hσ2 : ∀ i, σ i ^ 2 = hM.eigenvalues i := PSD_S180_gnorm R hM
  have hr1 : rMoment X 1 = ∑ i, σ i ^ 2 := by
    simp only [hσ2]
    rw [rMoment, powerTrace, pow_one, ← hRdef, hM.trace_eq_sum_eigenvalues]
    simp
  have hr2 : rMoment X 2 = ∑ i, (σ i ^ 2) ^ 2 := by
    simp only [hσ2]
    rw [rMoment, powerTrace, ← hRdef, PSD_S180_tr_sq hM]
    simp [← Complex.ofReal_pow]
  have hmass : mass X = ∑ j, w j := by
    rw [mass, powerTrace, pow_one, hXe, trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [trace_smul, Matrix.kronecker, trace_kronecker, (hAB j).1.2, (hAB j).2.2]
    simp
  rw [hr1, hr2, hmass]
  exact PSD_S180_scalar σ (fun i => norm_nonneg _) _ hc

end PSD_S180

section PSD_helpers
open Matrix Finset
open scoped ComplexOrder ComplexConjugate

lemma PSD_tr_pow {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (k : ℕ) : (A ^ k).trace = ((∑ i, hA.eigenvalues i ^ k : ℝ) : ℂ) := by
  have h := hA.spectral_theorem
  conv_lhs => rw [h]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, diagonal_pow, trace_diagonal]
  simp

lemma PSD_spec_entry {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (i j : n) :
    A i j = ∑ k, (hA.eigenvectorUnitary : Matrix n n ℂ) i k * (hA.eigenvalues k : ℂ) *
      star ((hA.eigenvectorUnitary : Matrix n n ℂ) j k) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
  simp [Matrix.mul_diagonal, star_apply]

lemma PSD_tr_ct {n m : Type*} [Fintype n] [Fintype m] (A B : Matrix n m ℂ) :
    (A * Bᴴ).trace = ∑ i, ∑ k, A i k * star (B i k) := by
  simp [trace, mul_apply]

namespace QAlgorithms.Papers.Independent.Information100.P19

variable {a b : ℕ}

lemma PSD_realign (M : Matrix (Fin a) (Fin b) ℂ) :
    realign (outer (fun p => M p.1 p.2)) = kroneckerMap (· * ·) M (M.map star) := by
  ext p q; rfl

lemma PSD_mA (M : Matrix (Fin a) (Fin b) ℂ) :
    marginalA (outer (fun p => M p.1 p.2)) = M * Mᴴ := by
  ext i j; simp [marginalA, outer, mul_apply]

lemma PSD_mB (M : Matrix (Fin a) (Fin b) ℂ) :
    marginalB (outer (fun p => M p.1 p.2)) = Mᵀ * (Mᵀ)ᴴ := by
  ext i j; simp [marginalB, outer, mul_apply]

lemma PSD_mapT (M : Matrix (Fin a) (Fin b) ℂ) : M.map star * (M.map star)ᴴ = (M * Mᴴ)ᵀ := by
  ext i j; simp [mul_apply, mul_comm]

lemma PSD_RR (M : Matrix (Fin a) (Fin b) ℂ) :
    realign (outer (fun p => M p.1 p.2)) * (realign (outer (fun p => M p.1 p.2)))ᴴ =
      kroneckerMap (· * ·) (M * Mᴴ) (M * Mᴴ)ᵀ := by
  rw [PSD_realign, conjTranspose_kronecker, ← mul_kronecker_mul, PSD_mapT]

lemma PSD_r1 (M : Matrix (Fin a) (Fin b) ℂ) :
    rMoment (outer (fun p => M p.1 p.2)) 1 = ((M * Mᴴ).trace * (M * Mᴴ).trace).re := by
  rw [rMoment, powerTrace, pow_one, PSD_RR, trace_kronecker, trace_transpose]

lemma PSD_r2 (M : Matrix (Fin a) (Fin b) ℂ) :
    rMoment (outer (fun p => M p.1 p.2)) 2 =
      (((M * Mᴴ) ^ 2).trace * ((M * Mᴴ) ^ 2).trace).re := by
  rw [rMoment, powerTrace, PSD_RR, sq, ← mul_kronecker_mul, trace_kronecker, ← transpose_mul,
    trace_transpose, sq]

lemma PSD_mass (M : Matrix (Fin a) (Fin b) ℂ) :
    mass (outer (fun p => M p.1 p.2)) = ((M * Mᴴ).trace).re := by
  rw [mass, powerTrace, pow_one, PSD_tr_ct]
  simp [trace, outer, Fintype.sum_prod_type]

lemma PSD_pA (M : Matrix (Fin a) (Fin b) ℂ) :
    purityA (outer (fun p => M p.1 p.2)) = (((M * Mᴴ) ^ 2).trace).re := by
  rw [purityA, powerTrace, PSD_mA]

lemma PSD_trB (M : Matrix (Fin a) (Fin b) ℂ) :
    ((Mᵀ * (Mᵀ)ᴴ) ^ 2).trace = ((M * Mᴴ) ^ 2).trace := by
  have : Mᵀ * (Mᵀ)ᴴ = (Mᴴ * M)ᵀ := by
    ext i j; simp [mul_apply, mul_comm]
  rw [this, sq, ← transpose_mul, trace_transpose, sq, Matrix.mul_assoc, trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma PSD_pB (M : Matrix (Fin a) (Fin b) ℂ) :
    purityB (outer (fun p => M p.1 p.2)) = (((M * Mᴴ) ^ 2).trace).re := by
  rw [purityB, powerTrace, PSD_mB, PSD_trB]


lemma PSD_cross_gen (M : Matrix (Fin a) (Fin b) ℂ) (ρ : Matrix (Fin a) (Fin a) ℂ)
    (σ : Matrix (Fin b) (Fin b) ℂ) :
    (realign (kronecker ρ σ) * (kroneckerMap (· * ·) M (M.map star))ᴴ).trace =
      (ρ * (M * σᵀ * Mᴴ)).trace := by
  rw [PSD_tr_ct]
  simp only [Fintype.sum_prod_type, realign, kronecker, kroneckerMap_apply, map_apply, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, transpose_apply, conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  simp only [star_mul', star_star]
  ring

lemma PSD_sq_gen (ρ : Matrix (Fin a) (Fin a) ℂ) (σ : Matrix (Fin b) (Fin b) ℂ) :
    (realign (kronecker ρ σ) * (realign (kronecker ρ σ))ᴴ).trace =
      (ρ * ρᴴ).trace * (σ * σᴴ).trace := by
  rw [mul_comm ((ρ * ρᴴ).trace), PSD_tr_ct, PSD_tr_ct, PSD_tr_ct]
  simp only [Fintype.sum_prod_type, realign, kronecker, kroneckerMap_apply, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  simp only [star_mul']
  ring

lemma PSD_cent (M : Matrix (Fin a) (Fin b) ℂ) (htr : (M * Mᴴ).trace = 1) :
    rMoment (centered (outer (fun p => M p.1 p.2))) 1 =
      1 - 2 * (((M * Mᴴ) ^ 3).trace).re + (((M * Mᴴ) ^ 2).trace * ((M * Mᴴ) ^ 2).trace).re := by
  set X : Bip a b := outer (fun p => M p.1 p.2) with hX
  have hm : mass X = 1 := by rw [hX, PSD_mass, htr]; simp
  set ρ := M * Mᴴ with hρ
  set σ := Mᵀ * (Mᵀ)ᴴ with hσ
  set R1 := kroneckerMap (· * ·) M (M.map star) with hR1
  set R2 := realign (kronecker ρ σ) with hR2
  have hC : realign (centered X) = R1 - R2 := by
    have hmA : marginalA X = ρ := PSD_mA M
    have hmB : marginalB X = σ := PSD_mB M
    rw [hR1, ← PSD_realign, hR2]
    ext p q
    simp [realign, centered, hm, hmA, hmB, X]
  have h11 : (R1 * R1ᴴ).trace = 1 := by
    rw [hR1, ← PSD_realign, PSD_RR, trace_kronecker, trace_transpose, ← hρ, htr, one_mul]
  have h21 : (R2 * R1ᴴ).trace = (ρ ^ 3).trace := by
    rw [hR2, hR1, PSD_cross_gen]
    congr 1
    have : σᵀ = Mᴴ * M := by rw [hσ]; ext i j; simp [mul_apply, mul_comm]
    rw [this, pow_succ, sq, hρ]
    simp only [Matrix.mul_assoc]
  have h12 : (R1 * R2ᴴ).trace = star (ρ ^ 3).trace := by
    rw [← h21, ← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  have hρH : ρᴴ = ρ := (isHermitian_mul_conjTranspose_self M).eq
  have hσH : σᴴ = σ := (isHermitian_mul_conjTranspose_self Mᵀ).eq
  have h22 : (R2 * R2ᴴ).trace = (ρ ^ 2).trace * (ρ ^ 2).trace := by
    rw [hR2, PSD_sq_gen, hρH, hσH, ← sq, ← sq, hσ, PSD_trB]
  rw [rMoment, powerTrace, pow_one, hC, conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [trace_sub]
  rw [h11, h21, h12, h22]
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.star_def, Complex.conj_re]
  ring


lemma PSD_scal {ι : Type*} [Fintype ι] (l : ι → ℝ) (h0 : ∀ i, 0 ≤ l i) (h1 : ∑ i, l i = 1) :
    (∀ i, l i ≤ 1) ∧ ∑ i, l i ^ 2 ≤ 1 ∧ 0 ≤ ∑ i, l i ^ 2 ∧ ∑ i, l i ^ 3 ≤ ∑ i, l i ^ 2 ∧
      (∑ i, l i ^ 3 = ∑ i, l i ^ 2 → ∑ i, l i ^ 2 = 1) ∧
      (∑ i, l i ^ 2 = 1 → ∀ i, l i = 0 ∨ l i = 1) := by
  classical
  have hle : ∀ i, l i ≤ 1 := fun i => by
    rw [← h1]; exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
  have hsq : ∀ i, l i ^ 2 ≤ l i := fun i => by nlinarith [h0 i, hle i]
  have hcu : ∀ i, l i ^ 3 ≤ l i ^ 2 := fun i => by nlinarith [h0 i, hle i, sq_nonneg (l i)]
  refine ⟨hle, ?_, Finset.sum_nonneg (fun i _ => sq_nonneg _), Finset.sum_le_sum (fun i _ => hcu i),
    ?_, ?_⟩
  · rw [← h1]; exact Finset.sum_le_sum (fun i _ => hsq i)
  · intro h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun i => l i ^ 2 - l i ^ 3) (fun i _ => sub_nonneg.mpr (hcu i))).mp
      (by rw [Finset.sum_sub_distrib, h, sub_self])
    have : ∀ i, l i ^ 2 = l i := by
      intro i
      have := hz i (Finset.mem_univ i)
      have h' : l i ^ 2 * (1 - l i) = 0 := by linear_combination this
      rcases mul_eq_zero.mp h' with h'' | h''
      · have : l i = 0 := by simpa using h''
        rw [this]; ring
      · have : l i = 1 := by linarith
        rw [this]; ring
    rw [Finset.sum_congr rfl (fun i _ => this i), h1]
  · intro h i
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun i => l i - l i ^ 2) (fun i _ => sub_nonneg.mpr (hsq i))).mp
      (by rw [Finset.sum_sub_distrib, h, h1, sub_self])
    have := hz i (Finset.mem_univ i)
    have h' : l i * (1 - l i) = 0 := by linear_combination this
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (by linarith)

lemma PSD_sep_of (M : Matrix (Fin a) (Fin b) ℂ) (htr : (M * Mᴴ).trace = 1)
    (hH : (M * Mᴴ).IsHermitian) (h0 : ∀ i, 0 ≤ hH.eigenvalues i)
    (h1 : ∑ i, hH.eigenvalues i = 1) (hP : ∑ i, hH.eigenvalues i ^ 2 = 1) :
    QAlgorithms.Entanglement.IsSeparablePositive (outer (fun p => M p.1 p.2)) := by
  classical
  set l := hH.eigenvalues with hl
  set ρ := M * Mᴴ with hρ
  obtain ⟨-, -, -, -, -, h01⟩ := PSD_scal l h0 h1
  have h01 := h01 hP
  obtain ⟨k0, hk0⟩ : ∃ k0, l k0 = 1 := by
    by_contra hne
    push Not at hne
    have : ∑ i, l i = 0 := Finset.sum_eq_zero (fun i _ => (h01 i).resolve_right (hne i))
    rw [h1] at this; exact one_ne_zero this
  have hk : ∀ k, k ≠ k0 → l k = 0 := by
    intro k hk
    refine (h01 k).resolve_right (fun hk1 => ?_)
    have hsub : ({k0, k} : Finset (Fin a)) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := l) (fun i _ _ => h0 i)
    rw [Finset.sum_pair (Ne.symm hk), hk0, hk1, h1] at this
    norm_num at this
  have hT : ∑ i, l i ^ 3 = 1 := by
    rw [← hP]; refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases h01 i with h | h <;> rw [h] <;> ring
  set U : Matrix (Fin a) (Fin a) ℂ := (hH.eigenvectorUnitary : Matrix (Fin a) (Fin a) ℂ)
  set u : Fin a → ℂ := fun i => U i k0 with hu
  have hρu : ∀ i i', ρ i i' = u i * star (u i') := by
    intro i i'
    rw [PSD_spec_entry hH, Finset.sum_eq_single k0]
    · rw [← hl, hk0]; simp [u, U]
    · intro k _ hne; rw [← hl, hk k hne]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  have hρH : ρᴴ = ρ := hH.eq
  have htp : ∀ k, (ρ ^ k).trace = ((∑ i, l i ^ k : ℝ) : ℂ) := PSD_tr_pow hH
  -- M = ρ * M
  have hD : (1 - ρ) * M = 0 := by
    rw [← trace_mul_conjTranspose_self_eq_zero_iff, conjTranspose_mul, conjTranspose_sub,
      conjTranspose_one, hρH, ← Matrix.mul_assoc, Matrix.mul_assoc (1 - ρ) M, ← hρ]
    have e : (1 - ρ) * ρ * (1 - ρ) = ρ ^ 1 - ρ ^ 2 - ρ ^ 2 + ρ ^ 3 := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, pow_succ,
        pow_zero, Matrix.mul_assoc]
      abel
    rw [e, trace_add, trace_sub, trace_sub, htp, htp, htp, hP, hT]
    simp only [pow_one, h1]
    norm_num
  have hMeq : M = ρ * M := by
    have := hD; rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this; exact this
  set v : Fin b → ℂ := fun j => ∑ l', star (u l') * M l' j with hv
  have hMuv : ∀ i j, M i j = u i * v j := by
    intro i j
    rw [hMeq, mul_apply]
    simp only [hρu, hv, Finset.mul_sum, mul_assoc]
  have hun : ∑ i, u i * star (u i) = 1 := by
    rw [← htr]; simp only [Matrix.trace, Matrix.diag]
    exact Finset.sum_congr rfl (fun i _ => (hρu i i).symm)
  have hvn : ∑ j, v j * star (v j) = 1 := by
    rw [← htr, PSD_tr_ct]
    simp only [hMuv, star_mul']
    have : ∀ i, ∑ j, u i * v j * (star (u i) * star (v j)) =
        (u i * star (u i)) * ∑ j, v j * star (v j) := by
      intro i; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.sum_mul, hun, one_mul]
  refine ⟨1, fun _ => 1, fun _ => vecMulVec u (star u), fun _ => vecMulVec v (star v),
    fun _ => zero_le_one, fun _ => ⟨⟨posSemidef_vecMulVec_self_star u, ?_⟩,
      ⟨posSemidef_vecMulVec_self_star v, ?_⟩⟩, ?_⟩
  · simpa [Matrix.trace, vecMulVec_apply] using hun
  · simpa [Matrix.trace, vecMulVec_apply] using hvn
  · ext p q
    simp only [outer, Fin.sum_univ_one, Complex.ofReal_one, one_smul, kronecker,
      kroneckerMap_apply, vecMulVec_apply, Pi.star_apply, hMuv]
    simp only [Complex.star_def, map_mul]
    ring

theorem PSD_main (M : Matrix (Fin a) (Fin b) ℂ) (ha : 0 < a) (hb : 0 < b)
    (hpsi : ∑ p : Fin a × Fin b, Complex.normSq (M p.1 p.2) = 1) :
    let X := outer (fun p => M p.1 p.2)
    (0 < rMoment (centered X) 1-G X ↔ ¬ QAlgorithms.Entanglement.IsSeparablePositive X) ∧
    (1 < (3/2 : ℝ)*rMoment X 1-(1/2 : ℝ)*rMoment X 2 ↔
      ¬ QAlgorithms.Entanglement.IsSeparablePositive X) ∧
    ((1-rMoment X 1)^2 < 2*(rMoment X 1^2-rMoment X 2) ↔
      ¬ QAlgorithms.Entanglement.IsSeparablePositive X) ∧
    (rMoment X 2 < rMoment X 1^3 ↔ ¬ QAlgorithms.Entanglement.IsSeparablePositive X) := by
  intro X
  have htr : (M * Mᴴ).trace = 1 := by
    rw [PSD_tr_ct, ← Complex.ofReal_one, ← hpsi, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [Complex.star_def, Complex.mul_conj]
  have hH : (M * Mᴴ).IsHermitian := isHermitian_mul_conjTranspose_self M
  set l := hH.eigenvalues with hl
  have h0 : ∀ i, 0 ≤ l i := (posSemidef_self_mul_conjTranspose M).eigenvalues_nonneg
  have htp : ∀ k, ((M * Mᴴ) ^ k).trace = ((∑ i, l i ^ k : ℝ) : ℂ) := PSD_tr_pow hH
  have h1 : ∑ i, l i = 1 := by
    have := htp 1
    rw [pow_one, htr] at this
    simp only [pow_one] at this
    exact_mod_cast this.symm
  set P := ∑ i, l i ^ 2 with hPdef
  set T := ∑ i, l i ^ 3 with hTdef
  obtain ⟨-, hP1, hP0, hTP, hTeq, h01⟩ := PSD_scal l h0 h1
  have hPT : P = 1 → T = P := by
    intro hP
    have h01 := h01 hP
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases h01 i with h | h <;> rw [h] <;> ring
  have hmass : mass X = 1 := by rw [PSD_mass, htr]; simp
  have hr1 : rMoment X 1 = 1 := by rw [PSD_r1, htr]; simp
  have hr2 : rMoment X 2 = P ^ 2 := by
    rw [PSD_r2, htp 2, ← hPdef, ← Complex.ofReal_mul, Complex.ofReal_re, sq]
  have hG : G X = (1 - P) ^ 2 := by
    rw [G, hmass, PSD_pA, PSD_pB, htp 2, Complex.ofReal_re]; ring
  have hc : rMoment (centered X) 1 = 1 - 2 * T + P ^ 2 := by
    rw [PSD_cent M htr, htp 3, htp 2, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.ofReal_re, sq]
  have hsep : QAlgorithms.Entanglement.IsSeparablePositive X ↔ P = 1 := by
    constructor
    · intro hs
      have := PSD_ccnr_sol a b ha hb X hs
      rw [hr1, hr2, hmass] at this
      nlinarith
    · intro hP
      exact PSD_sep_of M htr hH h0 h1 hP
  have hnsep : ¬ QAlgorithms.Entanglement.IsSeparablePositive X ↔ P < 1 := by
    rw [hsep]; constructor
    · intro h; exact lt_of_le_of_ne hP1 h
    · intro h h'; linarith
  rw [hnsep, hc, hG, hr1, hr2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro h
      refine lt_of_le_of_ne hP1 (fun hP => ?_)
      have := hPT hP
      nlinarith
    · intro h
      have hne : T ≠ P := fun he => by have := hTeq he; linarith
      have : T < P := lt_of_le_of_ne hTP hne
      nlinarith
  · constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · constructor
    · intro h; nlinarith
    · intro h; nlinarith

end QAlgorithms.Papers.Independent.Information100.P19

end PSD_helpers

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 6.1; arXiv:2609.29471v1, PDF pp.38, 39. -/
theorem PSD_solution (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (psi : Fin a × Fin b → ℂ) (hpsi : ∑ i, Complex.normSq (psi i)=1) :
    let X := outer psi
    (0 < rMoment (centered X) 1-G X ↔ ¬ QAlgorithms.Entanglement.IsSeparablePositive X) ∧
    (1 < (3/2 : ℝ)*rMoment X 1-(1/2 : ℝ)*rMoment X 2 ↔
      ¬ QAlgorithms.Entanglement.IsSeparablePositive X) ∧
    ((1-rMoment X 1)^2 < 2*(rMoment X 1^2-rMoment X 2) ↔
      ¬ QAlgorithms.Entanglement.IsSeparablePositive X) ∧
    (rMoment X 2 < rMoment X 1^3 ↔ ¬ QAlgorithms.Entanglement.IsSeparablePositive X) :=
  PSD_main (Matrix.of fun i j => psi (i, j)) ha hb hpsi

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (psi : Fin a × Fin b → ℂ) (hpsi : ∑ i, Complex.normSq (psi i)=1) :
    let X := outer psi
    (0 < rMoment (centered X) 1-G X ↔ ¬ QAlgorithms.Entanglement.IsSeparablePositive X) ∧
    (1 < (3/2 : ℝ)*rMoment X 1-(1/2 : ℝ)*rMoment X 2 ↔
      ¬ QAlgorithms.Entanglement.IsSeparablePositive X) ∧
    ((1-rMoment X 1)^2 < 2*(rMoment X 1^2-rMoment X 2) ↔
      ¬ QAlgorithms.Entanglement.IsSeparablePositive X) ∧
    (rMoment X 2 < rMoment X 1^3 ↔ ¬ QAlgorithms.Entanglement.IsSeparablePositive X) :=
  PSD_solution a b ha hb psi hpsi

end
