-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.discrete_separability_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:49:43.940706+00:00
-- url     : https://prove2.me/submissions/9f3373d9-fa4d-4c65-8250-ae2447d9ff30

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

section DSB_gen
open Matrix Finset WithLp

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma DSB_tr_pow {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, ((hA.eigenvalues i : ℂ)) ^ k := by
  have h := hA.spectral_theorem
  conv_lhs => rw [h]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, diagonal_pow, trace_diagonal]
  simp

lemma DSB_tr_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℂ)) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal]
  simp

omit [DecidableEq m] in
lemma DSB_gram (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i k : n) :
    inner ℂ (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i))) (toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis k)))
      = (hM.eigenvalues k : ℂ) * inner ℂ (hM.eigenvectorBasis i) (hM.eigenvectorBasis k) := by
  rw [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_eq_star_dotProduct, star_mulVec,
    dotProduct_comm, ← dotProduct_mulVec, conjTranspose_conjTranspose, mulVec_mulVec,
    hM.mulVec_eigenvectorBasis, dotProduct_comm]
  rw [smul_dotProduct, Complex.real_smul]

lemma DSB_gnorm (R : Matrix n m ℂ) (hM : (R * Rᴴ).IsHermitian) (i : n) :
    ‖(toLp 2 (Rᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ m)‖ ^ 2 = hM.eigenvalues i := by
  have := DSB_gram R hM i i
  rw [inner_self_eq_norm_sq_to_K, orthonormal_iff_ite.mp (hM.eigenvectorBasis).orthonormal i i,
    if_pos rfl, mul_one] at this
  have h := congrArg Complex.re this
  simpa [← Complex.ofReal_pow] using h

lemma DSB_trnorm (M : Matrix n n ℂ) (hM : (Mᴴ * Mᴴᴴ).IsHermitian) :
    QAlgorithms.traceNorm M = ∑ i, ‖(toLp 2 (Mᴴᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ n)‖ := by
  unfold QAlgorithms.traceNorm
  have e : Mᴴ * M = Mᴴ * Mᴴᴴ := by rw [conjTranspose_conjTranspose]
  rw [e, DSB_tr_cfc hM, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.ofReal_re, ← DSB_gnorm Mᴴ hM i, Real.sqrt_sq (norm_nonneg _)]

lemma DSB_powtr (M : Matrix n n ℂ) (hM : (Mᴴ * Mᴴᴴ).IsHermitian) (k : ℕ) :
    ((Mᴴ * M) ^ k).trace.re =
      ∑ i, ‖(toLp 2 (Mᴴᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ n)‖ ^ (2 * k) := by
  have e : Mᴴ * M = Mᴴ * Mᴴᴴ := by rw [conjTranspose_conjTranspose]
  rw [e, DSB_tr_pow hM, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pow_mul, DSB_gnorm Mᴴ hM i, ← Complex.ofReal_pow, Complex.ofReal_re]


lemma DSB_cyc (A : Matrix m n ℂ) (B : Matrix n m ℂ) (k : ℕ) :
    ((A * B) ^ (k + 1)).trace = ((B * A) ^ (k + 1)).trace := by
  have h : ∀ k : ℕ, (A * B) ^ (k + 1) = A * (B * A) ^ k * B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [h, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

lemma DSB_adj_expand {Q : Type*} [Fintype Q] (w : Q → ℝ) (u : Q → n → ℂ) (v : Q → m → ℂ)
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

lemma DSB_ccnr {Q : Type*} [Fintype Q] (w : Q → ℝ) (hw : ∀ j, 0 ≤ w j) (u : Q → n → ℂ)
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
    rw [DSB_adj_expand w u v R hR]
    apply (WithLp.equiv 2 _).injective
    ext k
    simp [EuclideanSpace.inner_eq_star_dotProduct]
  have hgg : ∀ i k, inner ℂ (g i) (g k) = (hM.eigenvalues k : ℂ) * inner ℂ (e i) (e k) :=
    DSB_gram R hM
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

end DSB_gen

section DSB_sc
open Matrix Finset

lemma DSB_id {Q : Type*} [Fintype Q] (w : Q → ℝ) (α β : Q → ℂ) :
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

lemma DSB_idn {Q : Type*} [Fintype Q] (w : Q → ℝ) (α : Q → ℂ) :
    ∑ p : Q × Q, (w p.1 * w p.2 / 2) * ‖α p.1 - α p.2‖ ^ 2 =
      (∑ j, w j) * (∑ j, w j * ‖α j‖ ^ 2) - ‖∑ j, (w j : ℂ) * α j‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj', map_sub, map_sum, map_mul, Complex.conj_ofReal]
  rw [← DSB_id]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  push_cast; ring

lemma DSB_tr_sq {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A ^ 2).trace.re = ∑ i, ∑ k, ‖A i k‖ ^ 2 := by
  have : A ^ 2 = A * Aᴴ := by rw [hA.eq, sq]
  rw [this]
  simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast

lemma DSB_frob {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htr : A.trace = 1) : ∑ i, ∑ k, ‖A i k‖ ^ 2 ≤ 1 := by
  have hH := hA.1
  rw [← DSB_tr_sq hH]
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

end DSB_sc

namespace QAlgorithms.Papers.Independent.Information100.P19
open Matrix WithLp

lemma DSB_sq_gram {a b : ℕ} (Y : Bip a b) :
    (realignmentSquare Y)ᴴ * realignmentSquare Y =
      fromBlocks 0 0 0 ((realign Y)ᴴ * realign Y) := by
  simp [realignmentSquare, fromBlocks_conjTranspose, fromBlocks_multiply]

lemma DSB_fb_pow {a b : ℕ} (D : Matrix (Fin b × Fin b) (Fin b × Fin b) ℂ) (k : ℕ) :
    (fromBlocks (0 : Matrix (Fin a × Fin a) (Fin a × Fin a) ℂ) 0 0 D) ^ (k + 1) =
      fromBlocks 0 0 0 (D ^ (k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, fromBlocks_multiply, pow_succ (n := k + 1)]; simp

lemma DSB_fb_tr {a b : ℕ} (D : Matrix (Fin b × Fin b) (Fin b × Fin b) ℂ) :
    (fromBlocks (0 : Matrix (Fin a × Fin a) (Fin a × Fin a) ℂ) 0 0 D).trace = D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

lemma DSB_spec {a b : ℕ} (Y : Bip a b) :
    ∃ σ : (Fin a × Fin a) ⊕ (Fin b × Fin b) → ℝ, (∀ i, 0 ≤ σ i) ∧
      QAlgorithms.traceNorm (realignmentSquare Y) = ∑ i, σ i ∧
      ∀ k : ℕ, rMoment Y (k + 1) = ∑ i, σ i ^ (2 * (k + 1)) := by
  set M := realignmentSquare Y with hMdef
  have hM : (Mᴴ * Mᴴᴴ).IsHermitian := isHermitian_mul_conjTranspose_self Mᴴ
  refine ⟨fun i => ‖(toLp 2 (Mᴴᴴ *ᵥ ⇑(hM.eigenvectorBasis i)) : EuclideanSpace ℂ _)‖,
    fun i => norm_nonneg _, DSB_trnorm M hM, fun k => ?_⟩
  rw [← DSB_powtr M hM, hMdef, DSB_sq_gram, DSB_fb_pow, DSB_fb_tr, DSB_cyc]
  rfl

lemma DSB_bound {a b : ℕ} (Y : Bip a b) {Q : Type*} [Fintype Q] (w : Q → ℝ) (hw : ∀ j, 0 ≤ w j)
    (p : Q → Fin a × Fin a → ℂ) (r : Q → Fin b × Fin b → ℂ)
    (hY : realign Y = ∑ j, (w j : ℂ) • Matrix.of (fun x y => p j x * r j y)) :
    QAlgorithms.traceNorm (realignmentSquare Y) ≤
      ∑ j, w j * (Real.sqrt (∑ x, ‖p j x‖ ^ 2) * Real.sqrt (∑ y, ‖r j y‖ ^ 2)) := by
  set M := realignmentSquare Y with hMdef
  have hM : (Mᴴ * Mᴴᴴ).IsHermitian := isHermitian_mul_conjTranspose_self Mᴴ
  rw [DSB_trnorm M hM]
  refine le_of_le_of_eq (DSB_ccnr w hw (fun j => Sum.elim 0 (star (r j)))
    (fun j => Sum.elim (star (p j)) 0)
    (fun j => Real.sqrt (∑ y, ‖r j y‖ ^ 2)) (fun j => Real.sqrt (∑ x, ‖p j x‖ ^ 2))
    (fun j => ?_) (fun j => ?_) Mᴴ ?_ hM) (Finset.sum_congr rfl fun j _ => by ring)
  · simp [EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  · simp [EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  · ext i k
    rcases i with i | i <;> rcases k with k | k <;>
      simp [hMdef, realignmentSquare, hY, Matrix.sum_apply, mul_comm]

lemma DSB_rsmul {a b : ℕ} (Y : Bip a b) (t : ℝ) (k : ℕ) :
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

lemma DSB_alpha {a b : ℕ} (Y : Bip a b) (m : ℕ) (c : ℝ) (hc : 0 < c)
    (hle : QAlgorithms.traceNorm (realignmentSquare Y) ≤ c) :
    alpha (fun k : Fin m => rMoment (((c : ℂ))⁻¹ • Y) (k.val + 1)) ≤
      ENNReal.ofReal (QAlgorithms.traceNorm (realignmentSquare Y) / c) := by
  obtain ⟨σ, hσ0, htn, hmom⟩ := DSB_spec Y
  set e := Fintype.equivFin ((Fin a × Fin a) ⊕ (Fin b × Fin b))
  apply sInf_le
  refine ⟨_, fun t => σ (e.symm t) / c, ⟨fun i => ⟨div_nonneg (hσ0 _) hc.le, ?_⟩, fun k => ?_⟩, ?_⟩
  · rw [div_le_one hc]
    exact (Finset.single_le_sum (fun j _ => hσ0 j) (Finset.mem_univ _)).trans (htn ▸ hle)
  · simp only []
    rw [← Complex.ofReal_inv, DSB_rsmul, hmom, e.symm.sum_comp (fun i => (σ i / c) ^ (2 * (k.val + 1))),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_pow, ← pow_mul, div_eq_mul_inv, mul_comm, inv_pow]
  · rw [e.symm.sum_comp (fun i => σ i / c), ← Finset.sum_div, htn]

section DSB_S
variable {a b q : ℕ} (w : Fin q → ℝ) (A : Fin q → Matrix (Fin a) (Fin a) ℂ)
  (B : Fin q → Matrix (Fin b) (Fin b) ℂ)
  (hAB : ∀ j, QAlgorithms.IsDensityMatrix (A j) ∧ QAlgorithms.IsDensityMatrix (B j))

include hAB in
lemma DSB_mass : mass (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) = ∑ j, w j := by
  rw [mass, powerTrace, pow_one, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [trace_smul, Matrix.kronecker, trace_kronecker, (hAB j).1.2, (hAB j).2.2]
  simp

include hAB in
lemma DSB_margA : marginalA (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
    ∑ j, (w j : ℂ) • A j := by
  ext i i'
  have h : ∀ j, ∑ k, B j k k = 1 := fun j => (hAB j).2.2
  simp only [marginalA, Matrix.sum_apply, Matrix.smul_apply, kronecker, kroneckerMap_apply,
    smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.mul_sum, ← Finset.mul_sum, h, mul_one]

include hAB in
lemma DSB_margB : marginalB (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
    ∑ j, (w j : ℂ) • B j := by
  ext i i'
  have h : ∀ j, ∑ k, A j k k = 1 := fun j => (hAB j).1.2
  simp only [marginalB, Matrix.sum_apply, Matrix.smul_apply, kronecker, kroneckerMap_apply,
    smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.mul_sum, ← Finset.sum_mul, h, one_mul]

lemma DSB_real : realign (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
    ∑ j, (w j : ℂ) • Matrix.of (fun x y => A j x.1 x.2 * B j y.1 y.2) := by
  ext x y
  simp [realign, Matrix.sum_apply, kronecker]

include hAB in
lemma DSB_realc : realign (centered (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j))) =
    ∑ p : Fin q × Fin q, ((w p.1 * w p.2 / 2 : ℝ) : ℂ) •
      Matrix.of (fun x y => (A p.1 x.1 x.2 - A p.2 x.1 x.2) * (B p.1 y.1 y.2 - B p.2 y.1 y.2)) := by
  ext x y
  rw [centered, DSB_margA w A B hAB, DSB_margB w A B hAB, DSB_mass w A B hAB]
  simp only [realign, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply,
    smul_eq_mul, kronecker, kroneckerMap_apply]
  have := DSB_id w (fun j => A j x.1 x.2) (fun j => B j y.1 y.2)
  rw [this]
  push_cast
  ring

include hAB in
lemma DSB_purA : purityA (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
    ∑ x : Fin a × Fin a, ‖∑ j, (w j : ℂ) * A j x.1 x.2‖ ^ 2 := by
  rw [purityA, powerTrace, DSB_margA w A B hAB, DSB_tr_sq, Fintype.sum_prod_type]
  · simp [Matrix.sum_apply]
  · unfold Matrix.IsHermitian
    rw [conjTranspose_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [conjTranspose_smul, (hAB j).1.1.1.eq]
    simp

include hAB in
lemma DSB_purB : purityB (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
    ∑ y : Fin b × Fin b, ‖∑ j, (w j : ℂ) * B j y.1 y.2‖ ^ 2 := by
  rw [purityB, powerTrace, DSB_margB w A B hAB, DSB_tr_sq, Fintype.sum_prod_type]
  · simp [Matrix.sum_apply]
  · unfold Matrix.IsHermitian
    rw [conjTranspose_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [conjTranspose_smul, (hAB j).2.1.1.eq]
    simp

omit hAB in
lemma DSB_SA {d : ℕ} (C : Fin q → Matrix (Fin d) (Fin d) ℂ)
    (hC : ∀ j, QAlgorithms.IsDensityMatrix (C j)) (hw : ∀ j, 0 ≤ w j) :
    ∑ p : Fin q × Fin q, (w p.1 * w p.2 / 2) * ∑ x : Fin d × Fin d, ‖C p.1 x.1 x.2 - C p.2 x.1 x.2‖ ^ 2
      ≤ (∑ j, w j) ^ 2 - ∑ x : Fin d × Fin d, ‖∑ j, (w j : ℂ) * C j x.1 x.2‖ ^ 2 := by
  have e : ∑ p : Fin q × Fin q, (w p.1 * w p.2 / 2) *
      ∑ x : Fin d × Fin d, ‖C p.1 x.1 x.2 - C p.2 x.1 x.2‖ ^ 2 =
      (∑ j, w j) * (∑ j, w j * ∑ x : Fin d × Fin d, ‖C j x.1 x.2‖ ^ 2) -
        ∑ x : Fin d × Fin d, ‖∑ j, (w j : ℂ) * C j x.1 x.2‖ ^ 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have := fun x : Fin d × Fin d => DSB_idn w (fun j => C j x.1 x.2)
    simp only [Finset.mul_sum] at this
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
  rw [e]
  have hF : ∀ j, ∑ x : Fin d × Fin d, ‖C j x.1 x.2‖ ^ 2 ≤ 1 := fun j => by
    rw [Fintype.sum_prod_type]; exact DSB_frob (hC j).1 (hC j).2
  have h1 : ∑ j, w j * ∑ x : Fin d × Fin d, ‖C j x.1 x.2‖ ^ 2 ≤ ∑ j, w j :=
    Finset.sum_le_sum (fun j _ => by
      have := mul_le_mul_of_nonneg_left (hF j) (hw j); linarith)
  have h0 : 0 ≤ ∑ j, w j := Finset.sum_nonneg (fun j _ => hw j)
  have := mul_le_mul_of_nonneg_left h1 h0
  nlinarith

include hAB in
lemma DSB_p3 (hw : ∀ j, 0 ≤ w j) :
    QAlgorithms.traceNorm (realignmentSquare (centered (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j))))
      ≤ Real.sqrt (G (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j))) := by
  set c : Fin q × Fin q → ℝ := fun p => w p.1 * w p.2 / 2 with hc
  have hc0 : ∀ p, 0 ≤ c p := fun p => by
    simp only [hc]; have := mul_nonneg (hw p.1) (hw p.2); linarith
  have hb := DSB_bound _ c hc0 (fun p x => A p.1 x.1 x.2 - A p.2 x.1 x.2)
    (fun p y => B p.1 y.1 y.2 - B p.2 y.1 y.2) (DSB_realc w A B hAB)
  set FA : Fin q × Fin q → ℝ := fun p => ∑ x : Fin a × Fin a, ‖A p.1 x.1 x.2 - A p.2 x.1 x.2‖ ^ 2
  set FB : Fin q × Fin q → ℝ := fun p => ∑ y : Fin b × Fin b, ‖B p.1 y.1 y.2 - B p.2 y.1 y.2‖ ^ 2
  have hSA := DSB_SA w (fun j => A j) (fun j => (hAB j).1) hw
  have hSB := DSB_SA w (fun j => B j) (fun j => (hAB j).2) hw
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
  rw [G, DSB_mass w A B hAB, DSB_purA w A B hAB, DSB_purB w A B hAB]
  refine hb.trans (hcs.trans ?_)
  rw [Real.sqrt_mul (hA0.trans hSA)]
  exact mul_le_mul (Real.sqrt_le_sqrt hSA) (Real.sqrt_le_sqrt hSB) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

include hAB in
lemma DSB_p2 (hw : ∀ j, 0 ≤ w j) :
    QAlgorithms.traceNorm (realignmentSquare (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)))
      ≤ mass (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) := by
  refine (DSB_bound _ w hw (fun j x => A j x.1 x.2) (fun j y => B j y.1 y.2)
    (DSB_real w A B)).trans ?_
  rw [DSB_mass w A B hAB]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hA : Real.sqrt (∑ x : Fin a × Fin a, ‖A j x.1 x.2‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by
    rw [Fintype.sum_prod_type]; exact DSB_frob (hAB j).1.1 (hAB j).1.2)
  have hB : Real.sqrt (∑ y : Fin b × Fin b, ‖B j y.1 y.2‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by
    rw [Fintype.sum_prod_type]; exact DSB_frob (hAB j).2.1 (hAB j).2.2)
  have := mul_le_mul hA hB (Real.sqrt_nonneg _) zero_le_one
  have := mul_le_mul_of_nonneg_left this (hw j)
  simpa using this

end DSB_S

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (m : ℕ) (hm : 1 ≤ m) (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (X : Bip a b) (hX : QAlgorithms.Entanglement.IsSeparablePositive X) (ht : 0 < mass X) :
    alpha (fun k : Fin m => rMoment (((mass X)⁻¹ : ℂ) • X) (k.val+1)) ≤
      ENNReal.ofReal (QAlgorithms.traceNorm (realignmentSquare X)/mass X) ∧
    QAlgorithms.traceNorm (realignmentSquare X)/mass X ≤ 1 ∧
    (0<G X →
      alpha (fun k : Fin m => rMoment (((Real.sqrt (G X))⁻¹ : ℂ) • centered X) (k.val+1)) ≤
        ENNReal.ofReal (QAlgorithms.traceNorm (realignmentSquare (centered X))/Real.sqrt (G X)) ∧
      QAlgorithms.traceNorm (realignmentSquare (centered X))/Real.sqrt (G X) ≤ 1) := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := hX
  have h2 := DSB_p2 w A B hAB hw
  refine ⟨DSB_alpha _ m _ ht h2, (div_le_one ht).mpr h2, fun hG => ?_⟩
  have h3 := DSB_p3 w A B hAB hw
  have hs : 0 < Real.sqrt (G (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j))) := Real.sqrt_pos.mpr hG
  exact ⟨DSB_alpha _ m _ hs h3, (div_le_one hs).mpr h3⟩

end

