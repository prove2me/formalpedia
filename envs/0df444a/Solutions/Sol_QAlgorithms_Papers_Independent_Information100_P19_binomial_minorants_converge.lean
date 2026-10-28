-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.binomial_minorants_converge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:00:42.070188+00:00
-- url     : https://prove2.me/submissions/c1650c6a-a785-4771-bdc1-e5a4295cce22

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory
section BMC_g0
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma BMC_spec_nonneg {S : Matrix ι ι ℂ} (hS : S.PosSemidef) {x : ℝ} (hx : x ∈ spectrum ℝ S) :
    0 ≤ x := by
  rw [hS.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hS.eigenvalues_nonneg i

lemma BMC_sqrt_sq {S : Matrix ι ι ℂ} (hS : S.PosSemidef) : cfc Real.sqrt (S * S) = S := by
  have hsa : IsSelfAdjoint S := hS.1
  have h1 : S * S = cfc (fun x : ℝ => x * x) S := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) S, cfc_id' ℝ S]
  rw [h1, ← cfc_comp' Real.sqrt (fun x : ℝ => x * x) S]
  rw [cfc_congr (g := fun x : ℝ => x) (fun x hx => by
    simp only
    exact Real.sqrt_mul_self (BMC_spec_nonneg hS hx)), cfc_id' ℝ S]

lemma BMC_cfc_sqrt_psd {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    (cfc Real.sqrt P).PosSemidef ∧ cfc Real.sqrt P * cfc Real.sqrt P = P := by
  have hsa : IsSelfAdjoint P := hP.1
  constructor
  · rw [hP.1.cfc_eq]
    unfold IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply]
    refine (PosSemidef.diagonal ?_).mul_mul_conjTranspose_same _
    intro i
    simp only [Pi.zero_apply, Function.comp_apply]
    exact Complex.zero_le_real.mpr (Real.sqrt_nonneg _)
  · rw [← cfc_mul Real.sqrt Real.sqrt P]
    rw [cfc_congr (g := fun x : ℝ => x) (fun x hx => by
      simp only
      exact Real.mul_self_sqrt (BMC_spec_nonneg hP hx)), cfc_id' ℝ P]

end BMC_g0

section BMC_gen2
open Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma BMC_blk_psd {T : Matrix J J ℂ} (hT : T.PosSemidef) :
    (fromBlocks (0 : Matrix I I ℂ) 0 0 T).PosSemidef := by
  have h : fromBlocks (0 : Matrix I I ℂ) 0 0 T =
      (fromCols (0 : Matrix J I ℂ) 1)ᴴ * T * fromCols (0 : Matrix J I ℂ) 1 := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul,
      mul_fromCols, mul_fromCols]
    ext (i|i) (j|j) <;> simp
  rw [h]
  exact hT.conjTranspose_mul_mul_same _

lemma BMC_tn (R : Matrix I J ℂ) :
    QAlgorithms.traceNorm (fromBlocks (0 : Matrix I I ℂ) R 0 (0 : Matrix J J ℂ)) =
      (cfc Real.sqrt (Rᴴ * R)).trace.re := by
  unfold QAlgorithms.traceNorm
  obtain ⟨hT, hTT⟩ := BMC_cfc_sqrt_psd (posSemidef_conjTranspose_mul_self R)
  set T := cfc Real.sqrt (Rᴴ * R)
  have h1 : (fromBlocks (0 : Matrix I I ℂ) R 0 (0 : Matrix J J ℂ))ᴴ *
      fromBlocks (0 : Matrix I I ℂ) R 0 (0 : Matrix J J ℂ) =
      fromBlocks (0 : Matrix I I ℂ) 0 0 T * fromBlocks (0 : Matrix I I ℂ) 0 0 T := by
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, hTT]
    simp
  rw [h1, BMC_sqrt_sq (BMC_blk_psd hT)]
  simp [Matrix.trace, Fintype.sum_sum_type]

end BMC_gen2

section BMC_cc
open Matrix Finset WithLp

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma BMC_tr_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℂ)) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal]
  simp

end BMC_cc

namespace QAlgorithms.Papers.Independent.Information100.P19
open Matrix
section BMC_gen
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma BMC_eigSpec {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    eigenSpectrum H = Finset.univ.val.map hH.eigenvalues := by
  rw [eigenSpectrum, hH.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  congr 1

lemma BMC_tr_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A ^ 2).trace = ∑ i, ((hA.eigenvalues i : ℂ)) ^ 2 := by
  have h := hA.spectral_theorem
  conv_lhs => rw [h]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, diagonal_pow, trace_diagonal]
  simp

end BMC_gen
lemma BMC_frob {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htr : A.trace = 1) : ∑ i, ∑ k, ‖A i k‖ ^ 2 ≤ 1 := by
  have hH := hA.1
  have e1 : ((A ^ 2).trace).re = ∑ i, ∑ k, ‖A i k‖ ^ 2 := by
    have : A ^ 2 = A * Aᴴ := by rw [hH.eq, sq]
    rw [this]
    simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
  rw [← e1, BMC_tr_sq hH]
  have hl : ∀ i, 0 ≤ hH.eigenvalues i := hA.eigenvalues_nonneg
  have hs : ∑ i, hH.eigenvalues i = 1 := by
    have := congrArg Complex.re (hH.trace_eq_sum_eigenvalues)
    rw [htr] at this; simpa using this.symm
  have : ∑ i, hH.eigenvalues i ^ 2 ≤ (∑ i, hH.eigenvalues i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hl i)
  rw [hs] at this
  simpa [← Complex.ofReal_pow] using this

def BMC_c (a : ℕ) : ℝ := ((Nat.factorial (2*a) : ℝ) / (4^a * (Nat.factorial a : ℝ)^2))

theorem BMC_bin (m : ℕ) (x : ℝ) :
    binomial m x = x * ∑ a ∈ Finset.range m, BMC_c a * (1-x)^a := rfl

theorem BMC_c_nonneg (a : ℕ) : 0 ≤ BMC_c a := by unfold BMC_c; positivity

theorem BMC_c_zero : BMC_c 0 = 1 := by simp [BMC_c]

theorem BMC_c_succ (k : ℕ) : BMC_c (k+1) * ((k:ℝ)+1) = BMC_c k * ((k:ℝ) + 1/2) := by
  unfold BMC_c
  rw [show 2 * (k+1) = (2*k+1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ k]
  push_cast
  have h1 : (0:ℝ) < (Nat.factorial (2*k) : ℝ) := by positivity
  have h2 : (0:ℝ) < (Nat.factorial k : ℝ) := by positivity
  field_simp
  ring

def BMC_T (n : ℕ) : ℝ := ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)), BMC_c p.1 * BMC_c p.2

theorem BMC_T_eq (n : ℕ) : BMC_T n = 1 := by
  induction n with
  | zero => simp [BMC_T, BMC_c_zero]
  | succ n ih =>
    have hsym : ∀ N, ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)), (p.1:ℝ) * (BMC_c p.1 * BMC_c p.2)
        = ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)), (p.2:ℝ) * (BMC_c p.1 * BMC_c p.2) := by
      intro N
      rw [← Finset.Nat.sum_antidiagonal_swap]
      apply Finset.sum_congr rfl
      intro p _
      simp only [Prod.fst_swap, Prod.snd_swap]
      ring
    have hsum : ∀ N, ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)), ((p.1:ℝ) + p.2) * (BMC_c p.1 * BMC_c p.2)
        = N * BMC_T N := by
      intro N
      rw [BMC_T, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [← hp]; push_cast; ring
    have h2 : ∀ N, 2 * ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)), (p.1:ℝ) * (BMC_c p.1 * BMC_c p.2)
        = N * BMC_T N := by
      intro N
      rw [← hsum N, two_mul]
      nth_rewrite 2 [hsym N]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _; ring
    have hstep : ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (n+1) : Finset (ℕ × ℕ)), (p.1:ℝ) * (BMC_c p.1 * BMC_c p.2)
        = ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)), ((p.1:ℝ) + 1/2) * (BMC_c p.1 * BMC_c p.2) := by
      rw [Finset.Nat.sum_antidiagonal_succ]
      simp only [Nat.cast_zero, zero_mul, zero_add]
      apply Finset.sum_congr rfl
      intro p _
      push_cast
      have := BMC_c_succ p.1
      linear_combination (BMC_c p.2) * this
    have h3 : ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)), ((p.1:ℝ) + 1/2) * (BMC_c p.1 * BMC_c p.2)
        = (1/2) * (n * BMC_T n) + (1/2) * BMC_T n := by
      rw [← h2 n, BMC_T, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _; ring
    have h4 := h2 (n+1)
    rw [hstep, h3, ih] at h4
    push_cast at h4
    have : ((n:ℝ) + 1) * BMC_T (n+1) = (n:ℝ) + 1 := by linarith
    have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have := mul_left_cancel₀ hn.ne' (this.trans (mul_one _).symm)
    exact this

theorem BMC_c_le (a : ℕ) : BMC_c a ≤ 1 := by
  have h := BMC_T_eq a
  rw [BMC_T] at h
  have hmem : ((0:ℕ), a) ∈ (Finset.HasAntidiagonal.antidiagonal a : Finset (ℕ × ℕ)) :=
    Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add a)
  have := Finset.single_le_sum (f := fun p : ℕ × ℕ => BMC_c p.1 * BMC_c p.2)
      (fun p _ => mul_nonneg (BMC_c_nonneg _) (BMC_c_nonneg _)) hmem
  simp only at this
  rw [BMC_c_zero, one_mul] at this
  linarith

theorem BMC_summ {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) : Summable (fun n => BMC_c n * u^n) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (BMC_c_nonneg n) (pow_nonneg h0 n))
    (fun n => ?_) (summable_geometric_of_lt_one h0 h1)
  have := pow_nonneg h0 n
  nlinarith [BMC_c_le n]

theorem BMC_sq {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    (∑' n, BMC_c n * u^n) * (∑' n, BMC_c n * u^n) = (1 - u)⁻¹ := by
  have hs := BMC_summ h0 h1
  have hn : Summable (fun n => ‖BMC_c n * u^n‖) := by
    refine hs.congr fun n => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (BMC_c_nonneg n) (pow_nonneg h0 n))]
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hn hn, ← tsum_geometric_of_lt_one h0 h1]
  congr 1
  ext n
  have : ∀ p ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)), BMC_c p.1 * u ^ p.1 * (BMC_c p.2 * u ^ p.2)
      = (BMC_c p.1 * BMC_c p.2) * u^n := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [← hp, pow_add]; ring
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← BMC_T, BMC_T_eq, one_mul]

theorem BMC_scalar (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    (∀ m : ℕ, binomial m x ≤ Real.sqrt x) ∧
      (∀ m : ℕ, binomial m x ≤ binomial (m+1) x) ∧
      Tendsto (fun m => binomial m x) atTop (nhds (Real.sqrt x)) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hmono : ∀ m : ℕ, binomial m x ≤ binomial (m+1) x := by
    intro m
    rw [BMC_bin, BMC_bin, Finset.sum_range_succ, mul_add]
    have := mul_nonneg hx0 (mul_nonneg (BMC_c_nonneg m) (pow_nonneg (by linarith : (0:ℝ) ≤ 1 - x) m))
    linarith
  rcases hx0.lt_or_eq with hpos | hzero
  · have hu0 : 0 ≤ 1 - x := by linarith
    have hu1 : 1 - x < 1 := by linarith
    set L := ∑' n, BMC_c n * (1-x)^n with hL
    have hsq := BMC_sq hu0 hu1
    rw [← hL, sub_sub_cancel] at hsq
    have hL0 : 0 ≤ L := tsum_nonneg fun n => mul_nonneg (BMC_c_nonneg n) (pow_nonneg hu0 n)
    have hxL : x * L = Real.sqrt x := by
      rw [← Real.sqrt_sq (mul_nonneg hx0 hL0), mul_pow, sq, sq L, hsq,
        mul_inv_cancel_right₀ hpos.ne']
    refine ⟨fun m => ?_, hmono, ?_⟩
    · rw [← hxL, BMC_bin]
      apply mul_le_mul_of_nonneg_left _ hx0
      exact (BMC_summ hu0 hu1).sum_le_tsum _ fun n _ =>
        mul_nonneg (BMC_c_nonneg n) (pow_nonneg hu0 n)
    · rw [← hxL]
      exact ((BMC_summ hu0 hu1).hasSum.tendsto_sum_nat).const_mul x
  · subst hzero
    refine ⟨fun m => by simp [BMC_bin], hmono, ?_⟩
    simp [BMC_bin]


theorem BMC_lagC {I : Type*} [Fintype I] (u v : I → ℂ) :
    ∑ i, ∑ j, (u i * v j - u j * v i) * conj (u i * v j - u j * v i)
      = 2 * ((∑ i, u i * conj (u i)) * (∑ j, v j * conj (v j))
        - (∑ i, conj (u i) * v i) * conj (∑ i, conj (u i) * v i)) := by
  have e1 : ∀ i j, (u i * v j - u j * v i) * conj (u i * v j - u j * v i)
      = (u i * conj (u i)) * (v j * conj (v j)) + (u j * conj (u j)) * (v i * conj (v i))
        - (conj (u i) * v i) * (u j * conj (v j)) - (conj (u j) * v j) * (u i * conj (v i)) := by
    intro i j; simp only [map_sub, map_mul]; ring
  simp_rw [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => (u j * conj (u j)) * (v i * conj (v i))),
    Finset.sum_comm (f := fun i j => (conj (u j) * v j) * (u i * conj (v i)))]
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [map_mul, Complex.conj_conj]
  ring

theorem BMC_lag {I : Type*} [Fintype I] (u v : I → ℂ) :
    ∑ i, ∑ j, Complex.normSq (u i * v j - u j * v i)
      = 2 * ((∑ i, Complex.normSq (u i)) * (∑ j, Complex.normSq (v j))
        - Complex.normSq (∑ i, conj (u i) * v i)) := by
  apply Complex.ofReal_injective
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self]
  have := BMC_lagC u v
  simp only [mul_comm (conj _) _] at this ⊢
  rw [this]

theorem BMC_hs {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ∑ x, ∑ y, Complex.normSq ((Aᴴ * A) x y) = ((Aᴴ * A) * (Aᴴ * A)).trace.re := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self A
  rw [Matrix.trace, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro y _
  have : (Aᴴ * A) y x = conj ((Aᴴ * A) x y) := by
    rw [← hH.apply x y, Complex.star_def, Complex.conj_conj]
  rw [this, Complex.mul_conj]; simp

theorem BMC_prod {I K L : Type*} [Fintype I] [Fintype K] [Fintype L] (T : L → I → K → ℂ)
    (htr : ∑ i, ∑ k, ∑ l, Complex.normSq (T l i k) = 1)
    (hpur : ∑ i, ∑ j, Complex.normSq (∑ k, ∑ l, conj (T l i k) * T l j k) = 1)
    (i j : I) (k k' : K) :
    ∑ l, conj (T l i k) * T l j k' = (∑ k'', ∑ l, conj (T l i k'') * T l j k'') *
      (∑ i', ∑ l, conj (T l i' k) * T l i' k') := by
  classical
  let W : Matrix (K × L) I ℂ := fun α x => T α.2 x α.1
  have hM : ∀ x y, (Wᴴ * W) x y = ∑ k, ∑ l, conj (T l x k) * T l y k := by
    intro x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Complex.star_def]
    rfl
  have hN : ∑ α : K × L, ∑ x, Complex.normSq (W α x) = 1 := by
    rw [← htr, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    rw [Fintype.sum_prod_type]
  have hpur' : ((Wᴴ * W) * (Wᴴ * W)).trace.re = 1 := by
    rw [← BMC_hs, ← hpur]
    simp only [hM]
  have hG : ∑ α, ∑ β, Complex.normSq (∑ x, conj (W α x) * W β x) = 1 := by
    have e : ((Wᴴ * W) * (Wᴴ * W)).trace = ((Wᴴᴴ * Wᴴ) * (Wᴴᴴ * Wᴴ)).trace := by
      rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [← hpur', e, ← BMC_hs]
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro β _
    rw [← Complex.normSq_conj]
    congr 1
    simp [Matrix.mul_apply, Complex.star_def, map_sum]
  have hsum : ∑ α, ∑ β, ∑ x, ∑ y, Complex.normSq (W α x * W β y - W α y * W β x) = 0 := by
    simp_rw [BMC_lag, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul_sum, hN, hG]
    norm_num
  have hnn : ∀ α β x y, 0 ≤ Complex.normSq (W α x * W β y - W α y * W β x) :=
    fun _ _ _ _ => Complex.normSq_nonneg _
  have hminor : ∀ α β x y, W α x * W β y = W α y * W β x := by
    intro α β x y
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun α _ => Finset.sum_nonneg fun β _ =>
      Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hnn α β x y)).1 hsum α
      (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun β _ =>
      Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hnn α β x y)).1 h1 β
      (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
      Finset.sum_nonneg fun y _ => hnn α β x y)).1 h2 x (Finset.mem_univ _)
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hnn α β x y)).1 h3 y
      (Finset.mem_univ _)
    exact sub_eq_zero.1 (Complex.normSq_eq_zero.1 h4)
  have hone : ∑ α : K × L, ∑ x, conj (W α x) * W α x = 1 := by
    have : ∀ α : K × L, ∑ x, conj (W α x) * W α x = ((∑ x, Complex.normSq (W α x) : ℝ) : ℂ) := by
      intro α; push_cast; simp only [Complex.normSq_eq_conj_mul_self]
    simp_rw [this]
    rw [← Complex.ofReal_sum, hN, Complex.ofReal_one]
  have hfirst : (∑ k'', ∑ l, conj (T l i k'') * T l j k'') = ∑ α : K × L, conj (W α i) * W α j := by
    rw [Fintype.sum_prod_type]
  rw [hfirst, Finset.sum_mul_sum]
  have hterm : ∀ α : K × L, ∀ i', ∑ l, conj (W α i) * W α j * (conj (T l i' k) * T l i' k')
      = ∑ l, (conj (W α i') * W α i') * (conj (T l i k) * T l j k') := by
    intro α i'
    apply Finset.sum_congr rfl
    intro l _
    have m1 := hminor α (k', l) j i'
    have m2 := hminor α (k, l) i i'
    simp only [W] at m1 m2
    calc conj (T α.2 i α.1) * T α.2 j α.1 * (conj (T l i' k) * T l i' k')
        = conj (T α.2 i α.1 * T l i' k) * (T α.2 j α.1 * T l i' k') := by
          simp only [map_mul]; ring
      _ = conj (T α.2 i' α.1 * T l i k) * (T α.2 i' α.1 * T l j k') := by rw [m1, m2]
      _ = _ := by simp only [map_mul]; ring
  simp_rw [Finset.mul_sum] at *
  simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul, hone, one_mul]


theorem BMC_lim1 (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    Tendsto (fun m => binomial m (s^2)) atTop (nhds s) := by
  have := (BMC_scalar (s^2) ⟨sq_nonneg s, by nlinarith⟩).2.2
  rwa [Real.sqrt_sq h0] at this

theorem BMC_ms (S : Multiset ℝ) (h : ∀ s ∈ S, 0 ≤ s ∧ s ≤ 1) :
    Tendsto (fun m => (S.map fun s => binomial m (s^2)).sum) atTop (nhds S.sum) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have ha := h a (Multiset.mem_cons_self a S)
    exact (BMC_lim1 a ha.1 ha.2).add (ih fun s hs => h s (Multiset.mem_cons_of_mem hs))

section BMC_mat
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem BMC_svb (R : Matrix I J ℂ) :
    ∀ s ∈ singularSpectrum R, 0 ≤ s ∧ s^2 ≤ (R * Rᴴ).trace.re := by
  intro s hs
  have hH := Matrix.isHermitian_mul_conjTranspose_self R
  have hP := Matrix.posSemidef_self_mul_conjTranspose R
  rw [singularSpectrum, BMC_eigSpec hH, Multiset.map_map, Multiset.mem_map] at hs
  obtain ⟨i, _, rfl⟩ := hs
  simp only [Function.comp_apply]
  have hl : ∀ j, 0 ≤ hH.eigenvalues j := hP.eigenvalues_nonneg
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  rw [Real.sq_sqrt (hl i)]
  have htr : (R * Rᴴ).trace.re = ∑ j, hH.eigenvalues j := by
    rw [hH.trace_eq_sum_eigenvalues]; simp
  rw [htr]
  exact Finset.single_le_sum (fun j _ => hl j) (Finset.mem_univ i)

theorem BMC_tnS (R : Matrix I J ℂ) :
    QAlgorithms.traceNorm (Matrix.fromBlocks (0 : Matrix I I ℂ) R 0 (0 : Matrix J J ℂ))
      = (singularSpectrum R).sum := by
  rw [BMC_tn, BMC_tr_cfc (Matrix.isHermitian_conjTranspose_mul_self R), Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hc := Matrix.charpoly_mul_comm' R Rᴴ
  have hr := congrArg Polynomial.roots hc
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hr
  have hs := congrArg (fun s : Multiset ℂ => (s.map (fun z => Real.sqrt z.re)).sum) hr
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton, Complex.zero_re, Real.sqrt_zero,
    smul_zero, zero_add] at hs
  rw [singularSpectrum, eigenSpectrum, Multiset.map_map]
  rw [show (Real.sqrt ∘ Complex.re) = (fun z : ℂ => Real.sqrt z.re) from rfl, hs,
    (Matrix.isHermitian_conjTranspose_mul_self R).roots_charpoly_eq_eigenvalues, Multiset.map_map,
    Finset.sum_eq_multiset_sum]
  rfl

end BMC_mat

theorem BMC_tn_smul {n : Type*} [Fintype n] [DecidableEq n] (t : ℝ) (M : Matrix n n ℂ) :
    QAlgorithms.traceNorm ((t:ℂ) • M) = |t| * QAlgorithms.traceNorm M := by
  unfold QAlgorithms.traceNorm
  have e : ((t:ℂ) • M)ᴴ * ((t:ℂ) • M) = (t^2) • (Mᴴ * M) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, smul_eq_mul,
      Complex.real_smul, star_mul', Complex.star_def, Complex.conj_ofReal, Finset.mul_sum]
    push_cast
    apply Finset.sum_congr rfl; intros; ring
  rw [e]
  have hA : IsSelfAdjoint (Mᴴ * M) := Matrix.isHermitian_conjTranspose_mul_self M
  rw [← cfc_comp_smul (t^2) Real.sqrt (Mᴴ * M)]
  rw [cfc_congr (g := fun x => Real.sqrt (t^2) * Real.sqrt x) (fun x _ => by
    simp only [Function.comp_apply, smul_eq_mul]; exact Real.sqrt_mul (sq_nonneg t) x)]
  rw [cfc_const_mul (Real.sqrt (t^2)) Real.sqrt (Mᴴ * M), Matrix.trace_smul, Real.sqrt_sq_eq_abs, Complex.smul_re, smul_eq_mul]

theorem BMC_rs_smul {a b : ℕ} (c : ℂ) (Z : Bip a b) :
    realignmentSquare (c • Z) = c • realignmentSquare Z := by
  unfold realignmentSquare
  rw [Matrix.fromBlocks_smul, smul_zero, smul_zero, smul_zero]
  rfl

theorem BMC_rm_smul {a b : ℕ} (t : ℝ) (Z : Bip a b) :
    rMoment ((t:ℂ) • Z) 1 = t^2 * rMoment Z 1 := by
  have e : realign ((t:ℂ) • Z) = (t:ℂ) • realign Z := rfl
  simp only [rMoment, powerTrace, pow_one, e, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_smul, smul_eq_mul, Complex.star_def,
    Complex.conj_ofReal]
  rw [show (t:ℂ) * (t:ℂ) = ((t^2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]

theorem BMC_conv {a b : ℕ} (Y : Bip a b) (h : rMoment Y 1 ≤ 1) :
    Tendsto (fun m => ((singularSpectrum (realign Y)).map (fun s => binomial m (s^2))).sum)
      atTop (nhds (QAlgorithms.traceNorm (realignmentSquare Y))) := by
  rw [show realignmentSquare Y = Matrix.fromBlocks 0 (realign Y) 0 0 from rfl, BMC_tnS]
  apply BMC_ms
  intro s hs
  obtain ⟨h0, h1⟩ := BMC_svb _ s hs
  have : (realign Y * (realign Y)ᴴ).trace.re = rMoment Y 1 := by simp [rMoment, powerTrace]
  rw [this] at h1
  exact ⟨h0, by nlinarith⟩

theorem BMC_trace1 {a b : ℕ} (X : Bip a b) (hX : X.PosSemidef) (hm : mass X = 1) :
    X.trace = 1 := by
  have hre : X.trace.re = 1 := by rw [← hm, mass, powerTrace, pow_one]
  have h := hX.1.trace_eq_sum_eigenvalues
  refine Complex.ext (by simpa using hre) ?_
  rw [h]; simp

theorem BMC_rm1 {a b : ℕ} (X : Bip a b) (hX : X.PosSemidef) (hm : mass X = 1) :
    rMoment X 1 ≤ 1 := by
  have hf := BMC_frob hX (BMC_trace1 X hX hm)
  have e1 : rMoment X 1 = ∑ p, ∑ q, ‖realign X p q‖^2 := by
    simp only [rMoment, powerTrace, pow_one, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.re_sum]
    apply Finset.sum_congr rfl; intro p _; apply Finset.sum_congr rfl; intro q _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
  rw [e1]
  convert hf using 1
  simp only [Fintype.sum_prod_type, realign]
  apply Finset.sum_congr rfl; intro i1 _
  rw [Finset.sum_comm]

theorem BMC_hs2 {n : Type*} [Fintype n] (M : Matrix n n ℂ) (h : ∀ x y, M y x = conj (M x y)) :
    ∑ x, ∑ y, Complex.normSq (M x y) = (M * M).trace.re := by
  rw [Matrix.trace, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [h x y, Complex.mul_conj]; simp

theorem BMC_G0 {a b : ℕ} (X : Bip a b) (hX : X.PosSemidef) (hm : mass X = 1) (hG : G X = 0) :
    centered X = 0 := by
  obtain ⟨hS, hSS⟩ := BMC_cfc_sqrt_psd hX
  set S := cfc Real.sqrt X
  have hXS : ∀ p q, X p q = ∑ l, conj (S l p) * S l q := by
    intro p q
    have : X = Sᴴ * S := by rw [hS.1.eq, hSS]
    rw [this, Matrix.mul_apply]
    simp [Complex.star_def]
  have htrX : ∑ i : Fin a, ∑ k : Fin b, ∑ l, Complex.normSq (S l (i,k)) = 1 := by
    have h1 : X.trace.re = 1 := by rw [← hm, mass, powerTrace, pow_one]
    rw [← h1, Matrix.trace, Complex.re_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro k _
    rw [Matrix.diag, hXS, Complex.re_sum]
    apply Finset.sum_congr rfl; intro l _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have hherm : ∀ p q, X q p = conj (X p q) := fun p q => by
    rw [← hX.1.apply p q, Complex.star_def, Complex.conj_conj]
  have hMA : ∀ i j, marginalA X i j = ∑ k, ∑ l, conj (S l (i,k)) * S l (j,k) := fun i j => by
    simp only [marginalA, hXS]
  have hMB : ∀ k k', marginalB X k k' = ∑ i, ∑ l, conj (S l (i,k)) * S l (i,k') := fun k k' => by
    simp only [marginalB, hXS]
  have hpA : purityA X = ∑ i, ∑ j, Complex.normSq (marginalA X i j) := by
    rw [purityA, powerTrace, sq, BMC_hs2]
    intro x y
    simp only [marginalA, map_sum]
    exact Finset.sum_congr rfl fun k _ => hherm _ _
  have hpB : purityB X = ∑ i, ∑ j, Complex.normSq (marginalB X i j) := by
    rw [purityB, powerTrace, sq, BMC_hs2]
    intro x y
    simp only [marginalB, map_sum]
    exact Finset.sum_congr rfl fun k _ => hherm _ _
  rw [G, hm] at hG
  have key : ∀ i j k k', X (i,k) (j,k') = marginalA X i j * marginalB X k k' := by
    rcases mul_eq_zero.1 hG with h | h
    · have hpur : ∑ i, ∑ j, Complex.normSq (∑ k, ∑ l, conj (S l (i,k)) * S l (j,k)) = 1 := by
        simp_rw [← hMA]; rw [← hpA]; linarith
      intro i j k k'
      rw [hXS, hMA, hMB]
      exact BMC_prod (fun l i k => S l (i,k)) htrX hpur i j k k'
    · have htr' : ∑ k : Fin b, ∑ i : Fin a, ∑ l, Complex.normSq (S l (i,k)) = 1 := by
        rw [Finset.sum_comm]; exact htrX
      have hpur : ∑ k, ∑ k', Complex.normSq (∑ i, ∑ l, conj (S l (i,k)) * S l (i,k')) = 1 := by
        simp_rw [← hMB]; rw [← hpB]; linarith
      intro i j k k'
      rw [hXS, hMA, hMB, mul_comm]
      exact BMC_prod (fun l k i => S l (i,k)) htr' hpur k k' i j
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [centered, hm, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.ofReal_one, one_smul]
  rw [key]; ring

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution  :
    (∀ x ∈ Set.Icc (0:ℝ) 1, (∀ m : ℕ, 1 ≤ m → binomial m x ≤ Real.sqrt x) ∧
      (∀ m : ℕ, 1 ≤ m → binomial m x ≤ binomial (m+1) x) ∧
      Tendsto (fun m => binomial m x) atTop (nhds (Real.sqrt x))) ∧
    (∀ N : ℕ, ∀ s : Fin N → ℝ, (∀ i, s i ∈ Set.Icc (0:ℝ) 1) →
      Tendsto (fun m => ∑ i, binomial m (s i^2)) atTop (nhds (∑ i, s i))) ∧
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.PosSemidef → mass X=1 →
      Tendsto (fun m => ((singularSpectrum (realign X)).map
        (fun s => binomial m (s^2))).sum) atTop (nhds (QAlgorithms.traceNorm (realignmentSquare X))) ∧
      (G X=0 → centered X=0) ∧
      (G X<rMoment (centered X) 1 → defect 1 X<0) ∧
      (0<G X → rMoment (centered X) 1 ≤ G X → Tendsto (fun m => ((singularSpectrum
        (realign (((Real.sqrt (G X))⁻¹ : ℂ) • centered X))).map
          (fun s => binomial m (s^2))).sum) atTop
            (nhds (QAlgorithms.traceNorm (realignmentSquare (centered X))/Real.sqrt (G X))))) := by
  refine ⟨fun x hx => ?_, fun N s hs => ?_, fun a b _ _ X hX hm => ⟨?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨h1, h2, h3⟩ := BMC_scalar x hx
    exact ⟨fun m _ => h1 m, fun m _ => h2 m, h3⟩
  · exact tendsto_finset_sum _ fun i _ => BMC_lim1 (s i) (hs i).1 (hs i).2
  · exact BMC_conv X (BMC_rm1 X hX hm)
  · exact BMC_G0 X hX hm
  · intro h
    show G X - rMoment (centered X) 1 < 0
    linarith
  · intro hG hle
    have hs : 0 < Real.sqrt (G X) := Real.sqrt_pos.2 hG
    rw [← Complex.ofReal_inv]
    have hlim := BMC_conv ((((Real.sqrt (G X))⁻¹ : ℝ) : ℂ) • centered X) (by
      rw [BMC_rm_smul, inv_pow, Real.sq_sqrt hG.le]
      rw [inv_mul_le_iff₀ hG]; linarith)
    rw [BMC_rs_smul, BMC_tn_smul, abs_of_pos (inv_pos.2 hs), inv_mul_eq_div] at hlim
    exact hlim

