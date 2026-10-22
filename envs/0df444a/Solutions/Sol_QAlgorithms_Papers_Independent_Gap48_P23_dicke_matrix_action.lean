-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.dicke_matrix_action
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:45:18.383752+00:00
-- url     : https://prove2.me/submissions/b8cee6b9-6175-47ab-a0d3-153d19b72556

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)


def g74g_mu (l : ℕ) (v : Fin 2 → ℂ) : Fin (l+1) → ℂ :=
  fun k => (Real.sqrt (l.choose k.val : ℝ) : ℂ) * v 0 ^ (l - k.val) * v 1 ^ k.val

theorem g74g_coef_real (l j r s : ℕ) (hj : j ≤ l) (hr : r ≤ l - j) (hs : s ≤ j) :
    Real.sqrt ((Nat.factorial j : ℝ) * Nat.factorial (l - j) * Nat.factorial (l - r - s) *
      Nat.factorial (l - (l - r - s))) * Real.sqrt (l.choose (l - r - s) : ℝ) =
    Real.sqrt (l.choose j : ℝ) * (l-j).choose r * j.choose s *
      ((Nat.factorial r : ℝ) * Nat.factorial (l - j - r) * Nat.factorial s *
        Nat.factorial (j - s)) := by
  have hk : l - r - s ≤ l := by omega
  set k := l - r - s
  have e1 := Nat.choose_mul_factorial_mul_factorial hr
  have e2 := Nat.choose_mul_factorial_mul_factorial hs
  have e3 := Nat.choose_mul_factorial_mul_factorial hk
  have e4 := Nat.choose_mul_factorial_mul_factorial hj
  set G : ℝ := (Nat.factorial j : ℝ) * Nat.factorial (l - j) with hG
  have hGpos : 0 < G := by positivity
  have hK : (0:ℝ) < (Nat.factorial k : ℝ) * Nat.factorial (l - k) := by positivity
  -- RHS scalar
  have hR : ((l-j).choose r : ℝ) * j.choose s * ((Nat.factorial r : ℝ) * Nat.factorial (l - j - r) *
      Nat.factorial s * Nat.factorial (j - s)) = G := by
    rw [hG, ← e1, ← e2]; push_cast; ring
  rw [show Real.sqrt (l.choose j : ℝ) * ((l-j).choose r : ℝ) * (j.choose s : ℝ) *
      ((Nat.factorial r : ℝ) * Nat.factorial (l - j - r) * Nat.factorial s * Nat.factorial (j - s)) =
      Real.sqrt (l.choose j : ℝ) * (((l-j).choose r : ℝ) * (j.choose s : ℝ) *
      ((Nat.factorial r : ℝ) * Nat.factorial (l - j - r) * Nat.factorial s * Nat.factorial (j - s))) by ring, hR]
  rw [show (Nat.factorial j : ℝ) * Nat.factorial (l - j) * Nat.factorial k * Nat.factorial (l - k) =
      G * ((Nat.factorial k : ℝ) * Nat.factorial (l - k)) by rw [hG]; ring]
  have hCk : (l.choose k : ℝ) = (Nat.factorial l : ℝ) / ((Nat.factorial k : ℝ) * Nat.factorial (l - k)) := by
    rw [← e3]; push_cast; field_simp
  have hCj : (l.choose j : ℝ) = (Nat.factorial l : ℝ) / G := by
    rw [hG, ← e4]; push_cast; field_simp
  rw [hCk, hCj, ← Real.sqrt_mul (by positivity)]
  rw [show G * (↑k.factorial * ↑(l - k).factorial) * (↑l.factorial / (↑k.factorial * ↑(l - k).factorial))
      = (↑l.factorial / G) * G^2 by field_simp]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hGpos.le]

theorem g74g_mulVec (l : ℕ) (M : Op (Fin 2)) (v : Fin 2 → ℂ) :
    (polynomialIrrep l M) *ᵥ (g74g_mu l v) = g74g_mu l (M *ᵥ v) := by
  funext j
  have hJ : j.val ≤ l := by omega
  set J := j.val with hJdef
  set f : ℕ → ℕ → ℂ := fun k r => if r + J ≤ l ∧ r + k ≤ l ∧ l ≤ J + k + r then
    (Real.sqrt ((Nat.factorial J : ℝ) * Nat.factorial (l - J) * Nat.factorial k *
      Nat.factorial (l - k)) : ℂ) *
      (M 0 0 ^ r * M 0 1 ^ (l - J - r) * M 1 0 ^ (l - k - r) * M 1 1 ^ (J + k + r - l) /
          ((Nat.factorial r : ℂ) * Nat.factorial (l - J - r) *
            Nat.factorial (l - k - r) * Nat.factorial (J + k + r - l))) *
      ((Real.sqrt (l.choose k : ℝ) : ℂ) * v 0 ^ (l - k) * v 1 ^ k) else 0 with hf
  have step1 : ((polynomialIrrep l M) *ᵥ (g74g_mu l v)) j =
      ∑ k ∈ Finset.range (l+1), ∑ r ∈ Finset.range (l+1), f k r := by
    simp only [Matrix.mulVec, dotProduct, polynomialIrrep, g74g_mu]
    rw [← Fin.sum_univ_eq_sum_range (fun k => ∑ r ∈ Finset.range (l+1), f k r)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hf]
    split_ifs with h
    · rfl
    · simp
  rw [step1, Finset.sum_comm]
  rw [← Finset.sum_subset (s₁ := Finset.range (l - J + 1)) (s₂ := Finset.range (l+1))]
  rotate_left
  · intro r; simp only [Finset.mem_range]; omega
  · intro r _ hr
    simp only [Finset.mem_range] at hr
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [hf]; rw [if_neg (by omega)]
  -- RHS
  simp only [g74g_mu, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [add_pow, add_pow]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.range (J+1))]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  have himg : ∀ s ∈ Finset.range (J+1), ∀ t ∈ Finset.range (J+1),
      l - r - s = l - r - t → s = t := by
    intro s hs t ht h; simp only [Finset.mem_range] at hs ht; omega
  rw [← Finset.sum_subset (s₁ := (Finset.range (J+1)).image (fun s => l - r - s))
    (s₂ := Finset.range (l+1)), Finset.sum_image himg]
  rotate_left
  · intro k; simp only [Finset.mem_image, Finset.mem_range]; omega
  · intro k _ hk
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hk
    simp only [hf]
    rw [if_neg]
    intro h
    exact hk (l - r - k) (by omega) (by omega)
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hs' : s ≤ J := by omega
  have hr' : r ≤ l - J := by omega
  simp only [hf]
  rw [if_pos (by omega)]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) (g74g_coef_real l J r s hJ hr' hs')
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hc
  rw [show l - (l - r - s) - r = s by omega, show J + (l - r - s) + r - l = J - s by omega,
    show l - (l - r - s) = r + s by omega,
    show l - r - s = (l - J - r) + (J - s) by omega]
  rw [show l - (l - r - s) = r + s by omega, show l - r - s = (l - J - r) + (J - s) by omega] at hc
  have hden : ((Nat.factorial r : ℂ) * Nat.factorial (l - J - r) * Nat.factorial s *
      Nat.factorial (J - s)) ≠ 0 := by positivity
  rw [mul_pow, mul_pow, mul_pow, mul_pow, pow_add, pow_add]
  field_simp
  linear_combination (M 0 0 ^ r * M 0 1 ^ (l - J - r) * M 1 0 ^ s * M 1 1 ^ (J - s) *
    (v 0 ^ r * v 0 ^ s) * (v 1 ^ (l - J - r) * v 1 ^ (J - s))) * hc

theorem g74g_ext (l : ℕ) (X Y : Op (Fin (l+1)))
    (h : ∀ v : Fin 2 → ℂ, X *ᵥ g74g_mu l v = Y *ᵥ g74g_mu l v) : X = Y := by
  ext j k
  have hrow : ∀ t : ℂ, ∑ i : Fin (l+1), (X j i - Y j i) * (Real.sqrt (l.choose i.val : ℝ) : ℂ) * t ^ i.val = 0 := by
    intro t
    have := congrFun (h ![1, t]) j
    simp only [Matrix.mulVec, dotProduct, g74g_mu] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one] at this
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set p : Polynomial ℂ := ∑ i : Fin (l+1),
    Polynomial.C ((X j i - Y j i) * (Real.sqrt (l.choose i.val : ℝ) : ℂ)) * Polynomial.X ^ i.val with hp
  have hp0 : p = 0 := by
    apply Polynomial.funext
    intro t
    rw [hp, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_zero]
    exact hrow t
  have hcoef := congrArg (fun q => Polynomial.coeff q k.val) hp0
  simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hcoef
  rw [Finset.sum_eq_single k] at hcoef
  · rw [if_pos rfl] at hcoef
    have hne : (Real.sqrt (l.choose k.val : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt (l.choose k.val : ℝ) := Real.sqrt_pos.mpr (by
        exact_mod_cast Nat.choose_pos (by omega))
      exact_mod_cast this.ne'
    have := (mul_eq_zero.mp hcoef).resolve_right hne
    exact sub_eq_zero.mp this
  · intro b _ hb
    rw [if_neg (fun h => hb (Fin.ext h.symm))]
  · simp

def g74q_tv (l : ℕ) (v : Fin 2 → ℂ) : Qubits l → ℂ :=
  fun x => ∏ i, v (QAlgorithms.Papers.Independent.Support21.P18.bitIndex (x i))

lemma g74q_sumBool (f : Fin 2 → ℂ) :
    (∑ c : Bool, f (QAlgorithms.Papers.Independent.Support21.P18.bitIndex c)) = ∑ j : Fin 2, f j := by
  simp [QAlgorithms.Papers.Independent.Support21.P18.bitIndex, Fin.sum_univ_two, add_comm]

lemma g74q_Q_tv (l : ℕ) (M : Op (Fin 2)) (v : Fin 2 → ℂ) :
    QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower l M *ᵥ g74q_tv l v =
      g74q_tv l (M *ᵥ v) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, g74q_tv,
    QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower, Matrix.submatrix_apply,
    QAlgorithms.Papers.Independent.Information100.P63.tensorPower]
  simp_rw [← Finset.prod_mul_distrib]
  have key := Finset.prod_univ_sum (t := fun _ : Fin l => (Finset.univ : Finset Bool))
    (fun i c => M (QAlgorithms.Papers.Independent.Support21.P18.bitIndex (x i))
      (QAlgorithms.Papers.Independent.Support21.P18.bitIndex c) *
      v (QAlgorithms.Papers.Independent.Support21.P18.bitIndex c))
  rw [Fintype.piFinset_univ] at key
  refine key.symm.trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  exact g74q_sumBool (fun j => M (QAlgorithms.Papers.Independent.Support21.P18.bitIndex (x i)) j * v j)

lemma g74q_prodPow (l : ℕ) (v : Fin 2 → ℂ) (x : Qubits l) :
    g74q_tv l v x = v 0 ^ (l - hammingWeight x) * v 1 ^ hammingWeight x := by
  have h1 : ∀ i, v (QAlgorithms.Papers.Independent.Support21.P18.bitIndex (x i)) =
      if x i = true then v 1 else v 0 := by
    intro i; cases x i <;> simp [QAlgorithms.Papers.Independent.Support21.P18.bitIndex]
  unfold g74q_tv
  simp_rw [h1]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin l))) (fun i : Fin l => x i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  unfold hammingWeight
  rw [mul_comm]
  congr 2
  omega

lemma g74q_hw_le (l : ℕ) (x : Qubits l) : hammingWeight x ≤ l := by
  unfold hammingWeight
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma g74q_E_mu (l : ℕ) (v : Fin 2 → ℂ) :
    symmetricEmbedding l *ᵥ g74g_mu l v = g74q_tv l v := by
  funext x
  rw [g74q_prodPow]
  simp only [Matrix.mulVec, dotProduct, symmetricEmbedding,
    QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding, g74g_mu]
  have hle : hammingWeight x < l + 1 := by have := g74q_hw_le l x; omega
  rw [Finset.sum_eq_single ⟨hammingWeight x, hle⟩]
  · simp only [if_true]
    have hpos : (0:ℝ) < Real.sqrt (Nat.choose l (hammingWeight x) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos (g74q_hw_le l x))
    have hne : ((Real.sqrt (Nat.choose l (hammingWeight x) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast hpos.ne'
    field_simp
  · intro b _ hb
    rw [if_neg]; · simp
    intro h; apply hb; ext; simp [h]
  · simp

theorem g74q_extR {ι : Type*} (l : ℕ) (X Y : Matrix ι (Fin (l+1)) ℂ)
    (h : ∀ v : Fin 2 → ℂ, X *ᵥ g74g_mu l v = Y *ᵥ g74g_mu l v) : X = Y := by
  ext x k
  have := g74g_ext l (Matrix.of fun _ k => X x k) (Matrix.of fun _ k => Y x k)
    (fun v => funext fun _ => by simpa [Matrix.mulVec, dotProduct] using congrFun (h v) x)
  simpa using congrFun (congrFun this 0) k

theorem g74q_QE (l : ℕ) (M : Op (Fin 2)) :
    QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower l M *
        symmetricEmbedding l = symmetricEmbedding l * polynomialIrrep l M := by
  apply g74q_extR; intro v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, g74q_E_mu, g74q_Q_tv, g74g_mulVec, g74q_E_mu]

lemma g74q_card_hw (l j : ℕ) :
    (Finset.univ.filter (fun x : Qubits l => hammingWeight x = j)).card = l.choose j := by
  have : (Finset.univ.filter (fun x : Qubits l => hammingWeight x = j)).card =
      (Finset.powersetCard j (Finset.univ : Finset (Fin l))).card := by
    apply Finset.card_bij (fun x _ => Finset.univ.filter (fun i => x i = true))
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact hx
    · intro x _ y _ hxy
      funext i
      have := congrArg (fun s => i ∈ s) hxy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
      cases hx : x i <;> cases hy : y i <;> simp_all
    · intro s hs
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hs
      refine ⟨fun i => decide (i ∈ s), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        unfold hammingWeight
        convert hs using 2
        ext i; simp
      · ext i; simp
  rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem g74q_EhE (l : ℕ) : (symmetricEmbedding l)ᴴ * symmetricEmbedding l = 1 := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, symmetricEmbedding,
    QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding]
  by_cases hjk : j = k
  · subst hjk
    simp only [Matrix.one_apply_eq]
    have : ∀ x : Qubits l, star (if hammingWeight x = j.val then ((Real.sqrt (l.choose j.val : ℝ))⁻¹ : ℂ) else 0) *
        (if hammingWeight x = j.val then ((Real.sqrt (l.choose j.val : ℝ))⁻¹ : ℂ) else 0) =
        if hammingWeight x = j.val then ((l.choose j.val : ℂ))⁻¹ else 0 := by
      intro x
      split_ifs
      · have hpos : (0:ℝ) ≤ (l.choose j.val : ℝ) := by positivity
        rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
          ← mul_inv, Real.mul_self_sqrt hpos]
        push_cast; rfl
      · simp
    simp_rw [this]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, g74q_card_hw]
    have hpos : (l.choose j.val : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : j.val ≤ l)).ne'
    rw [nsmul_eq_mul, mul_inv_cancel₀ hpos]
  · rw [Matrix.one_apply_ne hjk]
    apply Finset.sum_eq_zero
    intro x _
    have : ¬ (hammingWeight x = j.val ∧ hammingWeight x = k.val) := by
      rintro ⟨h1, h2⟩; exact hjk (Fin.ext (h1.symm.trans h2))
    split_ifs <;> simp_all

theorem solution (ell : ℕ) (M : Op (Fin 2)) :
    (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower ell M *
        symmetricEmbedding ell = symmetricEmbedding ell * polynomialIrrep ell M) ∧
    (symmetricEmbedding ell)ᴴ * QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower ell M *
      symmetricEmbedding ell = polynomialIrrep ell M := by
  refine ⟨g74q_QE ell M, ?_⟩
  rw [Matrix.mul_assoc, g74q_QE, ← Matrix.mul_assoc, g74q_EhE, Matrix.one_mul]

end
