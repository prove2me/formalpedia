-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.dual_cg_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:43:27.717868+00:00
-- url     : https://prove2.me/submissions/1ee00e6e-11a1-4b4b-88da-474ef7f6b89f

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


namespace X7CG

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


lemma g74q_real_id (A B N C0 C1 : ℝ) (hA : 0 < A) (hB : 0 < B) (hN : 0 < N) (h0 : 0 < C0) (h1 : 0 < C1)
    (key : A * C0 = B * C1) :
    Real.sqrt (B / N) * (Real.sqrt C1)⁻¹ =
      Real.sqrt (2 * A / N) * (C0 * (C1⁻¹ * ((Real.sqrt 2)⁻¹ * (Real.sqrt C0)⁻¹))) := by
  have hk : Real.sqrt A * Real.sqrt C0 = Real.sqrt B * Real.sqrt C1 := by
    rw [← Real.sqrt_mul hA.le, ← Real.sqrt_mul hB.le, key]
  rw [Real.sqrt_div' _ hN.le, Real.sqrt_div' _ hN.le, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have e0 : C0 = Real.sqrt C0 ^ 2 := (Real.sq_sqrt h0.le).symm
  have e1 : C1 = Real.sqrt C1 ^ 2 := (Real.sq_sqrt h1.le).symm
  have p0 : 0 < Real.sqrt C0 := Real.sqrt_pos.mpr h0
  have p1 : 0 < Real.sqrt C1 := Real.sqrt_pos.mpr h1
  have pN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have p2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set s0 := Real.sqrt C0
  set s1 := Real.sqrt C1
  clear_value s0 s1
  subst e0 e1
  field_simp
  linear_combination (-1 : ℝ) * hk

example (m w : ℕ) (hw : w ≤ m) : True := by
  have := Nat.add_one_mul_choose_eq m w
  have := Nat.choose_mul_succ_eq m w
  trivial

lemma g74q_hw_cons (m : ℕ) (c : Bool) (t : Fin m → Bool) :
    hammingWeight (Fin.cons c t : Qubits (m+1)) = (if c = true then 1 else 0) + hammingWeight t := by
  unfold hammingWeight
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp

lemma g74q_sum_cons (m : ℕ) (f : Qubits (m+1) → ℂ) :
    (∑ z : Qubits (m+1), f z) = ∑ c : Bool, ∑ t : Fin m → Bool, f (Fin.cons c t) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => Bool)) _ _ (fun p => rfl)).symm

lemma g74q_count (m w : ℕ) :
    (∑ t : Fin m → Bool, if hammingWeight t = w then (1:ℂ) else 0) = (m.choose w : ℂ) := by
  rw [Finset.sum_boole, g74q_card_hw]

lemma g74q_P_apply (l : ℕ) (y z : Qubits l) :
    dickeColumnProjector l y z = if hammingWeight y = hammingWeight z then
      ((l.choose (hammingWeight y) : ℂ))⁻¹ else 0 := by
  simp only [dickeColumnProjector, Matrix.mul_apply, Matrix.conjTranspose_apply, symmetricEmbedding,
    QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding]
  have hle : hammingWeight y < l + 1 := by have := g74q_hw_le l y; omega
  rw [Finset.sum_eq_single ⟨hammingWeight y, hle⟩]
  · simp only [if_true]
    by_cases h : hammingWeight z = hammingWeight y
    · rw [if_pos h, if_pos h.symm]
      have hpos : (0:ℝ) ≤ (l.choose (hammingWeight y) : ℝ) := by positivity
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
          ← mul_inv, Real.mul_self_sqrt hpos]
      push_cast; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  · intro b _ hb
    rw [if_neg]; · simp
    intro h; apply hb; ext; simp [h]
  · simp

lemma g74q_singlet_cons (m : ℕ) (w : Fin (m+1)) (a : Fin 2) (c : Bool) (t : Fin m → Bool) :
    singletDicke (m+1) w (a, Fin.cons c t) =
      (if a = 0 ∧ c = true then ((Real.sqrt 2)⁻¹ : ℂ) else if a = 1 ∧ c = false then -((Real.sqrt 2)⁻¹ : ℂ) else 0) *
      (if hammingWeight t = w.val then ((Real.sqrt (m.choose w.val : ℝ))⁻¹ : ℂ) else 0) := by
  simp only [singletDicke, schurDicke, QAlgorithms.Papers.Independent.Information100.P22.dicke,
    PiLp.toLp_apply, dif_pos (Nat.succ_pos m)]
  have e : ∀ j : Fin m, (Fin.cons c t : Fin (m+1) → Bool) ⟨j.val + 1, by omega⟩ = t j := fun j => rfl
  simp [e]

lemma g74q_hw_lt (l : ℕ) (x : Qubits l) : hammingWeight x < l + 1 := by
  have := g74q_hw_le l x; omega

lemma g74q_XEh {R : Type*} (l : ℕ) (X : Matrix R (Fin 2 × Fin (l+1)) ℂ) (r : R) (a : Fin 2) (y : Qubits l) :
    (X * Matrix.kronecker (1 : Op (Fin 2)) (symmetricEmbedding l)ᴴ) r (a, y) =
      X r (a, ⟨hammingWeight y, g74q_hw_lt l y⟩) * ((Real.sqrt (l.choose (hammingWeight y) : ℝ))⁻¹ : ℂ) := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, symmetricEmbedding,
    QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp only [if_true, one_mul]
  rw [Finset.sum_eq_single ⟨hammingWeight y, g74q_hw_lt l y⟩]
  · simp only [if_true]
    congr 1
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inv]
  · intro b _ hb
    rw [if_neg]; · simp
    intro h; apply hb; ext; simp [h]
  · simp

lemma g74q_real_id2 (A B P Q : ℝ) (hA : 0 < A) (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q)
    (key : A * Q = B * P) : (Real.sqrt P)⁻¹ = Real.sqrt B / Real.sqrt A * (Real.sqrt Q)⁻¹ := by
  have hk : Real.sqrt A * Real.sqrt Q = Real.sqrt B * Real.sqrt P := by
    rw [← Real.sqrt_mul hA.le, ← Real.sqrt_mul hB.le, key]
  have pA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have pP : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have pQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  field_simp
  linear_combination hk

theorem g74q_CG_eq (l : ℕ) :
    symmetricCG l = ordinaryCG l * Matrix.kronecker (1 : Op (Fin 2)) (symmetricEmbedding l)ᴴ := by
  ext r p
  obtain ⟨a, y⟩ := p
  rw [g74q_XEh]
  have hle := g74q_hw_le l y
  rcases r with v | w
  · fin_cases a
    · simp [symmetricCG, primedDicke, ordinaryCG, schurDicke,
        QAlgorithms.Papers.Independent.Information100.P22.dicke]
      by_cases h : hammingWeight y = v.val + 1
      · rw [if_pos h, if_pos h.symm, h, Real.sqrt_div (by positivity)]
        push_cast
        simp [Complex.conj_ofReal]
      · rw [if_neg h, if_neg (Ne.symm h)]; simp
    · simp [symmetricCG, primedDicke, ordinaryCG, schurDicke,
        QAlgorithms.Papers.Independent.Information100.P22.dicke]
      by_cases h : hammingWeight y = v.val
      · have hv : (v.val : ℝ) ≤ l := by exact_mod_cast v.2.le
        rw [if_pos h, if_pos h.symm, h]
        simp [Complex.conj_ofReal]
        ring
      · rw [if_neg h, if_neg (Ne.symm h)]; simp
  · fin_cases a
    · simp [symmetricCG, pairDicke, ordinaryCG]
      by_cases h : hammingWeight y = w.val
      · rw [if_pos h, if_pos h.symm]
        have hP : (0:ℝ) < ((l+1).choose (hammingWeight y) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
        have hQ : (0:ℝ) < (l.choose (hammingWeight y) : ℝ) := by exact_mod_cast Nat.choose_pos hle
        have hhl : (hammingWeight y : ℝ) ≤ l := by exact_mod_cast hle
        have key : ((l:ℝ)+1) * (l.choose (hammingWeight y) : ℝ) =
            ((l:ℝ)+1-hammingWeight y) * ((l+1).choose (hammingWeight y) : ℝ) := by
          have h' := Nat.choose_mul_succ_eq l (hammingWeight y)
          have hc : ((l + 1 - hammingWeight y : ℕ) : ℝ) = (l:ℝ) + 1 - hammingWeight y := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          rw [← hc, mul_comm, mul_comm (((l + 1 - hammingWeight y : ℕ) : ℝ))]; exact_mod_cast h'
        have := g74q_real_id2 _ _ _ _ (by positivity) (by linarith) hP hQ key
        have := congrArg (fun r : ℝ => (r : ℂ)) this
        rw [← h]
        push_cast at this ⊢
        simp only [Complex.conj_ofReal, map_inv₀]
        exact this
      · rw [if_neg h, if_neg (Ne.symm h)]; simp
    · simp [symmetricCG, pairDicke, ordinaryCG]
      by_cases h : 1 + hammingWeight y = w.val
      · rw [if_pos h, if_pos (by omega)]
        have hP : (0:ℝ) < ((l+1).choose (hammingWeight y + 1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
        have hQ : (0:ℝ) < (l.choose (hammingWeight y) : ℝ) := by exact_mod_cast Nat.choose_pos hle
        have key : ((l:ℝ)+1) * (l.choose (hammingWeight y) : ℝ) =
            ((hammingWeight y : ℝ)+1) * ((l+1).choose (hammingWeight y + 1) : ℝ) := by
          have h' := Nat.add_one_mul_choose_eq l (hammingWeight y)
          rw [mul_comm ((hammingWeight y:ℝ)+1)]; exact_mod_cast h'
        have := g74q_real_id2 _ _ _ _ (by positivity) (by positivity) hP hQ key
        have := congrArg (fun r : ℝ => (r : ℂ)) this
        rw [← h, add_comm 1]
        push_cast at this ⊢
        simp only [Complex.conj_ofReal, map_inv₀]
        exact this
      · rw [if_neg h, if_neg (by omega)]; simp

lemma g74q_sum2 (l a b c : ℕ) (F G : Fin (l+1) → ℂ) :
    (∑ x : Fin (l+1), (if a = x.val + c then F x else 0) * star (if b = x.val + c then G x else 0)) =
      if h : a = b ∧ c ≤ a ∧ a - c < l + 1 then F ⟨a - c, h.2.2⟩ * star (G ⟨a - c, h.2.2⟩) else 0 := by
  by_cases h : a = b ∧ c ≤ a ∧ a - c < l + 1
  · rw [dif_pos h, Finset.sum_eq_single ⟨a - c, h.2.2⟩]
    · simp only
      rw [if_pos (by omega), if_pos (by omega)]
    · intro x _ hx
      have : ¬ a = x.val + c := by
        intro e; apply hx; ext; simp; omega
      rw [if_neg this, zero_mul]
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro x _
    by_cases h1 : a = x.val + c
    · by_cases h2 : b = x.val + c
      · exfalso; apply h; refine ⟨by omega, by omega, by omega⟩
      · rw [if_neg h2]; simp
    · rw [if_neg h1, zero_mul]

lemma g74q_sqd (A L : ℝ) (hA : 0 ≤ A) (hL : 0 < L) :
    ((Real.sqrt A : ℂ) / (Real.sqrt L : ℂ)) * ((Real.sqrt A : ℂ) / (Real.sqrt L : ℂ)) = ((A / L : ℝ) : ℂ) := by
  have : Real.sqrt A / Real.sqrt L * (Real.sqrt A / Real.sqrt L) = A / L := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hA, Real.mul_self_sqrt hL.le]
  rw [← this]; push_cast; ring

theorem g74q_OOh (l : ℕ) : ordinaryCG l * (ordinaryCG l)ᴴ = 1 := by
  have hL : (0:ℝ) < (l:ℝ) + 1 := by positivity
  ext r s
  rcases r with v | w <;> rcases s with v' | w' <;>
  ( simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      ordinaryCG, Fin.val_zero, Fin.val_one]
    rw [g74q_sum2, g74q_sum2]
    simp )
  · by_cases h : v = v'
    · subst h
      have hv : (v.val : ℝ) ≤ l := by exact_mod_cast v.2.le
      simp only [if_true, Matrix.one_apply_eq]
      rw [neg_div, neg_mul_neg, g74q_sqd _ _ (by positivity) hL, g74q_sqd _ _ (by linarith) hL]
      rw [← Complex.ofReal_add, ← add_div, show (v.val:ℝ) + 1 + (l - v.val) = l + 1 by ring,
        div_self hL.ne']
      simp
    · have h' : v.val ≠ v'.val := fun e => h (Fin.ext e)
      rw [if_neg h', if_neg h', Matrix.one_apply_ne (fun e => h (Sum.inl_injective e))]; simp
  · by_cases h : v.val + 1 = w'.val
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; simp
  · by_cases h : w.val = v'.val + 1
    · have h1 : w.val ≤ l := by omega
      rw [if_pos ⟨h, h1⟩, if_pos ⟨h, by omega, by omega⟩]
      have e1 : ((w.val - 1 : ℕ) : ℝ) = v'.val := by rw [show w.val - 1 = v'.val by omega]
      have e2 : (w.val : ℝ) = v'.val + 1 := by exact_mod_cast h
      rw [e1, e2, show (l:ℝ) + 1 - ((v'.val:ℝ) + 1) = l - v'.val by ring]
      ring
    · rw [if_neg (fun e => h e.1), if_neg (fun e => h e.1)]; simp
  · by_cases h : w = w'
    · subst h
      simp only [true_and, Matrix.one_apply_eq]
      have hw := w.2
      by_cases h0 : w.val = 0
      · rw [if_pos (by omega), if_neg (by omega), h0]
        simp only [Nat.cast_zero, sub_zero, add_zero]
        rw [g74q_sqd _ _ hL.le hL, div_self hL.ne']; simp
      · by_cases h2 : w.val = l + 1
        · rw [if_neg (by omega), if_pos (by omega), zero_add]
          rw [show ((w.val - 1 : ℕ) : ℝ) + 1 = l + 1 by rw [show w.val - 1 = l by omega]]
          rw [g74q_sqd _ _ hL.le hL, div_self hL.ne']; simp
        · rw [if_pos (by omega), if_pos (by omega)]
          have hw1 : ((w.val - 1 : ℕ) : ℝ) + 1 = w.val := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          have hwl : (w.val : ℝ) ≤ l := by exact_mod_cast (show w.val ≤ l by omega)
          rw [hw1, g74q_sqd _ _ (by linarith) hL, g74q_sqd _ _ (by positivity) hL,
            ← Complex.ofReal_add, ← add_div, show (l:ℝ) + 1 - w.val + w.val = l + 1 by ring,
            div_self hL.ne']
          simp
    · have h' : w.val ≠ w'.val := fun e => h (Fin.ext e)
      rw [if_neg (fun e => h' e.1), if_neg (fun e => h' e.1),
        Matrix.one_apply_ne (fun e => h (Sum.inr_injective e))]; simp

lemma g74q_kct {a b c e : Type*} (A : Matrix a b ℂ) (B : Matrix c e ℂ) :
    (Matrix.kronecker A B)ᴴ = Matrix.kronecker Aᴴ Bᴴ := Matrix.conjTranspose_kronecker A B

lemma g74q_kmul {a b c e f g : Type*} [Fintype b] [Fintype e] (A : Matrix a b ℂ) (B : Matrix b c ℂ)
    (A' : Matrix f e ℂ) (B' : Matrix e g ℂ) :
    Matrix.kronecker A A' * Matrix.kronecker B B' = Matrix.kronecker (A * B) (A' * B') :=
  (Matrix.mul_kronecker_mul A B A' B').symm

lemma g74q_k11 {a b : Type*} [DecidableEq a] [DecidableEq b] :
    Matrix.kronecker (1 : Matrix a a ℂ) (1 : Matrix b b ℂ) = 1 := Matrix.one_kronecker_one

lemma g74q_KKh (l : ℕ) :
    Matrix.kronecker (1 : Op (Fin 2)) (symmetricEmbedding l)ᴴ *
      (Matrix.kronecker (1 : Op (Fin 2)) (symmetricEmbedding l)ᴴ)ᴴ = 1 := by
  rw [g74q_kct, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one,
    g74q_kmul, Matrix.one_mul, g74q_EhE, g74q_k11]

lemma g74q_OhO (l : ℕ) : (ordinaryCG l)ᴴ * ordinaryCG l = 1 := by
  have e : Fin l ⊕ Fin (l + 2) ≃ Fin 2 × Fin (l + 1) :=
    Fintype.equivOfCardEq (by simp; ring)
  exact (Matrix.mul_eq_one_comm_of_equiv e).mp (g74q_OOh l)

theorem g74q_CGCGh (l : ℕ) : symmetricCG l * (symmetricCG l)ᴴ = 1 := by
  rw [g74q_CG_eq, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (ordinaryCG l)ᴴ,
    g74q_KKh, Matrix.one_mul, g74q_OOh]

theorem g74q_CGE (l : ℕ) :
    ordinaryCG l = symmetricCG l * Matrix.kronecker (1 : Op (Fin 2)) (symmetricEmbedding l) := by
  have := g74q_KKh l
  rw [g74q_kct, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at this
  rw [g74q_CG_eq, Matrix.mul_assoc, this, Matrix.mul_one]


def g74q_v (l : ℕ) : Fin l ⊕ Fin (l+2) → EuclideanSpace ℂ (Fin 2 × Qubits l) :=
  Sum.elim (primedDicke l) (fun w => pairDicke l w.val)

def g74q_u (l : ℕ) : Fin 2 × Fin (l+1) → EuclideanSpace ℂ (Fin 2 × Qubits l) :=
  fun a => WithLp.toLp 2 fun x : Fin 2 × Qubits l => if x.1 = a.1 then schurDicke l a.2.val x.2 else 0

lemma g74q_CG_v (l : ℕ) (r : Fin l ⊕ Fin (l+2)) (x : Fin 2 × Qubits l) :
    symmetricCG l r x = star (g74q_v l r x) := by
  rcases r with v | w <;> rfl

lemma g74q_K_u (l : ℕ) (p : Fin 2 × Fin (l+1)) (x : Fin 2 × Qubits l) :
    Matrix.kronecker (1 : Op (Fin 2)) (symmetricEmbedding l)ᴴ p x = star (g74q_u l p x) := by
  obtain ⟨i, k⟩ := p
  obtain ⟨a, y⟩ := x
  simp only [g74q_u, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply, PiLp.toLp_apply, schurDicke, QAlgorithms.Papers.Independent.Information100.P22.dicke,
    symmetricEmbedding, QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding, Fintype.card_fin]
  by_cases h : i = a
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]; simp

lemma g74q_inner_eq {ι : Type*} [Fintype ι] (f g : EuclideanSpace ℂ ι) :
    inner ℂ f g = ∑ x, star (f x) * g x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [mul_comm]

lemma g74q_v_orth (l : ℕ) : Orthonormal ℂ (g74q_v l) := by
  rw [orthonormal_iff_ite]
  intro r s
  have := congrFun (congrFun (g74q_CGCGh l) r) s
  rw [Matrix.mul_apply] at this
  rw [g74q_inner_eq, ← Matrix.one_apply, ← this]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.conjTranspose_apply, g74q_CG_v, g74q_CG_v, star_star]

lemma g74q_u_orth (l : ℕ) : Orthonormal ℂ (g74q_u l) := by
  rw [orthonormal_iff_ite]
  intro r s
  have := congrFun (congrFun (g74q_KKh l) r) s
  rw [Matrix.mul_apply] at this
  rw [g74q_inner_eq, ← Matrix.one_apply, ← this]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.conjTranspose_apply, g74q_K_u, g74q_K_u, star_star]

lemma g74q_v_mem (l : ℕ) (r : Fin l ⊕ Fin (l+2)) : g74q_v l r ∈ physicalSymmetricSpace l := by
  have e : g74q_v l r = ∑ p, star (ordinaryCG l r p) • g74q_u l p := by
    ext x
    have := congrFun (congrFun (g74q_CG_eq l) r) x
    rw [Matrix.mul_apply] at this
    rw [g74q_CG_v] at this
    have := congrArg star this
    rw [star_star, star_sum] at this
    rw [this, WithLp.ofLp_sum]
    simp only [Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [star_mul, g74q_K_u, star_star, mul_comm]
  rw [e]
  refine Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)


lemma g74q_Qcons (m : ℕ) (M : Op (Fin 2)) (c d : Bool) (t u : Fin m → Bool) :
    QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower (m+1) M (Fin.cons c t) (Fin.cons d u) =
      M (QAlgorithms.Papers.Independent.Support21.P18.bitIndex c)
        (QAlgorithms.Papers.Independent.Support21.P18.bitIndex d) *
      QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower m M t u := by
  simp [QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower,
    QAlgorithms.Papers.Independent.Information100.P63.tensorPower, Matrix.submatrix_apply, Fin.prod_univ_succ]

def g74q_bitE : Fin 2 ≃ Bool where
  toFun a := decide (a = 1)
  invFun b := if b then 1 else 0
  left_inv a := by fin_cases a <;> rfl
  right_inv b := by cases b <;> rfl

def g74q_e (l : ℕ) : Fin 2 × Qubits l ≃ Qubits (l+1) :=
  (Equiv.prodCongr g74q_bitE (Equiv.refl _)).trans (Fin.consEquiv (fun _ : Fin (l+1) => Bool))

lemma g74q_e_apply (l : ℕ) (a : Fin 2) (y : Qubits l) :
    g74q_e l (a, y) = Fin.cons (decide (a = 1)) y := rfl

lemma g74q_bit_dec (a : Fin 2) :
    QAlgorithms.Papers.Independent.Support21.P18.bitIndex (decide (a = 1)) = a := by
  fin_cases a <;> rfl

lemma g74q_kron_e (l : ℕ) (M : Op (Fin 2)) (x x' : Fin 2 × Qubits l) :
    Matrix.kronecker M (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower l M) x x' =
      QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower (l+1) M (g74q_e l x) (g74q_e l x') := by
  obtain ⟨a, y⟩ := x
  obtain ⟨b, z⟩ := x'
  rw [g74q_e_apply, g74q_e_apply, g74q_Qcons, g74q_bit_dec, g74q_bit_dec]
  rfl

lemma g74q_pair_e (l : ℕ) (k : Fin (l+2)) (x : Fin 2 × Qubits l) :
    pairDicke l k.val x = symmetricEmbedding (l+1) (g74q_e l x) k := by
  obtain ⟨a, y⟩ := x
  rw [g74q_e_apply]
  simp only [pairDicke, PiLp.toLp_apply, symmetricEmbedding,
    QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding, g74q_hw_cons]
  fin_cases a <;> simp [add_comm]

lemma g74q_sum2e {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → β → ℂ) :
    (∑ x, ∑ x', f (e x) (e x')) = ∑ z, ∑ z', f z z' := by
  rw [← Equiv.sum_comp e (fun z => ∑ z', f z z')]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Equiv.sum_comp e (fun z' => f (e x) z')

lemma g74q_inner_mv {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (v w : EuclideanSpace ℂ ι) :
    inner ℂ v (WithLp.toLp 2 (A.mulVec w)) = ∑ x, ∑ x', star (v x) * A x x' * w x' := by
  rw [g74q_inner_eq]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [PiLp.toLp_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem g74q_part1 (ell : ℕ) (M : Op (Fin 2)) (j k : Fin (ell+2)) :
    inner ℂ (pairDicke ell j.val)
      (WithLp.toLp 2 ((Matrix.kronecker M
        (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower ell M)).mulVec
        (pairDicke ell k.val))) = polynomialIrrep (ell+1) M j k := by
  rw [g74q_inner_mv]
  simp only [g74q_pair_e, g74q_kron_e]
  refine (g74q_sum2e (g74q_e ell) (fun z z' => star (symmetricEmbedding (ell+1) z j) *
    QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower (ell+1) M z z' *
    symmetricEmbedding (ell+1) z' k)).trans ?_
  have h := (g74q_QE (ell+1) M)
  have h2 : (symmetricEmbedding (ell+1))ᴴ * QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower (ell+1) M *
      symmetricEmbedding (ell+1) = polynomialIrrep (ell+1) M := by
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, g74q_EhE, Matrix.one_mul]
  rw [← h2, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
theorem g74g_transpose (l : ℕ) (M : Op (Fin 2)) :
    polynomialIrrep l M.transpose = (polynomialIrrep l M).transpose := by
  ext j k
  simp only [polynomialIrrep, Matrix.transpose_apply]
  congr 1
  · congr 2; ring
  · refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : r + j.val ≤ l ∧ r + k.val ≤ l ∧ l ≤ j.val + k.val + r
    · rw [if_pos h, if_pos ⟨h.2.1, h.1, by omega⟩, show k.val + j.val + r - l = j.val + k.val + r - l by omega]
      ring
    · rw [if_neg h, if_neg (by omega)]

theorem g74g_conj (l : ℕ) (M : Op (Fin 2)) :
    polynomialIrrep l (fun i j => conj (M i j)) = (fun i j => conj (polynomialIrrep l M i j)) := by
  funext j k
  simp only [polynomialIrrep, map_mul, map_sum, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs
  · simp [map_div₀, map_mul, map_pow, map_natCast]
  · simp

theorem g74g_conjTranspose (l : ℕ) (M : Op (Fin 2)) :
    polynomialIrrep l Mᴴ = (polynomialIrrep l M)ᴴ := by
  set C : Op (Fin 2) := fun i j => conj (M i j) with hC
  have h1 : Mᴴ = C.transpose := Matrix.ext fun i j => rfl
  rw [h1, g74g_transpose, hC, g74g_conj]
  exact Matrix.ext fun i j => rfl


theorem g74q_pdp (ell : ℕ) (hell : 1 ≤ ell) (w : Fin ell) :
    primedDicke ell w = (Real.sqrt (2*(ell:ℝ)/(ell+1)) : ℂ) •
      WithLp.toLp 2 ((Matrix.kronecker (1 : Op (Fin 2)) (dickeColumnProjector ell)).mulVec
        (singletDicke ell w)) := by
  obtain ⟨m, rfl⟩ : ∃ m, ell = m + 1 := ⟨ell - 1, by omega⟩
  ext p
  obtain ⟨a, y⟩ := p
  simp only [PiLp.smul_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, smul_eq_mul]
  simp only [g74q_P_apply, g74q_sum_cons m, g74q_singlet_cons, g74q_hw_cons, Fintype.sum_bool]
  simp only [primedDicke, schurDicke, QAlgorithms.Papers.Independent.Information100.P22.dicke,
    PiLp.toLp_apply, Fintype.card_fin]
  have hw : w.val ≤ m := by omega
  have hC0 : (0:ℝ) < (m.choose w.val : ℝ) := by exact_mod_cast Nat.choose_pos hw
  fin_cases a
  · have hs : ∀ x : Fin m → Bool, (if hammingWeight x = w.val then
          (if hammingWeight y = 1 + hammingWeight x then
            ((((m + 1).choose (hammingWeight y)) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt (m.choose w.val : ℝ) : ℝ) : ℂ)⁻¹)
          else 0) else 0) =
        (if hammingWeight x = w.val then (1:ℂ) else 0) * (if hammingWeight y = w.val + 1 then
            ((((m + 1).choose (w.val + 1)) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt (m.choose w.val : ℝ) : ℝ) : ℂ)⁻¹)
          else 0) := by
      intro x
      by_cases h1 : hammingWeight x = w.val
      · rw [if_pos h1, if_pos h1, one_mul, h1, add_comm 1 w.val]
        by_cases h2 : hammingWeight y = w.val + 1
        · rw [if_pos h2, if_pos h2, h2]
        · rw [if_neg h2, if_neg h2]
      · rw [if_neg h1, if_neg h1, zero_mul]
    simp
    rw [Finset.sum_congr rfl (fun x _ => hs x), ← Finset.sum_mul, g74q_count]
    by_cases h : hammingWeight y = w.val + 1
    · simp only [h, if_true]
      have hC1 : (0:ℝ) < ((m+1).choose (w.val+1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
      have key : ((m:ℝ)+1) * (m.choose w.val : ℝ) = ((w.val:ℝ)+1) * ((m+1).choose (w.val+1) : ℝ) := by
        have h' := Nat.add_one_mul_choose_eq m w.val
        rw [mul_comm ((w.val:ℝ)+1)]; exact_mod_cast h'
      have := g74q_real_id ((m:ℝ)+1) ((w.val:ℝ)+1) ((m:ℝ)+1+1) _ _ (by positivity) (by positivity)
        (by positivity) hC0 hC1 key
      have := congrArg (fun r : ℝ => (r : ℂ)) this
      push_cast at this ⊢
      exact this
    · simp [h]
  · have hs : ∀ x : Fin m → Bool, (if hammingWeight x = w.val then
          -(if hammingWeight y = hammingWeight x then
            ((((m + 1).choose (hammingWeight y)) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt (m.choose w.val : ℝ) : ℝ) : ℂ)⁻¹)
          else 0) else 0) =
        (if hammingWeight x = w.val then (1:ℂ) else 0) * -(if hammingWeight y = w.val then
            ((((m + 1).choose w.val) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt (m.choose w.val : ℝ) : ℝ) : ℂ)⁻¹)
          else 0) := by
      intro x
      by_cases h1 : hammingWeight x = w.val
      · rw [if_pos h1, if_pos h1, one_mul, h1]
        by_cases h2 : hammingWeight y = w.val
        · rw [if_pos h2, if_pos h2, h2]
        · rw [if_neg h2, if_neg h2]
      · rw [if_neg h1, if_neg h1, zero_mul]
    simp
    rw [Finset.sum_congr rfl (fun x _ => hs x), ← Finset.sum_mul, g74q_count]
    by_cases h : hammingWeight y = w.val
    · simp only [h, if_true]
      have hC1 : (0:ℝ) < ((m+1).choose w.val : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
      have key : ((m:ℝ)+1) * (m.choose w.val : ℝ) = ((m:ℝ)+1-w.val) * ((m+1).choose w.val : ℝ) := by
        have h' := Nat.choose_mul_succ_eq m w.val
        have hc : ((m + 1 - w.val : ℕ) : ℝ) = (m:ℝ) + 1 - w.val := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [← hc, mul_comm, mul_comm (((m + 1 - w.val : ℕ) : ℝ))]; exact_mod_cast h'
      have := g74q_real_id ((m:ℝ)+1) ((m:ℝ)+1-w.val) ((m:ℝ)+1+1) _ _ (by positivity)
        (by have : (w.val:ℝ) ≤ m := by exact_mod_cast hw
            linarith)
        (by positivity) hC0 hC1 key
      have := congrArg (fun r : ℝ => (r : ℂ)) this
      push_cast at this ⊢
      rw [this]; ring
    · simp [h]


lemma g74q_Q_ct (l : ℕ) (M : Op (Fin 2)) :
    (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower l M)ᴴ =
      QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower l Mᴴ := by
  ext x y
  simp [QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower,
    QAlgorithms.Papers.Independent.Information100.P63.tensorPower, Matrix.conjTranspose_apply, star_prod]

lemma g74q_EhQ (l : ℕ) (M : Op (Fin 2)) :
    (symmetricEmbedding l)ᴴ * QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower l M =
      polynomialIrrep l M * (symmetricEmbedding l)ᴴ := by
  have h := congrArg Matrix.conjTranspose (g74q_QE l Mᴴ)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, g74q_Q_ct, Matrix.conjTranspose_conjTranspose,
    g74g_conjTranspose, Matrix.conjTranspose_conjTranspose] at h
  exact h

lemma g74q_QP (l : ℕ) (M : Op (Fin 2)) :
    QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower l M * dickeColumnProjector l =
      dickeColumnProjector l * QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower l M := by
  rw [dickeColumnProjector, ← Matrix.mul_assoc, g74q_QE, Matrix.mul_assoc, Matrix.mul_assoc,
    g74q_EhQ]

def g74q_Pr (l : ℕ) : Matrix (Fin 2 × Qubits l) (Fin l) ℂ := Matrix.of fun x j => primedDicke l j x
def g74q_Sg (l : ℕ) : Matrix (Fin 2 × Qubits l) (Fin l) ℂ := Matrix.of fun x j => singletDicke l j x

lemma g74q_PrhPr (l : ℕ) : (g74q_Pr l)ᴴ * g74q_Pr l = 1 := by
  ext i j
  have := (orthonormal_iff_ite.mp (g74q_v_orth l)) (Sum.inl i) (Sum.inl j)
  rw [g74q_inner_eq] at this
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, g74q_Pr, Matrix.of_apply]
  simpa [g74q_v] using this

lemma g74q_PiPr (l : ℕ) :
    Matrix.kronecker (1 : Op (Fin 2)) (dickeColumnProjector l) * g74q_Pr l = g74q_Pr l := by
  have hK := g74q_KKh l
  rw [g74q_kct, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at hK
  have hPi : Matrix.kronecker (1 : Op (Fin 2)) (dickeColumnProjector l) =
      Matrix.kronecker (1 : Op (Fin 2)) (symmetricEmbedding l) *
        Matrix.kronecker (1 : Op (Fin 2)) (symmetricEmbedding l)ᴴ := by
    rw [g74q_kmul, Matrix.one_mul, dickeColumnProjector]
  have hC : Matrix.kronecker (1 : Op (Fin 2)) (dickeColumnProjector l) * (symmetricCG l)ᴴ = (symmetricCG l)ᴴ := by
    rw [g74q_CG_eq, Matrix.conjTranspose_mul, hPi, g74q_kct, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (ordinaryCG l)ᴴ, hK, Matrix.one_mul]
  ext x j
  have := congrFun (congrFun hC x) (Sum.inl j)
  rw [Matrix.mul_apply] at this
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, g74q_CG_v, star_star, g74q_v, Sum.elim_inl] at this
  exact this

lemma g74q_Pi_ct (l : ℕ) :
    (Matrix.kronecker (1 : Op (Fin 2)) (dickeColumnProjector l))ᴴ =
      Matrix.kronecker (1 : Op (Fin 2)) (dickeColumnProjector l) := by
  rw [g74q_kct, Matrix.conjTranspose_one, dickeColumnProjector, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

lemma g74q_APi (l : ℕ) (M : Op (Fin 2)) :
    Matrix.kronecker M (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower l M) *
      Matrix.kronecker (1 : Op (Fin 2)) (dickeColumnProjector l) =
    Matrix.kronecker (1 : Op (Fin 2)) (dickeColumnProjector l) *
      Matrix.kronecker M (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower l M) := by
  rw [g74q_kmul, g74q_kmul, Matrix.mul_one, Matrix.one_mul, g74q_QP]

lemma g74q_PrSg (l : ℕ) (hl : 1 ≤ l) :
    g74q_Pr l = ((Real.sqrt (2*(l:ℝ)/(l+1)) : ℂ)) •
      (Matrix.kronecker (1 : Op (Fin 2)) (dickeColumnProjector l) * g74q_Sg l) := by
  ext x j
  have := congrArg (fun v : EuclideanSpace ℂ (Fin 2 × Qubits l) => v x) (g74q_pdp l hl j)
  simp only [PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul] at this
  simp only [g74q_Pr, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, g74q_Sg]
  rw [this]
  rfl

lemma g74q_sigma (M : Op (Fin 2)) (a : Fin 2) (c : Bool) :
    (∑ b : Fin 2, ∑ d : Bool, M a b * M (QAlgorithms.Papers.Independent.Support21.P18.bitIndex c)
        (QAlgorithms.Papers.Independent.Support21.P18.bitIndex d) *
      (if b = 0 ∧ d = true then ((Real.sqrt 2)⁻¹ : ℂ) else if b = 1 ∧ d = false then -((Real.sqrt 2)⁻¹ : ℂ) else 0)) =
    M.det * (if a = 0 ∧ c = true then ((Real.sqrt 2)⁻¹ : ℂ) else if a = 1 ∧ c = false then -((Real.sqrt 2)⁻¹ : ℂ) else 0) := by
  rw [Matrix.det_fin_two]
  fin_cases a <;> cases c <;>
    simp [Fin.sum_univ_two, QAlgorithms.Papers.Independent.Support21.P18.bitIndex] <;> ring

lemma g74q_fact {m : ℕ} (A : Fin 2 → ℂ) (B : Bool → ℂ) (Q : (Fin m → Bool) → ℂ)
    (f : Fin 2 → Bool → ℂ) (g : (Fin m → Bool) → ℂ) :
    (∑ b : Fin 2, ∑ d : Bool, ∑ u : Fin m → Bool, A b * (B d * Q u) * (f b d * g u)) =
      (∑ b : Fin 2, ∑ d : Bool, A b * B d * f b d) * ∑ u, Q u * g u := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

lemma g74q_ASg (m : ℕ) (M : Op (Fin 2)) :
    Matrix.kronecker M (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower (m+1) M) * g74q_Sg (m+1) =
      M.det • (g74q_Sg (m+1) * polynomialIrrep m M) := by
  ext x k
  obtain ⟨a, z⟩ := x
  obtain ⟨⟨c, t⟩, rfl⟩ : ∃ p : Bool × (Fin m → Bool), Fin.cons p.1 p.2 = z :=
    ⟨(Fin.consEquiv (fun _ : Fin (m+1) => Bool)).symm z, (Fin.consEquiv (fun _ : Fin (m+1) => Bool)).apply_symm_apply z⟩
  have hQE := congrFun (congrFun (g74q_QE m M) t) k
  rw [Matrix.mul_apply, Matrix.mul_apply] at hQE
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, g74q_Sg, Matrix.of_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp only [g74q_sum_cons m, g74q_Qcons, g74q_singlet_cons]
  simp only [symmetricEmbedding, QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding] at hQE
  refine (g74q_fact (fun b => M a b)
    (fun d => M (QAlgorithms.Papers.Independent.Support21.P18.bitIndex c) (QAlgorithms.Papers.Independent.Support21.P18.bitIndex d))
    (fun u => QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower m M t u)
    (fun b d => if b = 0 ∧ d = true then ((Real.sqrt 2)⁻¹ : ℂ) else if b = 1 ∧ d = false then -((Real.sqrt 2)⁻¹ : ℂ) else 0)
    (fun u => if hammingWeight u = k.val then ((Real.sqrt (m.choose k.val : ℝ))⁻¹ : ℂ) else 0)).trans ?_
  rw [g74q_sigma, hQE, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem g74q_part2 (m : ℕ) (M : Op (Fin 2)) :
    (g74q_Pr (m+1))ᴴ * Matrix.kronecker M (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower (m+1) M) *
      g74q_Pr (m+1) = M.det • polynomialIrrep m M := by
  have hPrSg := g74q_PrSg (m+1) (by omega)
  set c : ℂ := ((Real.sqrt (2*((m+1:ℕ):ℝ)/((m+1:ℕ)+1)) : ℂ)) with hc
  set Pi := Matrix.kronecker (1 : Op (Fin 2)) (dickeColumnProjector (m+1)) with hPi
  set A := Matrix.kronecker M (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower (m+1) M) with hAdef
  set Pr := g74q_Pr (m+1) with hPr
  set Sg := g74q_Sg (m+1) with hSg
  have hA : A * Pi = Pi * A := g74q_APi (m+1) M
  have hP1 : Prᴴ * Pi = Prᴴ := by
    have := congrArg Matrix.conjTranspose (g74q_PiPr (m+1))
    rw [Matrix.conjTranspose_mul, g74q_Pi_ct] at this
    exact this
  have hS1 : c • (Prᴴ * Sg) = 1 := by
    have h1 := g74q_PrhPr (m+1)
    rw [← hPr] at h1
    conv_lhs at h1 => rw [show Prᴴ * Pr = Prᴴ * (c • (Pi * Sg)) by rw [← hPrSg]]
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hP1] at h1
    exact h1
  have hASg : A * Sg = M.det • (Sg * polynomialIrrep m M) := g74q_ASg m M
  rw [Matrix.mul_assoc]
  rw [show A * Pr = A * (c • (Pi * Sg)) by rw [← hPrSg]]
  rw [Matrix.mul_smul, ← Matrix.mul_assoc A Pi Sg, hA, Matrix.mul_assoc, hASg]
  simp only [Matrix.mul_smul]
  rw [← Matrix.mul_assoc Prᴴ Pi, hP1, smul_comm, ← Matrix.mul_assoc, ← Matrix.smul_mul, hS1, Matrix.one_mul]

lemma X7_AP (l : ℕ) (M : Op (Fin 2)) (x : Fin 2 × Qubits l) (k : Fin (l+2)) :
    ∑ x', Matrix.kronecker M (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower l M) x x' *
      pairDicke l k.val x' = ∑ j : Fin (l+2), pairDicke l j.val x * polynomialIrrep (l+1) M j k := by
  simp only [g74q_pair_e, g74q_kron_e]
  rw [Equiv.sum_comp (g74q_e l) (fun z =>
    QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower (l+1) M (g74q_e l x) z *
      symmetricEmbedding (l+1) z k)]
  have h := congrFun (congrFun (g74q_QE (l+1) M) (g74q_e l x)) k
  simp only [Matrix.mul_apply] at h
  exact h

lemma X7_orth_ip (l : ℕ) (j : Fin l) (k : Fin (l+2)) :
    ∑ x, star (primedDicke l j x) * pairDicke l k.val x = 0 := by
  have := (orthonormal_iff_ite.mp (g74q_v_orth l)) (Sum.inl j) (Sum.inr k)
  rw [g74q_inner_eq] at this
  simpa [g74q_v] using this

lemma X7_orth_ip' (l : ℕ) (j : Fin l) (k : Fin (l+2)) :
    ∑ x, star (pairDicke l k.val x) * primedDicke l j x = 0 := by
  have := (orthonormal_iff_ite.mp (g74q_v_orth l)) (Sum.inr k) (Sum.inl j)
  rw [g74q_inner_eq] at this
  simpa [g74q_v] using this

lemma X7_lowerblock (ell : ℕ) (M : Op (Fin 2)) (j k : Fin ell) :
    inner ℂ (primedDicke ell j)
      (WithLp.toLp 2 ((Matrix.kronecker M
        (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower ell M)).mulVec
        (primedDicke ell k))) = lowerCGAction ell M j k := by
  obtain ⟨m, rfl⟩ : ∃ m, ell = m + 1 := ⟨ell - 1, by have := j.isLt; omega⟩
  have := congrFun (congrFun (g74q_part2 m M) j) k
  rw [Matrix.smul_apply, smul_eq_mul] at this
  show _ = M.det * polynomialIrrep m M j k
  rw [← this, g74q_inner_mv]
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.conjTranspose_apply, g74q_Pr, Matrix.of_apply]
  rw [Finset.sum_comm]

lemma X7_SAS (l : ℕ) (M : Op (Fin 2)) :
    ordinaryCG l * Matrix.kronecker M (polynomialIrrep l M) * (ordinaryCG l)ᴴ =
      symmetricCG l * Matrix.kronecker M
        (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower l M) * (symmetricCG l)ᴴ := by
  have hT : Matrix.kronecker M (polynomialIrrep l M) =
      (Matrix.kronecker (1 : Op (Fin 2)) (symmetricEmbedding l)ᴴ) *
        Matrix.kronecker M (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower l M) *
        (Matrix.kronecker (1 : Op (Fin 2)) (symmetricEmbedding l)ᴴ)ᴴ := by
    rw [g74q_kct, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one, g74q_kmul, g74q_kmul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, g74q_QE, ← Matrix.mul_assoc, g74q_EhE,
      Matrix.one_mul]
  rw [hT, g74q_CG_eq, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem X7_cg_main (ell : ℕ) (M : Op (Fin 2)) :
    ordinaryCG ell * Matrix.kronecker M (polynomialIrrep ell M) *
      (ordinaryCG ell)ᴴ = blockDiagonal (lowerCGAction ell M) (polynomialIrrep (ell+1) M) := by
  rw [X7_SAS]
  set A := Matrix.kronecker M
    (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower ell M) with hA
  have hent : ∀ r s, (symmetricCG ell * A * (symmetricCG ell)ᴴ) r s =
      inner ℂ (g74q_v ell r) (WithLp.toLp 2 (A.mulVec (g74q_v ell s))) := by
    intro r s
    rw [g74q_inner_mv]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g74q_CG_v, star_star, Finset.sum_mul]
    rw [Finset.sum_comm]
  ext r s
  rw [hent]
  rcases r with j | j <;> rcases s with k | k
  · exact X7_lowerblock ell M j k
  · -- primed / pair
    show _ = 0
    rw [g74q_inner_mv]
    simp only [g74q_v, Sum.elim_inl, Sum.elim_inr, mul_assoc, ← Finset.mul_sum]
    simp only [hA, X7_AP, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun j' _ => ?_)
    have := X7_orth_ip ell j j'
    calc _ = (∑ x, star (primedDicke ell j x) * pairDicke ell j'.val x) *
          polynomialIrrep (ell+1) M j' k := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun x _ => ?_); ring
      _ = 0 := by rw [this, zero_mul]
  · -- pair / primed
    show _ = 0
    rw [g74q_inner_mv]
    simp only [g74q_v, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_comm]
    have hAd : ∀ x', ∑ x, star (pairDicke ell j.val x) * A x x' =
        star (∑ j' : Fin (ell+2), pairDicke ell j'.val x' * polynomialIrrep (ell+1) Mᴴ j' j) := by
      intro x'
      rw [← X7_AP, star_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [star_mul, hA, ← g74q_Q_ct, ← g74q_kct, Matrix.conjTranspose_apply, star_star]
    have e2 : ∀ x', ∑ x, star (pairDicke ell j.val x) * A x x' * primedDicke ell k x' =
        (∑ x, star (pairDicke ell j.val x) * A x x') * primedDicke ell k x' := by
      intro x'; rw [Finset.sum_mul]
    simp only [e2, hAd, star_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun j' _ => ?_)
    have := X7_orth_ip' ell k j'
    calc _ = star (polynomialIrrep (ell+1) Mᴴ j' j) *
          (∑ x, star (pairDicke ell j'.val x) * primedDicke ell k x) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [star_mul]; ring
      _ = 0 := by rw [this, mul_zero]
  · exact g74q_part1 ell M j k

end X7CG

namespace X7CG

lemma X7_SS : (!![0, 1; -1, 0] : Op (Fin 2))ᴴ * (!![0, 1; -1, 0] : Op (Fin 2)) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma X7_SS' : (!![0, 1; -1, 0] : Op (Fin 2)) * (!![0, 1; -1, 0] : Op (Fin 2))ᴴ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma X7_SMS (M : Op (Fin 2)) (hM : M.det ≠ 0) :
    (!![0, 1; -1, 0] : Op (Fin 2)) * M⁻¹.transpose * (!![0, 1; -1, 0] : Op (Fin 2))ᴴ =
      M.det⁻¹ • M := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.vecMul,
      dotProduct] <;> ring

end X7CG

open X7CG in
theorem solution (ell : ℕ) :
    (dualCG ell)ᴴ * dualCG ell = 1 ∧ dualCG ell * (dualCG ell)ᴴ = 1 ∧
    ∀ M : Op (Fin 2), M.det ≠ 0 →
      dualCG ell * Matrix.kronecker M⁻¹.transpose (polynomialIrrep ell M) * (dualCG ell)ᴴ =
        blockDiagonal (lowerDualAction ell M) (M.det⁻¹ • polynomialIrrep (ell+1) M) := by
  have hK : (Matrix.kronecker (!![0, 1; -1, 0] : Op (Fin 2)) (1 : Op (Fin (ell + 1))))ᴴ *
      Matrix.kronecker (!![0, 1; -1, 0] : Op (Fin 2)) (1 : Op (Fin (ell + 1))) = 1 := by
    rw [g74q_kct, g74q_kmul, X7_SS, Matrix.conjTranspose_one, Matrix.one_mul, g74q_k11]
  have hK' : Matrix.kronecker (!![0, 1; -1, 0] : Op (Fin 2)) (1 : Op (Fin (ell + 1))) *
      (Matrix.kronecker (!![0, 1; -1, 0] : Op (Fin 2)) (1 : Op (Fin (ell + 1))))ᴴ = 1 := by
    rw [g74q_kct, g74q_kmul, X7_SS', Matrix.conjTranspose_one, Matrix.one_mul, g74q_k11]
  refine ⟨?_, ?_, ?_⟩
  · rw [dualCG, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (ordinaryCG ell)ᴴ,
      g74q_OhO, Matrix.one_mul, hK]
  · rw [dualCG, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (ordinaryCG ell)ᴴ,
      hK', Matrix.one_mul, g74q_OOh]
  · intro M hM
    have e : Matrix.kronecker (!![0, 1; -1, 0] : Op (Fin 2)) (1 : Op (Fin (ell + 1))) *
        Matrix.kronecker M⁻¹.transpose (polynomialIrrep ell M) *
        (Matrix.kronecker (!![0, 1; -1, 0] : Op (Fin 2)) (1 : Op (Fin (ell + 1))))ᴴ =
        M.det⁻¹ • Matrix.kronecker M (polynomialIrrep ell M) := by
      rw [g74q_kct, g74q_kmul, g74q_kmul, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one,
        X7_SMS M hM]
      ext ⟨a, b⟩ ⟨c, d⟩
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
      ring
    have e2 : dualCG ell * Matrix.kronecker M⁻¹.transpose (polynomialIrrep ell M) * (dualCG ell)ᴴ =
        M.det⁻¹ • (ordinaryCG ell * Matrix.kronecker M (polynomialIrrep ell M) * (ordinaryCG ell)ᴴ) := by
      have : dualCG ell * Matrix.kronecker M⁻¹.transpose (polynomialIrrep ell M) * (dualCG ell)ᴴ =
          ordinaryCG ell * (Matrix.kronecker (!![0, 1; -1, 0] : Op (Fin 2)) (1 : Op (Fin (ell + 1))) *
          Matrix.kronecker M⁻¹.transpose (polynomialIrrep ell M) *
          (Matrix.kronecker (!![0, 1; -1, 0] : Op (Fin 2)) (1 : Op (Fin (ell + 1))))ᴴ) *
          (ordinaryCG ell)ᴴ := by
        rw [dualCG, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      rw [this, e, Matrix.mul_smul, Matrix.smul_mul]
    rw [e2, X7_cg_main]
    ext r s
    rcases r with j | j <;> rcases s with k | k <;>
      simp [blockDiagonal, lowerCGAction, lowerDualAction, hM]

end
