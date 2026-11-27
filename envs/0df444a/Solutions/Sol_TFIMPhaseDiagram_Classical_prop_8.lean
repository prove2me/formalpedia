-- Prove2me | solution 1 for TFIMPhaseDiagram.Classical.prop_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:08:37.649331+00:00
-- url     : https://prove2.me/submissions/4b18899f-ea02-4daa-8228-08ebf6262670

import Theorems.Thm_TFIMPhaseDiagram_Classical_prop_7

set_option autoImplicit false
open scoped BigOperators Nat
noncomputable section

namespace TFIMPhaseDiagram.Classical.P8Aux
open TFIMPhaseDiagram.Classical Matrix

lemma localZ_eq {n : ℕ} (i : Fin n) :
    localPauli .Z i = diagonal (fun a : Bits n => if a i then (-1 : ℂ) else 1) := by
  ext a b
  simp only [localPauli, pauliString, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    rw [Finset.prod_eq_single i]
    · simp [pauliEntry, QAlgorithms.pauliZ]
    · intro k _ hk; simp [hk, pauliEntry]
    · simp
  · rw [if_neg hab]
    obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
      by_contra h; push Not at h; exact hab (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    by_cases hki : k = i
    · simp [hki, pauliEntry, QAlgorithms.pauliZ, diagonal_apply]
      subst hki; simp [hk]
    · simp [hki, pauliEntry, hk]

def flipAt {n : ℕ} (i : Fin n) (a : Bits n) : Bits n := Function.update a i (!(a i))

lemma flipAt_flipAt {n : ℕ} (i : Fin n) (a : Bits n) : flipAt i (flipAt i a) = a := by
  funext k; unfold flipAt; by_cases h : k = i
  · subst h; simp
  · simp [Function.update_of_ne h]

lemma flipAt_comm {n : ℕ} (i j : Fin n) (a : Bits n) : flipAt i (flipAt j a) = flipAt j (flipAt i a) := by
  funext k; unfold flipAt
  by_cases hi : k = i <;> by_cases hj : k = j
  · subst hi; subst hj; rfl
  · subst hi; simp [Function.update_of_ne hj, Function.update_of_ne (Ne.symm hj)]
  · subst hj; simp [Function.update_of_ne hi, Function.update_of_ne (Ne.symm hi)]
  · simp [Function.update_of_ne hi, Function.update_of_ne hj]

lemma localX_eq {n : ℕ} (i : Fin n) :
    localPauli .X i = Matrix.of (fun a b : Bits n => if b = flipAt i a then (1 : ℂ) else 0) := by
  ext a b
  simp only [localPauli, pauliString, Matrix.of_apply]
  by_cases hb : b = flipAt i a
  · rw [if_pos hb]; subst hb
    apply Finset.prod_eq_one; intro k _
    by_cases hk : k = i
    · subst hk; simp [pauliEntry, QAlgorithms.pauliX, flipAt]
    · simp [hk, pauliEntry, flipAt, Function.update_apply, Matrix.one_apply]
  · rw [if_neg hb]
    have : ∃ k, ¬ (if k = i then a k ≠ b k else a k = b k) := by
      by_contra h; push Not at h; apply hb; funext k
      have := h k
      by_cases hk : k = i
      · subst hk; simp only [if_true] at this; unfold flipAt; simp
        cases ha : a k <;> cases hb' : b k <;> simp_all
      · simp only [hk, if_false] at this; unfold flipAt; rw [Function.update_of_ne hk]; exact this.symm
    obtain ⟨k, hk⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    by_cases hki : k = i
    · subst hki; simp only [if_true, not_not] at hk
      simp [pauliEntry, QAlgorithms.pauliX, hk]
    · simp only [hki, if_false] at hk
      simp [hki, pauliEntry, hk]

lemma perm_mul {n : ℕ} (f g : Bits n → Bits n) :
    (Matrix.of (fun a b : Bits n => if b = f a then (1 : ℂ) else 0)) *
      (Matrix.of (fun a b : Bits n => if b = g a then (1 : ℂ) else 0)) =
      Matrix.of (fun a b : Bits n => if b = g (f a) then (1 : ℂ) else 0) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']; simp

lemma X_comm {n : ℕ} (i j : Fin n) : Commute (localPauli .X i) (localPauli .X j) := by
  unfold Commute SemiconjBy
  rw [localX_eq, localX_eq, perm_mul, perm_mul]
  simp only [flipAt_comm j i]

lemma X_sq {n : ℕ} (i : Fin n) : localPauli .X i * localPauli .X i = 1 := by
  rw [localX_eq, perm_mul]
  ext a b; simp [flipAt_flipAt, Matrix.one_apply, eq_comm]

/-- the transverse transfer matrix -/
def Tm {n : ℕ} (θ : Fin n → ℝ) : QMat n :=
  Matrix.of fun a b => ∏ i, ((if a i = b i then Real.cosh (θ i) else Real.sinh (θ i) : ℝ) : ℂ)

lemma Tm_mul {n : ℕ} (θ θ' : Fin n → ℝ) : Tm θ * Tm θ' = Tm (θ + θ') := by
  ext a b
  simp only [Tm, Matrix.mul_apply, Matrix.of_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i c => ((if a i = c then Real.cosh (θ i) else Real.sinh (θ i) : ℝ) : ℂ) *
    ((if c = b i then Real.cosh (θ' i) else Real.sinh (θ' i) : ℝ) : ℂ))]
  · apply Finset.prod_congr rfl; intro i _
    rw [Fintype.sum_bool]
    simp only [Pi.add_apply]
    cases a i <;> cases b i <;> simp [Real.cosh_add, Real.sinh_add] <;> push_cast <;> ring

lemma Tm_zero {n : ℕ} : Tm (0 : Fin n → ℝ) = 1 := by
  ext a b
  simp only [Tm, Matrix.of_apply, Pi.zero_apply, Real.cosh_zero, Real.sinh_zero, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])


lemma pow_inv {n : ℕ} (A : QMat n) (hA : A * A = 1) (k : ℕ) : A ^ k = if Even k then 1 else A := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    by_cases hk : Even k
    · rw [if_pos hk, if_neg (by rw [Nat.even_add_one]; exact not_not.2 hk), one_mul]
    · rw [if_neg hk, if_pos (by rw [Nat.even_add_one]; exact hk), hA]

lemma hasSum_even_cosh (t : ℝ) :
    HasSum (fun k : ℕ => if Even k then t ^ k / (k ! : ℝ) else 0) (Real.cosh t) := by
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m) (fun a b h => by simpa using h) _)]
  · have e : (fun k : ℕ => if Even k then t ^ k / (k ! : ℝ) else 0) ∘ (fun m : ℕ => 2 * m) =
        fun m => t ^ (2 * m) / ((2 * m) ! : ℝ) := by
      funext m; simp
    rw [e]; exact Real.hasSum_cosh t
  · intro x hx; rw [if_neg]; rintro ⟨m, hm⟩; exact hx ⟨m, by simp only; omega⟩

lemma hasSum_odd_sinh (t : ℝ) :
    HasSum (fun k : ℕ => if Even k then 0 else t ^ k / (k ! : ℝ)) (Real.sinh t) := by
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m + 1) (fun a b h => by simpa using h) _)]
  · have e : (fun k : ℕ => if Even k then 0 else t ^ k / (k ! : ℝ)) ∘ (fun m : ℕ => 2 * m + 1) =
        fun m => t ^ (2 * m + 1) / ((2 * m + 1) ! : ℝ) := by
      funext m; simp [Nat.even_add_one]
    rw [e]; exact Real.hasSum_sinh t
  · intro x hx; rw [if_pos]; by_contra h
    obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.1 h
    exact hx ⟨m, by simp only; omega⟩

lemma exp_inv {n : ℕ} (A : QMat n) (hA : A * A = 1) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • A) = ((Real.cosh t : ℝ) : ℂ) • (1 : QMat n) + ((Real.sinh t : ℝ) : ℂ) • A := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  apply HasSum.tsum_eq
  have h1 := (Complex.hasSum_ofReal.2 (hasSum_even_cosh t)).smul_const (1 : QMat n)
  have h2 := (Complex.hasSum_ofReal.2 (hasSum_odd_sinh t)).smul_const A
  have e : (fun k : ℕ => ((k ! : ℂ)⁻¹) • (((t : ℂ) • A) ^ k)) = fun k =>
      ((if Even k then t ^ k / (k ! : ℝ) else 0 : ℝ) : ℂ) • (1 : QMat n) +
        ((if Even k then 0 else t ^ k / (k ! : ℝ) : ℝ) : ℂ) • A := by
    funext k
    rw [smul_pow, pow_inv A hA k, smul_smul]
    by_cases hk : Even k
    · rw [if_pos hk, if_pos hk, if_pos hk]; simp; ring
    · rw [if_neg hk, if_neg hk, if_neg hk]; simp; congr 1; ring
  rw [e]
  exact h1.add h2


lemma Tm_single {n : ℕ} (i : Fin n) (t : ℝ) :
    Tm (Pi.single i t) = ((Real.cosh t : ℝ) : ℂ) • (1 : QMat n) + ((Real.sinh t : ℝ) : ℂ) • localPauli .X i := by
  ext a b
  rw [localX_eq]
  simp only [Tm, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hrest : ∏ k ∈ Finset.univ.erase i, (((if a k = b k then Real.cosh ((Pi.single i t : Fin n → ℝ) k)
      else Real.sinh ((Pi.single i t : Fin n → ℝ) k)) : ℝ) : ℂ) = if ∀ k, k ≠ i → a k = b k then 1 else 0 := by
    split_ifs with h
    · apply Finset.prod_eq_one; intro k hk
      have hki : k ≠ i := (Finset.mem_erase.1 hk).1
      simp [h k hki, Pi.single_apply, hki]
    · push Not at h; obtain ⟨k, hki, hk⟩ := h
      apply Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hki, Finset.mem_univ k⟩)
      simp [hk, Pi.single_apply, hki]
  rw [hrest]
  simp only [Pi.single_eq_same]
  by_cases hab : a i = b i
  · rw [if_pos hab]
    have hf : ¬ b = flipAt i a := by
      intro h; have := congrFun h i; simp [flipAt] at this; rw [this] at hab
      cases a i <;> simp at hab
    rw [if_neg hf, add_zero]
    by_cases h : ∀ k, k ≠ i → a k = b k
    · have : a = b := funext fun k => by by_cases hk : k = i; subst hk; exact hab; exact h k hk
      rw [if_pos h, if_pos this, mul_one]
    · have : a ≠ b := fun e => h (fun k _ => by rw [e])
      rw [if_neg h, if_neg this, mul_zero]
  · rw [if_neg hab]
    have hne : a ≠ b := fun e => hab (by rw [e])
    rw [if_neg hne, zero_add]
    by_cases h : ∀ k, k ≠ i → a k = b k
    · have : b = flipAt i a := by
        funext k; unfold flipAt
        by_cases hk : k = i
        · subst hk; simp; cases ha : a k <;> cases hb : b k <;> simp_all
        · rw [Function.update_of_ne hk]; exact (h k hk).symm
      rw [if_pos h, if_pos this, mul_one]
    · have : ¬ b = flipAt i a := by
        intro e; apply h; intro k hk; rw [e]; unfold flipAt; rw [Function.update_of_ne hk]
      rw [if_neg h, if_neg this, mul_zero]

lemma exp_hx_partial {n : ℕ} (θ : Fin n → ℝ) (s : Finset (Fin n)) :
    NormedSpace.exp (∑ i ∈ s, ((θ i : ℝ) : ℂ) • localPauli .X i) =
      Tm (fun i => if i ∈ s then θ i else 0) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, NormedSpace.exp_zero, Finset.notMem_empty, if_false]
    exact Tm_zero.symm
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Matrix.exp_add_of_commute]
    · rw [ih, exp_inv _ (X_sq j), ← Tm_single, Tm_mul]
      congr 1; funext i
      simp only [Pi.add_apply, Finset.mem_insert]
      by_cases hij : i = j
      · subst hij; simp [hj]
      · simp [hij, Pi.single_apply]
    · apply Commute.sum_right; intro i _
      exact ((X_comm j i).smul_left _).smul_right _

lemma exp_hx {n : ℕ} (η : Fin n → ℝ) (M : ℕ) :
    NormedSpace.exp ((1 / (M : ℂ)) • hx η) = Tm (fun i => η i / M) := by
  have : (1 / (M : ℂ)) • hx η = ∑ i, (((η i / M : ℝ)) : ℂ) • localPauli .X i := by
    unfold hx; rw [Finset.smul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [smul_smul]; congr 1; push_cast; ring
  rw [this, exp_hx_partial]
  congr 1; funext i; simp

lemma hz_diag {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) :
    hz J h = diagonal (fun a : Bits n => ((potential J h (fun i => spin (a i)) : ℝ) : ℂ)) := by
  unfold hz
  simp only [localZ_eq, diagonal_mul_diagonal]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, diagonal_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    simp only [if_true, potential, spin]
    push_cast
    simp only [Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      split_ifs <;> push_cast <;> ring
    · apply Finset.sum_congr rfl; intro i _
      split_ifs <;> push_cast <;> ring
  · simp [hab]

lemma exp_hz {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (M : ℕ) :
    NormedSpace.exp ((1 / (M : ℂ)) • hz J h) =
      diagonal (fun a : Bits n => ((Real.exp (potential J h (fun i => spin (a i)) / M) : ℝ) : ℂ)) := by
  rw [hz_diag, ← diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  congr 1; funext a
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]
  congr 1; push_cast; ring


lemma pow_expand {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) (m : ℕ) (a c : ι) :
    (B ^ m) a c = ∑ x : Fin m → ι, (∏ k : Fin m,
      B ((Fin.cons a x : Fin (m+1) → ι) k.castSucc) ((Fin.cons a x : Fin (m+1) → ι) k.succ)) *
        (if (Fin.cons a x : Fin (m+1) → ι) (Fin.last m) = c then 1 else 0) := by
  induction m generalizing a with
  | zero => simp [Matrix.one_apply]
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih]
    rw [← (Fin.consEquiv (fun _ : Fin (m+1) => ι)).sum_comp]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ,
      ← Fin.succ_castSucc]
    rw [← Fin.succ_last, Fin.cons_succ, Fin.consEquiv_apply]
    ring

lemma trace_expand {ι : Type} [Fintype ι] [DecidableEq ι] (O B : Matrix ι ι ℂ) (m : ℕ) :
    Matrix.trace (O * B ^ m) = ∑ y : Fin (m+1) → ι, O (y (Fin.last m)) (y 0) *
      ∏ k : Fin m, B (y k.castSucc) (y k.succ) := by
  unfold Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, pow_expand]
  rw [← (Fin.consEquiv (fun _ : Fin (m+1) => ι)).sum_comp, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  simp only [Fin.consEquiv_apply, Fin.cons_zero]
  rw [Finset.sum_eq_single ((Fin.cons c x : Fin (m+1) → ι) (Fin.last m))]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp


def gfun {n : ℕ} (θ : Fin n → ℝ) (i : Fin n) (a b : Bool) : ℂ :=
  ((if a = b then Real.cosh (θ i) else Real.sinh (θ i) : ℝ) : ℂ)
def clos {n : ℕ} (P : Fin n → Pauli) (θ : Fin n → ℝ) (i : Fin n) (a b : Bool) : ℂ :=
  ∑ β : Bool, pauliEntry (P i) β b * gfun θ i a β
def Gk {n m : ℕ} (P : Fin n → Pauli) (θ : Fin n → ℝ) (i : Fin n) (k : Fin (m+1)) (a b : Bool) : ℂ :=
  if k = Fin.last m then clos P θ i a b else gfun θ i a b

lemma next_cs {m : ℕ} (j : Fin m) : next (j.castSucc : Fin (m+1)) = j.succ := by
  ext; simp only [next, Fin.val_castSucc, Fin.val_succ]; exact Nat.mod_eq_of_lt (by omega)
lemma next_lst {m : ℕ} : next (Fin.last m : Fin (m+1)) = 0 := by
  ext; simp [next]

lemma master {n m : ℕ} (P : Fin n → Pauli) (d : Bits n → ℂ) (θ : Fin n → ℝ) :
    Matrix.trace (pauliString P * (diagonal d * Tm θ) ^ (m+1)) =
      ∑ x : Fin (m+1) → Bits n, (∏ k, d (x k)) *
        ∏ i, ∏ k : Fin (m+1), Gk P θ i k (x k i) (x (next k) i) := by
  rw [trace_expand]
  rw [← (Fin.snocEquiv (fun _ : Fin (m+2) => Bits n)).sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  simp only [Fin.snocEquiv_apply]
  -- rewrite the product over steps
  have hsteps : ∀ b : Bits n, ∏ k : Fin (m+1), (diagonal d * Tm θ)
      ((Fin.snoc x b : Fin (m+2) → Bits n) k.castSucc) ((Fin.snoc x b : Fin (m+2) → Bits n) k.succ) =
      (∏ k, d (x k)) * ((∏ j : Fin m, Tm θ (x j.castSucc) (x j.succ)) * Tm θ (x (Fin.last m)) b) := by
    intro b
    simp only [Matrix.diagonal_mul, Fin.snoc_castSucc]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc (f := fun k => d (x k))]
    simp only [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_last,
      Finset.prod_mul_distrib]
    ring
  simp only [hsteps]
  have h0 : ∀ b : Bits n, (Fin.snoc x b : Fin (m+2) → Bits n) 0 = x 0 := fun b => by
    rw [show (0 : Fin (m+2)) = (0 : Fin (m+1)).castSucc from rfl, Fin.snoc_castSucc]
  simp only [h0, Fin.snoc_last]
  -- sum over b
  have hb : ∑ b : Bits n, pauliString P b (x 0) * ((∏ k, d (x k)) *
      ((∏ j : Fin m, Tm θ (x j.castSucc) (x j.succ)) * Tm θ (x (Fin.last m)) b)) =
      (∏ k, d (x k)) * ((∏ j : Fin m, Tm θ (x j.castSucc) (x j.succ)) *
        ∏ i, clos P θ i (x (Fin.last m) i) (x 0 i)) := by
    have : ∀ b : Bits n, pauliString P b (x 0) * Tm θ (x (Fin.last m)) b =
        ∏ i, pauliEntry (P i) (b i) (x 0 i) * gfun θ i (x (Fin.last m) i) (b i) := by
      intro b; simp only [pauliString, Tm, Matrix.of_apply, gfun, ← Finset.prod_mul_distrib]
    calc _ = (∏ k, d (x k)) * ((∏ j : Fin m, Tm θ (x j.castSucc) (x j.succ)) *
          ∑ b : Bits n, pauliString P b (x 0) * Tm θ (x (Fin.last m)) b) := by
            rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
      _ = _ := by
            simp only [this]
            rw [← Fintype.prod_sum (fun i β => pauliEntry (P i) β (x 0 i) *
              gfun θ i (x (Fin.last m) i) β)]
            rfl
  rw [hb]
  congr 1
  -- reorganize per site
  simp only [Tm, Matrix.of_apply]
  rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro i _
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl; intro j _
    simp only [Gk, next_cs, gfun]
    rw [if_neg (Fin.castSucc_lt_last j).ne]
  · simp only [Gk, next_lst, if_pos]


lemma clos_eval {n : ℕ} (P : Fin n → Pauli) (θ : Fin n → ℝ) (i : Fin n) (a b : Bool) :
    clos P θ i a b = (if P i = .Y then Complex.I else 1) *
      (if P i = .Y ∨ P i = .Z then ((spin b : ℝ) : ℂ) else 1) * gfun θ i a (xor b (hasFlip (P i))) := by
  unfold clos
  rw [Fintype.sum_bool]
  cases h : P i <;> cases a <;> cases b <;>
    simp [pauliEntry, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, gfun, hasFlip,
      spin, Matrix.one_apply, Matrix.diagonal_apply]

def twist {m : ℕ} (p : Bool) (σ : Fin (m+1) → Bool) (k : Fin (m+1)) : Bool :=
  if k = Fin.last m then xor (σ 0) p else σ (next k)
def cycG {m : ℕ} (θ : ℝ) (p : Bool) (σ : Fin (m+1) → Bool) : ℂ :=
  ∏ k, ((if σ k = twist p σ k then Real.cosh θ else Real.sinh θ : ℝ) : ℂ)

lemma site_prod {n m : ℕ} (P : Fin n → Pauli) (θ : Fin n → ℝ) (i : Fin n) (σ : Fin (m+1) → Bool) :
    ∏ k : Fin (m+1), Gk P θ i k (σ k) (σ (next k)) =
      (if P i = .Y then Complex.I else 1) *
      (if P i = .Y ∨ P i = .Z then ((spin (σ 0) : ℝ) : ℂ) else 1) * cycG (θ i) (hasFlip (P i)) σ := by
  unfold cycG
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc (f := fun k => ((if σ k = twist (hasFlip (P i)) σ k
    then Real.cosh (θ i) else Real.sinh (θ i) : ℝ) : ℂ))]
  have hc : ∀ j : Fin m, Gk P θ i j.castSucc (σ j.castSucc) (σ (next j.castSucc)) =
      ((if σ j.castSucc = twist (hasFlip (P i)) σ j.castSucc then Real.cosh (θ i) else Real.sinh (θ i) : ℝ) : ℂ) := by
    intro j
    simp only [Gk, twist, if_neg (Fin.castSucc_lt_last j).ne, gfun]
  simp only [hc]
  rw [show Gk P θ i (Fin.last m) (σ (Fin.last m)) (σ (next (Fin.last m))) =
    clos P θ i (σ (Fin.last m)) (σ 0) by simp [Gk, next_lst], clos_eval]
  simp only [twist, if_pos, gfun]
  ring


def cycR {m : ℕ} (θ : ℝ) (p : Bool) (σ : Fin (m+1) → Bool) : ℝ :=
  ∏ k, (if σ k = twist p σ k then Real.cosh θ else Real.sinh θ)

lemma cycG_eq {m : ℕ} (θ : ℝ) (p : Bool) (σ : Fin (m+1) → Bool) : cycG θ p σ = (cycR θ p σ : ℂ) := by
  unfold cycG cycR; push_cast; rfl

lemma spin_xor (a b : Bool) : spin a * spin b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> simp [spin]

lemma exp_half_log' (y : ℝ) (hy : 0 < y) : Real.exp ((1/2) * Real.log y) = Real.sqrt y := by
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _), ← Real.exp_add]
  rw [show 1 / 2 * Real.log y + 1 / 2 * Real.log y = Real.log y by ring, Real.exp_log hy]

lemma fieldEnergy_const {M : ℕ} (c : ℝ) (σ : Spins M) :
    fieldEnergy (fun _ : Fin M => Field.finite c) σ = ∑ k, c * spin (σ k) := rfl

lemma cyc_weight_pos {m : ℕ} (η : ℝ) (hη : 0 < η) (p : Bool) (c : ℝ) (σ : Fin (m+1) → Bool) :
    cycR (η / (m+1 : ℕ)) p σ * Real.exp (∑ k, c * spin (σ k)) =
      Real.sqrt (Real.cosh (η / (m+1 : ℕ)) * Real.sinh (η / (m+1 : ℕ))) ^ (m+1) *
        pathCycleWeight η p (fun _ => Field.finite c) σ := by
  have hx : 0 < η / (m+1 : ℕ) := by positivity
  set ch := Real.cosh (η / (m+1 : ℕ)); set sh := Real.sinh (η / (m+1 : ℕ))
  have hc : 0 < ch := Real.cosh_pos _
  have hs : 0 < sh := Real.sinh_pos_iff.2 hx
  have hK : Real.exp (coupling (m+1) η) = Real.sqrt (ch / sh) := by
    unfold coupling; exact exp_half_log' _ (div_pos hc hs)
  have hKn : Real.exp (-coupling (m+1) η) = Real.sqrt (sh / ch) := by
    rw [Real.exp_neg, hK, ← Real.sqrt_inv, inv_div]
  have e1 : Real.sqrt (ch * sh) * Real.sqrt (ch / sh) = ch := by
    rw [← Real.sqrt_mul (by positivity), show ch * sh * (ch / sh) = ch ^ 2 by field_simp,
      Real.sqrt_sq hc.le]
  have e2 : Real.sqrt (ch * sh) * Real.sqrt (sh / ch) = sh := by
    rw [← Real.sqrt_mul (by positivity), show ch * sh * (sh / ch) = sh ^ 2 by field_simp,
      Real.sqrt_sq hs.le]
  have hfac : ∀ k : Fin (m+1), (if σ k = twist p σ k then ch else sh) =
      Real.sqrt (ch * sh) * Real.exp (signedCoupling η p k * spin (σ k) * spin (σ (next k))) := by
    intro k
    rw [mul_assoc, spin_xor]
    unfold twist signedCoupling
    by_cases hk : k = Fin.last m
    · have hkv : k.val + 1 = m + 1 := by rw [hk]; simp
      rw [if_pos hk, hk, next_lst]
      cases p <;> cases h0 : σ 0 <;> cases hl : σ (Fin.last m) <;>
        simp [hkv, hK, hKn, e1, e2]
    · have hkv : ¬ (k.val + 1 = m + 1) := by
        intro h; apply hk; ext; simp at h ⊢; omega
      rw [if_neg hk]
      simp only [hkv, false_and, if_false]
      by_cases he : σ k = σ (next k)
      · rw [if_pos he, if_pos he, mul_one, hK, e1]
      · rw [if_neg he, if_neg he, mul_neg_one, hKn, e2]
  unfold cycR pathCycleWeight
  rw [if_neg hη.ne']
  unfold cycleWeight cycleEnergy
  rw [if_pos (show compatible (fun _ => Field.finite c) σ from fun k => trivial), fieldEnergy_const]
  rw [show (∏ k : Fin (m+1), (if σ k = twist p σ k then Real.cosh (η / (m+1 : ℕ))
      else Real.sinh (η / (m+1 : ℕ)))) = ∏ k : Fin (m+1), (Real.sqrt (ch * sh) *
        Real.exp (signedCoupling η p k * spin (σ k) * spin (σ (next k)))) from
      Finset.prod_congr rfl (fun k _ => hfac k)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum,
    mul_assoc, ← Real.exp_add]

lemma ind_all {m : ℕ} (Q : Fin (m+1) → Prop) [DecidablePred Q]
    (hc : ∀ k ∈ (Finset.univ : Finset (Fin (m+1))), (if Q k then (1:ℝ) else 0) ≠ 0) : ∀ k, Q k :=
  fun k => by by_contra h; exact hc k (Finset.mem_univ k) (if_neg h)

lemma cyc_weight_zero {m : ℕ} (p : Bool) (c : ℝ) (σ : Fin (m+1) → Bool) :
    cycR (0 / (m+1 : ℕ)) p σ * Real.exp (∑ k, c * spin (σ k)) =
      (if p then 0 else 2) * pathCycleWeight 0 p (fun _ => Field.finite c) σ := by
  unfold pathCycleWeight
  rw [if_pos rfl, if_pos (show compatible (fun _ => Field.finite c) σ from fun k => trivial),
    fieldEnergy_const, zero_div]
  unfold cycR
  simp only [Real.cosh_zero, Real.sinh_zero]
  -- product of indicators
  have hall : (∀ k, σ k = twist p σ k) → p = false ∧ ∀ k, σ k = σ 0 := by
    intro h
    have hconst : ∀ j (hj : j < m + 1), σ ⟨j, hj⟩ = σ 0 := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        have := h ⟨j, by omega⟩
        unfold twist at this
        rw [if_neg (by intro e; have := congrArg Fin.val e; simp at this; omega)] at this
        have hn : next (⟨j, by omega⟩ : Fin (m+1)) = ⟨j+1, hj⟩ := by
          ext; simp [next, Nat.mod_eq_of_lt hj]
        rw [hn] at this
        rw [← this]; exact ih (by omega)
    have hl := h (Fin.last m)
    unfold twist at hl
    rw [if_pos rfl] at hl
    have h2 := hconst m (by omega)
    rw [show (⟨m, by omega⟩ : Fin (m+1)) = Fin.last m from rfl] at h2
    rw [h2] at hl
    refine ⟨?_, fun k => hconst k.val k.isLt⟩
    cases p <;> cases σ 0 <;> simp_all
  unfold zeroCycleBase
  by_cases hp : p
  · subst hp
    simp only [if_true, zero_mul]
    rw [Finset.prod_eq_zero_iff.2]
    · simp
    · by_contra hc; push Not at hc
      have := hall (ind_all _ hc)
      simp at this
  · simp only [Bool.not_eq_true] at hp; subst hp
    simp only [Bool.false_eq_true, if_false]
    by_cases hcst : ∀ k, σ k = σ 0
    · have h1 : ∏ k : Fin (m+1), (if σ k = twist false σ k then (1:ℝ) else 0) = 1 := by
        apply Finset.prod_eq_one; intro k _
        rw [if_pos]; unfold twist; split_ifs
        · simp [hcst k]
        · rw [hcst k, hcst (next k)]
      rw [h1, one_mul]
      have hs : σ = fun _ => σ 0 := funext hcst
      rw [Fintype.sum_bool]
      cases h0 : σ 0 <;> rw [h0] at hs <;> subst hs <;> simp <;>
        rw [if_neg (fun e => by have := congrFun e 0; simp at this)] <;> ring
    · have h1 : ∏ k : Fin (m+1), (if σ k = twist false σ k then (1:ℝ) else 0) = 0 := by
        rw [Finset.prod_eq_zero_iff]
        by_contra hc; push Not at hc
        apply hcst; exact (hall (ind_all _ hc)).2
      rw [h1, zero_mul]
      have ht : σ ≠ fun _ => true := fun e => hcst (fun k => by rw [e])
      have hf : σ ≠ fun _ => false := fun e => hcst (fun k => by rw [e])
      rw [Fintype.sum_bool]; simp [ht, hf]


lemma trotter_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) (M : ℕ) :
    trotter J h η M = (diagonal (fun a : Bits n =>
      ((Real.exp (potential J h (fun i => spin (a i)) / M) : ℝ) : ℂ)) * Tm (fun i => η i / M)) ^ M := by
  unfold trotter matrixExp; rw [exp_hz, exp_hx]

lemma phase_prod {n : ℕ} (P : Fin n → Pauli) :
    ∏ i, (if P i = .Y then Complex.I else 1) = Complex.I ^ yCount P := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]; rfl

lemma sfac_prod {n m : ℕ} (P : Fin n → Pauli) (s : Fin n → Spins (m+1)) :
    ∏ i, (if P i = .Y ∨ P i = .Z then ((spin (s i 0) : ℝ) : ℂ) else 1) = ((meshSign P s : ℝ) : ℂ) := by
  unfold meshSign
  push_cast
  apply Finset.prod_congr rfl; intro i _
  split_ifs
  · congr 1
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk; rw [if_neg]; intro h; apply hk; ext; exact h
    · simp
  · rfl

lemma energy_sum {n M : ℕ} (hM : 0 < M) (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ)
    (s : Fin n → Spins M) :
    ∑ k : Fin M, potential J h (fun i => spin (s i k)) / M =
      cycleInteraction J s + ∑ i, ∑ k, (h i / M) * spin (s i k) := by
  unfold potential cycleInteraction
  simp only [add_div, Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    ring
  · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring

theorem trotter_trace {n m : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) (P : Fin n → Pauli) :
    Matrix.trace (pauliString P * trotter J h η (m+1)) = Complex.I ^ yCount P *
      ∑ s : Fin n → Spins (m+1), ((Real.exp (cycleInteraction J s) * meshSign P s *
        ∏ i, (cycR (η i / (m+1 : ℕ)) (hasFlip (P i)) (s i) *
          Real.exp (∑ k, (h i / (m+1 : ℕ)) * spin (s i k))) : ℝ) : ℂ) := by
  rw [trotter_eq, master]
  rw [← (Equiv.piComm (fun (_ : Fin n) (_ : Fin (m+1)) => Bool)).sum_comp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  simp only [Equiv.piComm_apply, Function.swap]
  simp only [site_prod, Finset.prod_mul_distrib, phase_prod, sfac_prod P s, cycG_eq]
  have hd : ∏ k : Fin (m+1), ((Real.exp (potential J h (fun i => spin (s i k)) / (m+1 : ℕ)) : ℝ) : ℂ) =
      ((Real.exp (cycleInteraction J s) * ∏ i, Real.exp (∑ k, (h i / (m+1 : ℕ)) * spin (s i k)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum]
    congr 1
    rw [← Real.exp_sum, ← Real.exp_add]; congr 1
    exact energy_sum (Nat.succ_pos m) J h s
  rw [hd]
  push_cast
  ring


open MeasureTheory

instance finiteLaw_isFinite {A : Type} [Fintype A] [MeasurableSpace A] (q : A → ℝ) :
    IsFiniteMeasure (finiteLaw q) := by
  constructor
  unfold finiteLaw
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  exact ENNReal.sum_lt_top.2 (fun x _ => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))

lemma finiteLaw_singleton' {A : Type} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [DecidableEq A] (q : A → ℝ) (s : A) : finiteLaw q {s} = ENNReal.ofReal (q s) := by
  unfold finiteLaw
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton s),
    Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']; simp

lemma integral_pi_finite {n M : ℕ} (q : Fin n → Spins M → ℝ) (hq : ∀ i s, 0 ≤ q i s)
    (F : (Fin n → Spins M) → ℝ) :
    ∫ s, F s ∂(Measure.pi (fun i => finiteLaw (q i))) = ∑ s, (∏ i, q i (s i)) * F s := by
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl; intro s _
  rw [smul_eq_mul]
  congr 1
  rw [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl; intro i _
  rw [finiteLaw_singleton', ENNReal.toReal_ofReal (hq i (s i))]


def Aw {m : ℕ} (θ c : ℝ) (p : Bool) (σ : Fin (m+1) → Bool) : ℝ :=
  cycR θ p σ * Real.exp (∑ k, c * spin (σ k))
def kap (m : ℕ) (η : ℝ) (p : Bool) : ℝ :=
  if η = 0 then (if p then 0 else 2)
  else Real.sqrt (Real.cosh (η / (m+1 : ℕ)) * Real.sinh (η / (m+1 : ℕ))) ^ (m+1)

lemma Aw_eq {m : ℕ} (η : ℝ) (hη : 0 ≤ η) (p : Bool) (c : ℝ) (σ : Fin (m+1) → Bool) :
    Aw (η / (m+1 : ℕ)) c p σ = kap m η p * pathCycleWeight η p (fun _ => Field.finite c) σ := by
  unfold Aw kap
  by_cases h0 : η = 0
  · subst h0; rw [if_pos rfl]; exact cyc_weight_zero p c σ
  · rw [if_neg h0]; exact cyc_weight_pos η (lt_of_le_of_ne hη (Ne.symm h0)) p c σ

lemma kap_nonneg (m : ℕ) (η : ℝ) (p : Bool) : 0 ≤ kap m η p := by
  unfold kap; split_ifs <;> positivity

lemma pcw_nonneg {M : ℕ} (η : ℝ) (hη : 0 ≤ η) (p : Bool) (c : ℝ) (σ : Spins M) :
    0 ≤ pathCycleWeight η p (fun _ => Field.finite c) σ := by
  unfold pathCycleWeight zeroCycleBase cycleWeight
  split_ifs <;> positivity

lemma pcw_sum_pos {m : ℕ} (η : ℝ) (hη : 0 ≤ η) (p : Bool) (c : ℝ) :
    0 < ∑ σ : Spins (m+1), pathCycleWeight η p (fun _ => Field.finite c) σ := by
  have hc : ∀ σ : Spins (m+1), compatible (fun _ : Fin (m+1) => Field.finite c) σ := fun σ k => trivial
  have key : ∃ σ : Spins (m+1), 0 < pathCycleWeight η p (fun _ => Field.finite c) σ := by
    by_cases h0 : η = 0
    · subst h0
      cases p
      · refine ⟨fun _ => false, ?_⟩
        unfold pathCycleWeight zeroCycleBase
        have hne : (fun _ : Fin (m+1) => false) ≠ fun _ => true := fun e => by
          have := congrFun e 0; simp at this
        rw [if_pos rfl, if_pos (hc _), if_neg (by decide), Fintype.sum_bool, if_neg hne, if_pos rfl]
        positivity
      · refine ⟨oneJump false 0, ?_⟩
        unfold pathCycleWeight zeroCycleBase
        rw [if_pos rfl, if_pos (hc _)]
        simp only [if_true]
        apply mul_pos _ (Real.exp_pos _)
        apply div_pos _ (by positivity)
        apply lt_of_lt_of_le (zero_lt_one) 
        calc (1:ℝ) = if oneJump false 0 = oneJump false (0 : Fin (m+1)) then 1 else 0 := by simp
          _ ≤ ∑ r : Fin (m+1), if oneJump false 0 = oneJump false r then (1:ℝ) else 0 :=
              Finset.single_le_sum (f := fun r : Fin (m+1) => if oneJump false 0 = oneJump false r then (1:ℝ) else 0)
                (fun r _ => by split_ifs <;> norm_num) (Finset.mem_univ 0)
          _ ≤ ∑ u : Bool, ∑ r : Fin (m+1), if oneJump false 0 = oneJump u r then (1:ℝ) else 0 := by
              rw [Fintype.sum_bool]
              have : 0 ≤ ∑ r : Fin (m+1), (if oneJump false 0 = oneJump true r then (1:ℝ) else 0) :=
                Finset.sum_nonneg (fun r _ => by split_ifs <;> norm_num)
              linarith
    · refine ⟨fun _ => false, ?_⟩
      unfold pathCycleWeight cycleWeight
      rw [if_neg h0, if_pos (hc _)]; positivity
  obtain ⟨σ, hσ⟩ := key
  exact lt_of_lt_of_le hσ (Finset.single_le_sum (fun τ _ => pcw_nonneg η hη p c τ) (Finset.mem_univ σ))


abbrev wgt {n : ℕ} (m : ℕ) (h η : Fin n → ℝ) (P : Fin n → Pauli) (i : Fin n) (σ : Spins (m+1)) : ℝ :=
  pathCycleWeight (η i) (hasFlip (P i)) (fun _ => Field.finite (h i / (m+1 : ℕ))) σ

lemma xSubset_eq {n : ℕ} (P : Fin n → Pauli) :
    xSubset (flipSet P) = pauliString (fun i => if hasFlip (P i) then Pauli.X else Pauli.I) := by
  unfold xSubset flipSet; congr 1; funext i; simp

lemma D_formula {n m : ℕ} (h η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i) (P : Fin n → Pauli) :
    Matrix.trace (xSubset (flipSet P) * trotter 0 h η (m+1)) =
      ((∏ i, kap m (η i) (hasFlip (P i)) * ∑ σ, wgt m h η P i σ : ℝ) : ℂ) := by
  rw [xSubset_eq, trotter_trace]
  have hy : yCount (fun i => if hasFlip (P i) then Pauli.X else Pauli.I) = 0 := by
    unfold yCount; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _; by_cases hf : hasFlip (P i) <;> simp [hf]
  have hmesh : ∀ s : Fin n → Spins (m+1),
      meshSign (fun i => if hasFlip (P i) then Pauli.X else Pauli.I) s = 1 := by
    intro s; unfold meshSign; apply Finset.prod_eq_one; intro i _
    by_cases hf : hasFlip (P i) <;> simp [hf]
  have hflip : ∀ i, hasFlip (if hasFlip (P i) then Pauli.X else Pauli.I) = hasFlip (P i) := by
    intro i; split_ifs with h1 <;> simp_all [hasFlip]
  have hW : ∀ s : Fin n → Spins (m+1), cycleInteraction (0 : Matrix (Fin n) (Fin n) ℝ) s = 0 := by
    intro s; simp [cycleInteraction]
  simp only [hy, pow_zero, one_mul, hmesh, hflip, hW, Real.exp_zero, mul_one, one_mul]
  rw [← Complex.ofReal_sum]
  congr 1
  rw [← Fintype.prod_sum (fun i σ => cycR (η i / (m+1 : ℕ)) (hasFlip (P i)) σ *
    Real.exp (∑ k, h i / (m+1 : ℕ) * spin (σ k)))]
  apply Finset.prod_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro σ _
  exact Aw_eq (η i) (hη i) _ _ σ

theorem identity3 {n m : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i)
    (P : Fin n → Pauli) :
    Matrix.trace (pauliString P * trotter J h η (m+1)) =
      Complex.I ^ yCount P * Matrix.trace (xSubset (flipSet P) * trotter 0 h η (m+1)) *
        (∫ s, Real.exp (cycleInteraction J s) * meshSign P s ∂nuTilde (M := m+1) h η P : ℝ) := by
  rw [trotter_trace, D_formula h η hη P]
  unfold nuTilde pathCycleLaw
  rw [integral_pi_finite _ (fun i σ => by
    unfold pathCycleProb normalize
    exact div_nonneg (pcw_nonneg _ (hη i) _ _ σ) (Finset.sum_nonneg (fun τ _ => pcw_nonneg _ (hη i) _ _ τ)))]
  have hZ : ∀ i, (∑ σ, wgt m h η P i σ) ≠ 0 := fun i => (pcw_sum_pos (η i) (hη i) _ _).ne'
  have key : ∀ s : Fin n → Spins (m+1), Real.exp (cycleInteraction J s) * meshSign P s *
      ∏ i, (cycR (η i / (m+1 : ℕ)) (hasFlip (P i)) (s i) * Real.exp (∑ k, h i / (m+1 : ℕ) * spin (s i k))) =
      (∏ i, kap m (η i) (hasFlip (P i)) * ∑ σ, wgt m h η P i σ) *
        ((∏ i, pathCycleProb (η i) (hasFlip (P i)) (fun _ => Field.finite (h i / (m+1 : ℕ))) (s i)) *
          (Real.exp (cycleInteraction J s) * meshSign P s)) := by
    intro s
    have hprod : (∏ i, kap m (η i) (hasFlip (P i)) * ∑ σ, wgt m h η P i σ) *
        (∏ i, pathCycleProb (η i) (hasFlip (P i)) (fun _ => Field.finite (h i / (m+1 : ℕ))) (s i)) =
        ∏ i, (cycR (η i / (m+1 : ℕ)) (hasFlip (P i)) (s i) * Real.exp (∑ k, h i / (m+1 : ℕ) * spin (s i k))) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      have := Aw_eq (η i) (hη i) (hasFlip (P i)) (h i / (m+1 : ℕ)) (s i)
      unfold Aw at this
      rw [this]
      unfold pathCycleProb normalize
      field_simp [hZ i]
    rw [← mul_assoc, hprod]; ring
  rw [mul_assoc]
  congr 1
  rw [← Complex.ofReal_sum, ← Complex.ofReal_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  exact key s


lemma neg_one_pow_pm (c : ℕ) : (-1 : ℝ) ^ c = 1 ∨ (-1 : ℝ) ^ c = -1 := by
  rcases Nat.even_or_odd c with h | h
  · left; exact h.neg_one_pow
  · right; exact h.neg_one_pow

lemma pathValue_spin (σ : PathData) (t : ℝ) : pathValue σ t = spin (pathBits σ t) := by
  unfold pathBits pathValue
  rcases neg_one_pow_pm ((Finset.range σ.1).filter (fun k => σ.2.2 k ≤ t)).card with h | h <;>
    rw [h] <;> cases σ.2.1 <;> simp [spin] <;> norm_num

lemma meas_card' {ι : Type} (s : Finset ι) (t : ℝ) :
    Measurable (fun u : ι → ℝ => (s.filter (fun j => u j ≤ t)).card) := by
  have : (fun u : ι → ℝ => (s.filter (fun j => u j ≤ t)).card) =
      fun u => ∑ j ∈ s, (if u j ≤ t then 1 else 0) := by
    funext u; rw [Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ (fun j _ => Measurable.ite
    (measurableSet_le (measurable_pi_apply j) measurable_const) measurable_const measurable_const)

lemma pathValue_meas' (t : ℝ) : Measurable (fun σ : PathData => pathValue σ t) := by
  apply measurable_from_prod_countable_right
  intro d
  unfold pathValue
  simp only
  apply Measurable.mul
  · exact (measurable_of_countable (fun b : Bool => spin b)).comp measurable_fst
  · exact (measurable_of_countable (fun n : ℕ => (-1 : ℝ) ^ n)).comp
      ((meas_card' (Finset.range d) t).comp measurable_snd)

lemma discretize_meas' (M : ℕ) : Measurable (discretize M) := by
  apply measurable_pi_lambda
  intro k
  apply measurable_to_bool
  have : (fun σ : PathData => discretize M σ k) ⁻¹' {true} = {σ | pathValue σ (k.val / (M:ℝ)) < 0} := by
    ext σ; simp [discretize, pathBits]
  rw [this]
  exact measurableSet_lt (pathValue_meas' _) measurable_const

lemma matrixExp_hx_eq {n : ℕ} (η : Fin n → ℝ) (m : ℕ) :
    matrixExp (hx η) = trotter 0 0 η (m+1) := by
  unfold trotter matrixExp
  have hz0 : hz (0 : Matrix (Fin n) (Fin n) ℝ) (0 : Fin n → ℝ) = 0 := by simp [hz]
  rw [hz0, smul_zero, NormedSpace.exp_zero, one_mul, ← Matrix.exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have : ((m + 1 : ℕ) : ℂ) * (1 / ((m + 1 : ℕ) : ℂ)) = 1 := by
    rw [mul_one_div, div_self]; exact_mod_cast Nat.succ_ne_zero m
  rw [this, one_smul]

lemma C_formula {n m : ℕ} (η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i) (P : Fin n → Pauli) :
    Matrix.trace (xSubset (flipSet P) * matrixExp (hx η)) =
      ((∏ i, kap m (η i) (hasFlip (P i)) * ∑ σ, wgt m 0 η P i σ : ℝ) : ℂ) := by
  rw [matrixExp_hx_eq η m, D_formula 0 η hη P]


def Dsc {n : ℕ} (M : ℕ) (σ : Fin n → PathData) : Fin n → Spins M := fun i => discretize M (σ i)

lemma meshPot_eq {n m : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (σ : Fin n → PathData) :
    meshPotential J h (m+1) σ = cycleInteraction J (Dsc (m+1) σ) +
      ∑ i, ∑ k, (h i / (m+1 : ℕ)) * spin (Dsc (m+1) σ i k) := by
  rw [← energy_sum (Nat.succ_pos m)]
  unfold meshPotential Dsc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _
  simp only [pathValue_spin, discretize]
  ring

lemma pathSign_eq {n m : ℕ} (P : Fin n → Pauli) (σ : Fin n → PathData) :
    pathSign P σ = meshSign P (Dsc (m+1) σ) := by
  unfold pathSign meshSign Dsc
  apply Finset.prod_congr rfl; intro i _
  split_ifs
  · rw [Finset.sum_eq_single 0]
    · simp [discretize, pathValue_spin]
    · intro k _ hk; rw [if_neg]; intro h; apply hk; ext; exact h
    · simp
  · rfl

theorem identity2 {n m : ℕ} (hm : 2 ≤ m) (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ)
    (hη : ∀ i, 0 ≤ η i) (P : Fin n → Pauli) :
    Matrix.trace (pauliString P * trotter J h η (m+1)) =
      Complex.I ^ yCount P * Matrix.trace (xSubset (flipSet P) * matrixExp (hx η)) *
        (∫ σ, Real.exp (meshPotential J h (m+1) σ) * pathSign P σ ∂nu η P : ℝ) := by
  set G : (Fin n → Spins (m+1)) → ℝ := fun s => Real.exp (cycleInteraction J s +
      ∑ i, ∑ k, (h i / (m+1 : ℕ)) * spin (s i k)) * meshSign P s
  have hfun : (fun σ => Real.exp (meshPotential J h (m+1) σ) * pathSign P σ) = G ∘ Dsc (m+1) := by
    funext σ; simp only [Function.comp, G, meshPot_eq, pathSign_eq (m := m)]
  have hp7 : ∀ i, (pathLaw (η i) (hasFlip (P i))).map (discretize (m+1)) =
      pathCycleLaw (M := m+1) (η i) (hasFlip (P i)) (fun _ => .finite 0) :=
    fun i => TFIMPhaseDiagram.Classical.prop_7 (m+1) (by omega) (η i) (hη i) (hasFlip (P i))
  haveI : ∀ i, SigmaFinite ((pathLaw (η i) (hasFlip (P i))).map (discretize (m+1))) := by
    intro i; rw [hp7 i]; unfold pathCycleLaw; infer_instance
  have hmap : (nu η P).map (Dsc (m+1)) =
      Measure.pi (fun i => pathCycleLaw (M := m+1) (η i) (hasFlip (P i)) (fun _ => .finite 0)) := by
    unfold nu Dsc
    rw [Measure.pi_map_pi (fun i => (discretize_meas' (m+1)).aemeasurable)]
    congr 1; funext i; exact hp7 i
  have hint : ∫ σ, Real.exp (meshPotential J h (m+1) σ) * pathSign P σ ∂nu η P =
      ∑ s, (∏ i, pathCycleProb (M := m+1) (η i) (hasFlip (P i)) (fun _ => .finite 0) (s i)) * G s := by
    have hD : Measurable (Dsc (n := n) (m+1)) :=
      measurable_pi_lambda _ (fun i => (discretize_meas' (m+1)).comp (measurable_pi_apply i))
    rw [hfun]
    show ∫ σ, G (Dsc (m+1) σ) ∂(nu η P) = _
    rw [← integral_map hD.aemeasurable (Measurable.of_discrete).aestronglyMeasurable, hmap]
    unfold pathCycleLaw
    exact integral_pi_finite _ (fun i σ => by
      unfold pathCycleProb normalize
      exact div_nonneg (pcw_nonneg _ (hη i) _ _ σ) (Finset.sum_nonneg (fun τ _ => pcw_nonneg _ (hη i) _ _ τ))) G
  rw [hint, C_formula η hη P, trotter_trace]
  rw [mul_assoc]
  congr 1
  rw [← Complex.ofReal_sum, ← Complex.ofReal_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  have hZ : ∀ i, (∑ σ, wgt m 0 η P i σ) ≠ 0 := fun i => (pcw_sum_pos (η i) (hη i) _ _).ne'
  have hzero : ∀ i, (0 : Fin n → ℝ) i / ((m+1 : ℕ) : ℝ) = 0 := fun i => by simp
  have hA : ∀ i, cycR (η i / (m+1 : ℕ)) (hasFlip (P i)) (s i) =
      kap m (η i) (hasFlip (P i)) * pathCycleWeight (η i) (hasFlip (P i)) (fun _ => Field.finite 0) (s i) := by
    intro i
    have := Aw_eq (η i) (hη i) (hasFlip (P i)) 0 (s i)
    unfold Aw at this; simpa using this
  have hprod : (∏ i, kap m (η i) (hasFlip (P i)) * ∑ σ, wgt m 0 η P i σ) *
      (∏ i, pathCycleProb (M := m+1) (η i) (hasFlip (P i)) (fun _ => .finite 0) (s i)) =
      ∏ i, cycR (η i / (m+1 : ℕ)) (hasFlip (P i)) (s i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro i _
    rw [hA i]
    have hZi := hZ i
    simp only [wgt, hzero] at hZi ⊢
    unfold pathCycleProb normalize
    field_simp [hZi]
  simp only [G]
  rw [← mul_assoc, hprod, Real.exp_add, Real.exp_sum, Finset.prod_mul_distrib]
  ring

end TFIMPhaseDiagram.Classical.P8Aux

open MeasureTheory

namespace TFIMPhaseDiagram.Classical.LTAux

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

lemma norm_term_le (x : 𝔸) (n : ℕ) : ‖((n ! : ℂ)⁻¹) • x ^ n‖ ≤ ‖x‖ ^ n / n ! := by
  rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)

lemma real_exp_hasSum (r : ℝ) : HasSum (fun n : ℕ => r ^ n / n !) (Real.exp r) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp r

lemma norm_exp_le (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  refine (norm_tsum_le_tsum_norm (NormedSpace.norm_expSeries_summable' x)).trans ?_
  exact ((NormedSpace.norm_expSeries_summable' x).tsum_le_tsum (norm_term_le x)
    (real_exp_hasSum _).summable).trans (real_exp_hasSum _).tsum_eq.le

lemma norm_exp_sub_le (x : 𝔸) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℂ) x
  have hrep : NormedSpace.exp x - 1 - x = ∑' n : ℕ, (((n + 2) ! : ℂ)⁻¹) • x ^ (n + 2) := by
    rw [NormedSpace.exp_eq_tsum ℂ]
    simp only
    rw [← hs.sum_add_tsum_nat_add 2]
    simp [Finset.sum_range_succ]
    abel
  rw [hrep]
  have hsn : Summable (fun n : ℕ => ‖(((n + 2) ! : ℂ)⁻¹) • x ^ (n + 2)‖) :=
    (summable_nat_add_iff 2).2 (NormedSpace.norm_expSeries_summable' x)
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  have hb : ∀ n : ℕ, ‖(((n + 2) ! : ℂ)⁻¹) • x ^ (n + 2)‖ ≤ ‖x‖ ^ 2 * (‖x‖ ^ n / n !) := by
    intro n
    refine (norm_term_le x (n+2)).trans ?_
    rw [pow_add, mul_comm (‖x‖ ^ n), mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast Nat.factorial_le (by omega)
  calc ∑' n, ‖(((n + 2) ! : ℂ)⁻¹) • x ^ (n + 2)‖ ≤ ∑' n : ℕ, ‖x‖ ^ 2 * (‖x‖ ^ n / n !) :=
        hsn.tsum_le_tsum hb ((real_exp_hasSum _).summable.mul_left _)
    _ = ‖x‖ ^ 2 * Real.exp ‖x‖ := by rw [tsum_mul_left, (real_exp_hasSum _).tsum_eq]

lemma pow_sub_pow_le (S T : 𝔸) (q : ℝ) (hS : ‖S‖ ≤ q) (hT : ‖T‖ ≤ q) (M : ℕ) :
    ‖S ^ M - T ^ M‖ ≤ M * ‖S - T‖ * q ^ (M - 1) := by
  have hq : 0 ≤ q := (norm_nonneg _).trans hS
  induction M with
  | zero => simp
  | succ M ih =>
    have e : S ^ (M+1) - T ^ (M+1) = S * (S ^ M - T ^ M) + (S - T) * T ^ M := by
      rw [pow_succ', pow_succ']; noncomm_ring
    rw [e]
    calc ‖S * (S ^ M - T ^ M) + (S - T) * T ^ M‖
        ≤ ‖S‖ * ‖S ^ M - T ^ M‖ + ‖S - T‖ * ‖T‖ ^ M :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _)
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_pow_le _ _) (norm_nonneg _))))
      _ ≤ q * (M * ‖S - T‖ * q ^ (M - 1)) + ‖S - T‖ * q ^ M := by
          gcongr
      _ = (M + 1 : ℕ) * ‖S - T‖ * q ^ (M + 1 - 1) := by
          rcases M with _ | M
          · simp
          · simp only [Nat.add_sub_cancel]; push_cast; ring


lemma bch_bound (x y : 𝔸) (E : ℝ) (hx : Real.exp ‖x‖ ≤ E) (hy : Real.exp ‖y‖ ≤ E)
    (hxy : Real.exp (‖x‖ + ‖y‖) ≤ E) :
    ‖NormedSpace.exp x * NormedSpace.exp y - NormedSpace.exp (x + y)‖ ≤
      (‖y‖ ^ 2 * E + ‖x‖ * ‖y‖ + ‖x‖ * (‖y‖ ^ 2 * E) + ‖x‖ ^ 2 * E * E + (‖x‖ + ‖y‖) ^ 2 * E) := by
  set rx := NormedSpace.exp x - 1 - x
  set ry := NormedSpace.exp y - 1 - y
  set rxy := NormedSpace.exp (x + y) - 1 - (x + y)
  have e : NormedSpace.exp x * NormedSpace.exp y - NormedSpace.exp (x + y) =
      ry + x * y + x * ry + rx * NormedSpace.exp y - rxy := by
    simp only [rx, ry, rxy]; noncomm_ring
  have hrx : ‖rx‖ ≤ ‖x‖ ^ 2 * E := (norm_exp_sub_le x).trans (mul_le_mul_of_nonneg_left hx (by positivity))
  have hry : ‖ry‖ ≤ ‖y‖ ^ 2 * E := (norm_exp_sub_le y).trans (mul_le_mul_of_nonneg_left hy (by positivity))
  have hrxy : ‖rxy‖ ≤ (‖x‖ + ‖y‖) ^ 2 * E := by
    refine (norm_exp_sub_le (x + y)).trans ?_
    have h1 := norm_add_le x y
    have h2 : Real.exp ‖x + y‖ ≤ E := (Real.exp_le_exp.2 h1).trans hxy
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2 (by positivity) (by positivity)
  have hey : ‖NormedSpace.exp y‖ ≤ E := (norm_exp_le y).trans hy
  rw [e]
  calc ‖ry + x * y + x * ry + rx * NormedSpace.exp y - rxy‖
      ≤ ‖ry‖ + ‖x * y‖ + ‖x * ry‖ + ‖rx * NormedSpace.exp y‖ + ‖rxy‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _ ≤ ‖y‖ ^ 2 * E + ‖x‖ * ‖y‖ + ‖x‖ * (‖y‖ ^ 2 * E) + ‖x‖ ^ 2 * E * E + (‖x‖ + ‖y‖) ^ 2 * E := by
        gcongr
        · exact norm_mul_le _ _
        · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hry (norm_nonneg _))
        · exact (norm_mul_le _ _).trans (mul_le_mul hrx hey (norm_nonneg _)
            (mul_nonneg (sq_nonneg _) ((Real.exp_pos _).le.trans hx)))

theorem lie_trotter [NormedAlgebra ℚ 𝔸] (A B : 𝔸) :
    Filter.Tendsto (fun M : ℕ => (NormedSpace.exp ((1 / (M : ℂ)) • A) *
      NormedSpace.exp ((1 / (M : ℂ)) • B)) ^ M) Filter.atTop (nhds (NormedSpace.exp (A + B))) := by
  set a := ‖A‖; set b := ‖B‖
  set E := Real.exp (a + b)
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  set K := (b ^ 2 * E + a * b + a * (b ^ 2 * E) + a ^ 2 * E * E + (a + b) ^ 2 * E) * E
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat K)
  filter_upwards [Filter.eventually_ge_atTop 1] with M hM
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0:ℝ) < M := by linarith
  set u : ℝ := 1 / M
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 := by rw [div_le_one hM0]; exact hMr
  set x := (1 / (M : ℂ)) • A; set y := (1 / (M : ℂ)) • B
  have hnx : ‖x‖ = u * a := by
    simp only [x, norm_smul, u, a]; rw [norm_div, norm_one, Complex.norm_natCast]
  have hny : ‖y‖ = u * b := by
    simp only [y, norm_smul, u, b]; rw [norm_div, norm_one, Complex.norm_natCast]
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hxE : Real.exp ‖x‖ ≤ E := Real.exp_le_exp.2 (by rw [hnx]; nlinarith)
  have hyE : Real.exp ‖y‖ ≤ E := Real.exp_le_exp.2 (by rw [hny]; nlinarith)
  have hxyE : Real.exp (‖x‖ + ‖y‖) ≤ E := Real.exp_le_exp.2 (by rw [hnx, hny]; nlinarith)
  have hT : NormedSpace.exp (x + y) ^ M = NormedSpace.exp (A + B) := by
    rw [← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_add, smul_smul, smul_smul]
    have : (M : ℂ) * (1 / (M : ℂ)) = 1 := by
      rw [mul_one_div, div_self]; exact_mod_cast (Nat.one_le_iff_ne_zero.1 hM)
    rw [this, one_smul, one_smul]
  rw [← hT]
  set q := Real.exp (u * (a + b))
  have hS : ‖NormedSpace.exp x * NormedSpace.exp y‖ ≤ q := by
    refine (norm_mul_le _ _).trans ?_
    refine (mul_le_mul (norm_exp_le x) (norm_exp_le y) (norm_nonneg _) (by positivity)).trans ?_
    rw [← Real.exp_add, hnx, hny]; apply le_of_eq; congr 1; ring
  have hTq : ‖NormedSpace.exp (x + y)‖ ≤ q :=
    (norm_exp_le _).trans (Real.exp_le_exp.2 ((norm_add_le x y).trans (by rw [hnx, hny]; nlinarith)))
  have hpow := pow_sub_pow_le _ _ q hS hTq M
  have hqM : q ^ (M - 1) ≤ E := by
    rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.2
    have : ((M - 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.sub_le M 1
    calc ((M - 1 : ℕ) : ℝ) * (u * (a + b)) ≤ M * (u * (a + b)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = a + b := by simp only [u]; field_simp
  have hdiff := bch_bound x y E hxE hyE hxyE
  rw [hnx, hny] at hdiff
  have hdiff2 : ‖NormedSpace.exp x * NormedSpace.exp y - NormedSpace.exp (x + y)‖ ≤
      u ^ 2 * (b ^ 2 * E + a * b + a * (b ^ 2 * E) + a ^ 2 * E * E + (a + b) ^ 2 * E) := by
    refine hdiff.trans ?_
    have hE0 : 0 ≤ E := by linarith
    have hu3 : u ^ 3 ≤ u ^ 2 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg ha (mul_nonneg hb hb)) hE0, sq_nonneg u,
      mul_le_mul_of_nonneg_left hu3 (mul_nonneg (mul_nonneg ha (mul_nonneg hb hb)) hE0)]
  calc ‖(NormedSpace.exp x * NormedSpace.exp y) ^ M - NormedSpace.exp (x + y) ^ M‖
      ≤ M * ‖NormedSpace.exp x * NormedSpace.exp y - NormedSpace.exp (x + y)‖ * q ^ (M - 1) := hpow
    _ ≤ M * (u ^ 2 * (b ^ 2 * E + a * b + a * (b ^ 2 * E) + a ^ 2 * E * E + (a + b) ^ 2 * E)) * E := by
        gcongr
    _ = K / M := by simp only [K, u]; field_simp


open TFIMPhaseDiagram.Classical in
theorem trotter_tendsto {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) :
    Filter.Tendsto (fun M : ℕ => trotter J h η M) Filter.atTop
      (nhds (matrixExp (hamiltonian J h η))) := by
  unfold trotter matrixExp hamiltonian
  open scoped Matrix.Norms.Operator in
  exact lie_trotter (hz J h) (hx η)

open TFIMPhaseDiagram.Classical in
theorem trace_trotter_tendsto {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ)
    (P : Fin n → Pauli) :
    Filter.Tendsto (fun M : ℕ => Matrix.trace (pauliString P * trotter J h η M)) Filter.atTop
      (nhds (Matrix.trace (pauliString P * matrixExp (hamiltonian J h η)))) := by
  have hc : Continuous (fun X : QMat n => Matrix.trace (pauliString P * X)) :=
    (continuous_const.matrix_mul continuous_id).matrix_trace
  exact (hc.tendsto _).comp (trotter_tendsto J h η)

end TFIMPhaseDiagram.Classical.LTAux


open Filter Topology

namespace TFIMPhaseDiagram.Classical.RSAux

def stepf (f : ℝ → ℝ) (M : ℕ) (t : ℝ) : ℝ := f ((⌊t * M⌋ : ℝ) / M)

lemma floor_eq_on (M : ℕ) (hM : 0 < M) (k : ℕ) (t : ℝ)
    (ht : t ∈ Set.Ico ((k : ℝ) / M) (((k : ℝ) + 1) / M)) : ⌊t * M⌋ = (k : ℤ) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Int.floor_eq_iff]
  obtain ⟨h1, h2⟩ := ht
  rw [div_le_iff₀ hMr] at h1
  rw [lt_div_iff₀ hMr] at h2
  push_cast; constructor <;> linarith

lemma Ico_union (M : ℕ) (hM : 0 < M) :
    Set.Ico (0 : ℝ) 1 = ⋃ k ∈ (Finset.range M), Set.Ico ((k : ℝ) / M) (((k : ℝ) + 1) / M) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  ext t
  simp only [Set.mem_Ico, Set.mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨⌊t * M⌋₊, ?_, ?_, ?_⟩
    · have : t * M < M := by nlinarith
      exact_mod_cast (Nat.floor_lt (by positivity)).2 (by exact_mod_cast this)
    · rw [div_le_iff₀ hMr]; exact Nat.floor_le (by positivity)
    · rw [lt_div_iff₀ hMr]; exact Nat.lt_floor_add_one _
  · rintro ⟨k, hk, h1, h2⟩
    have hk' : (k : ℝ) + 1 ≤ M := by exact_mod_cast hk
    constructor
    · exact le_trans (by positivity) h1
    · calc t < ((k : ℝ) + 1) / M := h2
        _ ≤ 1 := by rw [div_le_one hMr]; exact hk'

lemma riemann_eq (f : ℝ → ℝ) (B : ℝ) (hB : ∀ t, |f t| ≤ B) (hf : Measurable f) (M : ℕ) (hM : 0 < M) :
    (1 / (M : ℝ)) * ∑ k : Fin M, f (k.val / M) = ∫ t in Set.Icc (0 : ℝ) 1, stepf f M t := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hmeas : Measurable (stepf f M) := by
    unfold stepf
    exact hf.comp (((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.mul_const _))).div_const _)
  rw [integral_Icc_eq_integral_Ico, Ico_union M hM]
  rw [integral_biUnion_finset]
  · rw [Fin.sum_univ_eq_sum_range (fun k => f (k / M)), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [setIntegral_congr_fun measurableSet_Ico (g := fun _ => f (k / M)) (fun t ht => by
      simp only [stepf]; rw [floor_eq_on M hM k t ht]; simp)]
    rw [setIntegral_const, Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (by
      rw [sub_nonneg]; gcongr; linarith), smul_eq_mul]
    congr 1; field_simp; ring
  · intro k _; exact measurableSet_Ico
  · intro k _ j _ hkj
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro t h1 h2
    have := floor_eq_on M hM k t h1
    rw [floor_eq_on M hM j t h2] at this
    exact hkj (by exact_mod_cast this.symm)
  · intro k _
    refine Measure.integrableOn_of_bounded (M := B) ?_ hmeas.aestronglyMeasurable ?_
    · simp
    · exact Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact hB _)


theorem riemann_tendsto (f : ℝ → ℝ) (B : ℝ) (hB : ∀ t, |f t| ≤ B) (hf : Measurable f) (S : Finset ℝ)
    (hloc : ∀ t, 0 ≤ t → t < 1 → t ∉ S → ∃ δ > 0, ∀ s, t - δ < s → s ≤ t → f s = f t) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * ∑ k : Fin M, f (k.val / M)) atTop
      (𝓝 (∫ t in Set.Icc (0 : ℝ) 1, f t)) := by
  have hmeas : ∀ M : ℕ, Measurable (stepf f M) := fun M => by
    unfold stepf
    exact hf.comp (((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.mul_const _))).div_const _)
  have heq : (fun M : ℕ => ∫ t in Set.Icc (0 : ℝ) 1, stepf f M t) =ᶠ[atTop]
      (fun M : ℕ => (1 / (M : ℝ)) * ∑ k : Fin M, f (k.val / M)) := by
    filter_upwards [eventually_ge_atTop 1] with M hM
    exact (riemann_eq f B hB hf M hM).symm
  refine Tendsto.congr' heq ?_
  apply tendsto_integral_of_dominated_convergence (fun _ => B)
  · intro M; exact (hmeas M).aestronglyMeasurable
  · exact integrable_const B
  · intro M; exact Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact hB _)
  · have hnull : volume ((S : Set ℝ) ∪ {1}) = 0 :=
      ((S.finite_toSet).union (Set.finite_singleton 1)).measure_zero volume
    have hae : ∀ᵐ t ∂volume, t ∉ (S : Set ℝ) ∪ {1} := measure_eq_zero_iff_ae_notMem.1 hnull
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hae] with t ht hIcc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_singleton_iff, not_or] at ht
    have ht1 : t < 1 := lt_of_le_of_ne hIcc.2 ht.2
    obtain ⟨δ, hδ, hδf⟩ := hloc t hIcc.1 ht1 ht.1
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop ⌈1 / δ⌉₊, eventually_ge_atTop 1] with M hM hM1
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM1
    have hMδ : 1 / δ < M := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hM)
    have hinv : 1 / (M : ℝ) < δ := by
      rw [div_lt_iff₀ hMr]; rw [div_lt_iff₀ hδ] at hMδ; linarith
    symm
    apply hδf
    · have h1 : t * M - 1 < (⌊t * M⌋ : ℝ) := Int.sub_one_lt_floor _
      rw [lt_div_iff₀ hMr]
      have : (t - δ) * M < t * M - 1 := by
        have : 1 < δ * M := by rw [div_lt_iff₀ hMr] at hinv; linarith
        nlinarith
      linarith
    · rw [div_le_iff₀ hMr]; exact Int.floor_le _

end TFIMPhaseDiagram.Classical.RSAux

namespace TFIMPhaseDiagram.Classical.P8Prob
open TFIMPhaseDiagram.Classical MeasureTheory
open scoped Nat

instance u01_prob' : IsProbabilityMeasure TFIMPhaseDiagram.Classical.uniform01 :=
  ⟨by simp [TFIMPhaseDiagram.Classical.uniform01]⟩

lemma mass_nonneg (η : ℝ) (hη : 0 ≤ η) (p : Bool) (d : ℕ) : 0 ≤ parityMass η p d := by
  unfold parityMass
  split_ifs <;> try positivity

lemma mass_hasSum (η : ℝ) (hη : 0 ≤ η) (p : Bool) : HasSum (fun d => parityMass η p d) 1 := by
  by_cases h0 : η = 0
  · subst h0
    have : (fun d => parityMass 0 p d) = fun d => if d = (if p then 1 else 0) then 1 else 0 := by
      funext d; simp [parityMass]
    rw [this]
    convert hasSum_ite_eq (if p then 1 else 0) (1:ℝ)
  have hpos : 0 < η := lt_of_le_of_ne hη (Ne.symm h0)
  cases p
  · have hc := (Real.hasSum_cosh η).div_const (Real.cosh η)
    rw [div_self (Real.cosh_pos η).ne'] at hc
    rw [← (Function.Injective.hasSum_iff (g := fun n : ℕ => 2 * n) (fun a b h => by simpa using h) _)]
    · have e : (fun d => parityMass η false d) ∘ (fun n : ℕ => 2 * n) =
          fun i => η ^ (2 * i) / ↑(2 * i)! / Real.cosh η := by
        funext n; simp only [Function.comp, parityMass, h0, if_false, Bool.false_eq_true]
        rw [if_pos (by omega)]; field_simp
      rw [e]; exact hc
    · intro x hx
      simp only [parityMass, h0, if_false, Bool.false_eq_true]
      rw [if_neg]; intro h; exact hx ⟨x / 2, by show 2 * (x / 2) = x; omega⟩
  · have hs : 0 < Real.sinh η := Real.sinh_pos_iff.2 hpos
    have hc := (Real.hasSum_sinh η).div_const (Real.sinh η)
    rw [div_self hs.ne'] at hc
    rw [← (Function.Injective.hasSum_iff (g := fun n : ℕ => 2 * n + 1) (fun a b h => by simpa using h) _)]
    · have e : (fun d => parityMass η true d) ∘ (fun n : ℕ => 2 * n + 1) =
          fun i => η ^ (2 * i + 1) / ↑(2 * i + 1)! / Real.sinh η := by
        funext n; simp only [Function.comp, parityMass, h0, if_false, if_true]
        rw [if_pos (by omega)]; field_simp
      rw [e]; exact hc
    · intro x hx
      simp only [parityMass, h0, if_false, if_true]
      rw [if_neg]; intro h; exact hx ⟨x / 2, by show 2 * (x / 2) + 1 = x; omega⟩

lemma parityLaw_prob (η : ℝ) (hη : 0 ≤ η) (p : Bool) : IsProbabilityMeasure (parityLaw η p) := by
  constructor
  unfold parityLaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (mass_nonneg η hη p) (mass_hasSum η hη p).summable,
    (mass_hasSum η hη p).tsum_eq, ENNReal.ofReal_one]

instance bern_prob : IsProbabilityMeasure (finiteLaw (fun _ : Bool => (1/2 : ℝ))) := by
  constructor
  unfold finiteLaw
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]; norm_num

lemma pathLaw_prob (η : ℝ) (hη : 0 ≤ η) (p : Bool) : IsProbabilityMeasure (pathLaw η p) := by
  haveI := parityLaw_prob η hη p
  unfold pathLaw; infer_instance

end TFIMPhaseDiagram.Classical.P8Prob

namespace TFIMPhaseDiagram.Classical.P8Fin
open TFIMPhaseDiagram.Classical TFIMPhaseDiagram.Classical.P8Aux TFIMPhaseDiagram.Classical.RSAux
  TFIMPhaseDiagram.Classical.LTAux MeasureTheory Filter Topology

def Bp {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : ℝ :=
  (1/2) * ∑ i, ∑ j, |J i j| + ∑ i, |h i|

lemma pot_bound {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (s : Fin n → ℝ)
    (hs : ∀ i, |s i| ≤ 1) : |potential J h s| ≤ Bp J h := by
  unfold potential Bp
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul, abs_mul]
    calc |J i j| * |s i| * |s j| ≤ |J i j| * 1 * 1 := by
          gcongr
          · exact hs i
          · exact hs j
      _ = |J i j| := by ring
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [abs_mul]
    calc |h i| * |s i| ≤ |h i| * 1 := by gcongr; exact hs i
      _ = |h i| := by ring

lemma pathValue_abs (σ : PathData) (t : ℝ) : |pathValue σ t| = 1 := by
  rw [pathValue_spin]; cases pathBits σ t <;> simp [spin]

lemma pot_cont {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : Continuous (potential J h) := by
  unfold potential; fun_prop

lemma pathValue_meas_t (σ : PathData) : Measurable (fun t : ℝ => pathValue σ t) := by
  unfold pathValue
  apply Measurable.const_mul
  apply (measurable_of_countable (fun n : ℕ => (-1 : ℝ) ^ n)).comp
  have : (fun t : ℝ => ((Finset.range σ.1).filter (fun k => σ.2.2 k ≤ t)).card) =
      fun t => ∑ k ∈ Finset.range σ.1, (if σ.2.2 k ≤ t then 1 else 0) := by
    funext t; rw [Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ (fun k _ => Measurable.ite (measurableSet_le measurable_const measurable_id)
    measurable_const measurable_const)

theorem meshPot_tendsto {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (σ : Fin n → PathData) :
    Tendsto (fun M : ℕ => meshPotential J h M σ) atTop (𝓝 (pathPotential J h σ)) := by
  set f : ℝ → ℝ := fun t => potential J h (fun i => pathValue (σ i) t)
  have hfm : Measurable f := (pot_cont J h).measurable.comp
    (measurable_pi_lambda _ (fun i => pathValue_meas_t (σ i)))
  have hB : ∀ t, |f t| ≤ Bp J h := fun t =>
    pot_bound J h _ (fun i => (pathValue_abs (σ i) t).le)
  set S : Finset ℝ := Finset.univ.biUnion (fun i => (Finset.range (σ i).1).image (fun j => (σ i).2.2 j))
  have hloc : ∀ t, 0 ≤ t → t < 1 → t ∉ S → ∃ δ > 0, ∀ s, t - δ < s → s ≤ t → f s = f t := by
    intro t _ _ htS
    set L := S.filter (· < t)
    have key : ∃ δ > 0, ∀ u ∈ L, u ≤ t - δ := by
      by_cases hL : L.Nonempty
      · refine ⟨t - L.max' hL, ?_, fun u hu => ?_⟩
        · have := (Finset.mem_filter.1 (L.max'_mem hL)).2; linarith
        · have := L.le_max' u hu; linarith
      · refine ⟨1, one_pos, fun u hu => absurd ⟨u, hu⟩ hL⟩
    obtain ⟨δ, hδ, hδL⟩ := key
    refine ⟨δ, hδ, fun s hs1 hs2 => ?_⟩
    simp only [f]
    congr 1; funext i
    unfold pathValue
    congr 2
    congr 1
    apply Finset.filter_congr; intro j hj
    constructor
    · intro hu; exact le_trans hu hs2
    · intro hu
      have hmem : (σ i).2.2 j ∈ S := Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
        Finset.mem_image.2 ⟨j, hj, rfl⟩⟩
      have hne : (σ i).2.2 j ≠ t := fun e => htS (e ▸ hmem)
      have hlt : (σ i).2.2 j < t := lt_of_le_of_ne hu hne
      have := hδL _ (Finset.mem_filter.2 ⟨hmem, hlt⟩)
      linarith
  exact riemann_tendsto f (Bp J h) hB hfm S hloc


lemma meshPot_meas {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (M : ℕ) :
    Measurable (fun σ : Fin n → PathData => meshPotential J h M σ) := by
  unfold meshPotential
  apply Measurable.const_mul
  apply Finset.measurable_sum; intro k _
  exact (pot_cont J h).measurable.comp
    (measurable_pi_lambda _ (fun i => (pathValue_meas' _).comp (measurable_pi_apply i)))

lemma pathSign_meas {n : ℕ} (P : Fin n → Pauli) : Measurable (fun σ : Fin n → PathData => pathSign P σ) := by
  unfold pathSign
  apply Finset.measurable_prod; intro i _
  by_cases hc : P i = .Y ∨ P i = .Z
  · simp only [hc, if_true]; exact (pathValue_meas' 0).comp (measurable_pi_apply i)
  · simp only [hc, if_false]; exact measurable_const

lemma pathSign_abs {n : ℕ} (P : Fin n → Pauli) (σ : Fin n → PathData) : |pathSign P σ| ≤ 1 := by
  unfold pathSign
  rw [Finset.abs_prod]
  apply Finset.prod_le_one (fun i _ => abs_nonneg _)
  intro i _
  split_ifs
  · rw [pathValue_abs]
  · simp

lemma meshPot_abs {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (M : ℕ) (σ : Fin n → PathData) :
    |meshPotential J h M σ| ≤ Bp J h := by
  have hB0 : 0 ≤ Bp J h := le_trans (abs_nonneg _) (pot_bound J h (fun _ => 0) (fun _ => by simp))
  unfold meshPotential
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp [hB0]
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  rw [abs_mul, abs_of_pos (by positivity)]
  calc 1 / (M:ℝ) * |∑ k : Fin M, potential J h (fun i => pathValue (σ i) (k.val / M))|
      ≤ 1 / (M:ℝ) * ∑ k : Fin M, Bp J h := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
        exact pot_bound J h _ (fun i => (pathValue_abs _ _).le)
    _ = Bp J h := by simp; field_simp

theorem int_tendsto {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i)
    (P : Fin n → Pauli) :
    Tendsto (fun M : ℕ => ∫ σ, Real.exp (meshPotential J h M σ) * pathSign P σ ∂nu η P) atTop
      (𝓝 (∫ σ, Real.exp (pathPotential J h σ) * pathSign P σ ∂nu η P)) := by
  haveI : ∀ i, IsProbabilityMeasure (pathLaw (η i) (hasFlip (P i))) :=
    fun i => TFIMPhaseDiagram.Classical.P8Prob.pathLaw_prob (η i) (hη i) _
  haveI : IsProbabilityMeasure (nu η P) := by unfold nu; infer_instance
  apply tendsto_integral_of_dominated_convergence (fun _ => Real.exp (Bp J h))
  · intro M
    exact ((Real.measurable_exp.comp (meshPot_meas J h M)).mul (pathSign_meas P)).aestronglyMeasurable
  · exact integrable_const _
  · intro M
    refine Eventually.of_forall (fun σ => ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    calc Real.exp (meshPotential J h M σ) * |pathSign P σ| ≤ Real.exp (Bp J h) * 1 :=
          mul_le_mul (Real.exp_le_exp.2 (le_of_abs_le (meshPot_abs J h M σ))) (pathSign_abs P σ)
            (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (Bp J h) := mul_one _
  · exact Eventually.of_forall (fun σ =>
      ((Real.continuous_exp.tendsto _).comp (meshPot_tendsto J h σ)).mul_const _)

theorem prop8 {n : ℕ} (hn : 0 < n) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.IsSymm) (h η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i)
    (P : Fin n → Pauli) (M : ℕ) (hM : 3 ≤ M) :
  let C := Matrix.trace (xSubset (flipSet P) * matrixExp (hx η))
  let D := Matrix.trace (xSubset (flipSet P) * trotter 0 h η M)
  C.im = 0 ∧ 0 ≤ C.re ∧ D.im = 0 ∧ 0 ≤ D.re ∧
  Matrix.trace (pauliString P * matrixExp (hamiltonian J h η)) =
    Complex.I ^ yCount P * C * (∫ σ, Real.exp (pathPotential J h σ) * pathSign P σ ∂nu η P : ℝ) ∧
  Matrix.trace (pauliString P * trotter J h η M) =
    Complex.I ^ yCount P * C * (∫ σ, Real.exp (meshPotential J h M σ) * pathSign P σ ∂nu η P : ℝ) ∧
  Matrix.trace (pauliString P * trotter J h η M) =
    Complex.I ^ yCount P * D * (∫ s, Real.exp (cycleInteraction J s) * meshSign P s ∂nuTilde (M := M) h η P : ℝ) := by
  intro C D
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  have hCf : C = ((∏ i, kap m (η i) (hasFlip (P i)) * ∑ σ, wgt m 0 η P i σ : ℝ) : ℂ) := C_formula η hη P
  have hDf : D = ((∏ i, kap m (η i) (hasFlip (P i)) * ∑ σ, wgt m h η P i σ : ℝ) : ℂ) := D_formula h η hη P
  have hnn : ∀ (c : Fin n → ℝ), 0 ≤ ∏ i, kap m (η i) (hasFlip (P i)) * ∑ σ, wgt m c η P i σ := by
    intro c
    apply Finset.prod_nonneg; intro i _
    exact mul_nonneg (kap_nonneg _ _ _) (Finset.sum_nonneg (fun σ _ => pcw_nonneg _ (hη i) _ _ σ))
  refine ⟨by rw [hCf, Complex.ofReal_im], by rw [hCf, Complex.ofReal_re]; exact hnn 0,
    by rw [hDf, Complex.ofReal_im], by rw [hDf, Complex.ofReal_re]; exact hnn h, ?_,
    identity2 hm J h η hη P, identity3 J h η hη P⟩
  -- the continuum identity by uniqueness of limits
  have h1 := trace_trotter_tendsto J h η P
  have h2 : Tendsto (fun M : ℕ => Complex.I ^ yCount P * C *
      ((∫ σ, Real.exp (meshPotential J h M σ) * pathSign P σ ∂nu η P : ℝ) : ℂ)) atTop
      (𝓝 (Complex.I ^ yCount P * C * ((∫ σ, Real.exp (pathPotential J h σ) * pathSign P σ ∂nu η P : ℝ) : ℂ))) :=
    ((Complex.continuous_ofReal.tendsto _).comp (int_tendsto J h η hη P)).const_mul _
  have heq : (fun M : ℕ => Matrix.trace (pauliString P * trotter J h η M)) =ᶠ[atTop]
      (fun M : ℕ => Complex.I ^ yCount P * C *
        ((∫ σ, Real.exp (meshPotential J h M σ) * pathSign P σ ∂nu η P : ℝ) : ℂ)) := by
    filter_upwards [eventually_ge_atTop 3] with M hM3
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    exact identity2 (by omega) J h η hη P
  exact tendsto_nhds_unique h1 (h2.congr' heq.symm)

end TFIMPhaseDiagram.Classical.P8Fin

open TFIMPhaseDiagram.Classical MeasureTheory in
theorem solution {n : ℕ} (hn : 0 < n) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.IsSymm) (h η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i)
    (P : Fin n → Pauli) (M : ℕ) (hM : 3 ≤ M) :
  let C := Matrix.trace (xSubset (flipSet P) * matrixExp (hx η))
  let D := Matrix.trace (xSubset (flipSet P) * trotter 0 h η M)
  C.im = 0 ∧ 0 ≤ C.re ∧ D.im = 0 ∧ 0 ≤ D.re ∧
  Matrix.trace (pauliString P * matrixExp (hamiltonian J h η)) =
    Complex.I ^ yCount P * C * (∫ σ, Real.exp (pathPotential J h σ) * pathSign P σ ∂nu η P : ℝ) ∧
  Matrix.trace (pauliString P * trotter J h η M) =
    Complex.I ^ yCount P * C * (∫ σ, Real.exp (meshPotential J h M σ) * pathSign P σ ∂nu η P : ℝ) ∧
  Matrix.trace (pauliString P * trotter J h η M) =
    Complex.I ^ yCount P * D * (∫ s, Real.exp (cycleInteraction J s) * meshSign P s ∂nuTilde (M := M) h η P : ℝ) :=
  TFIMPhaseDiagram.Classical.P8Fin.prop8 hn J hJ h η hη P M hM
