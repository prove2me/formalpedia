-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:21:48.480837+00:00
-- url     : https://prove2.me/submissions/cccbcda5-ec49-486a-ab3a-2241a051ad15

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open scoped BigOperators

noncomputable section
namespace OTDB1
open OptimalTraceDistance.Estimation Polynomial

def hh (m : ℕ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ f ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) m, ∏ i, x i ^ f i

lemma inner_eq (a j : ℕ) (hj : a ≤ j) (x : Fin (a+1) → ℝ) :
    ∑ r ∈ (Finset.pi Finset.univ (fun _ : Fin (a+1) => Finset.range (j+1))).filter
      (fun r => (∑ i, r i (Finset.mem_univ i)) = j - a), ∏ i, x i ^ (r i (Finset.mem_univ i)) =
    hh (j - a) x := by
  unfold hh
  refine Finset.sum_nbij' (fun r i => r i (Finset.mem_univ i)) (fun f i _ => f i) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter] at hr
    rw [Finset.mem_piAntidiag]
    exact ⟨hr.2, fun i _ => Finset.mem_univ i⟩
  · intro f hf
    rw [Finset.mem_piAntidiag] at hf
    rw [Finset.mem_filter, Finset.mem_pi]
    refine ⟨fun i _ => ?_, hf.1⟩
    have h3 : f i ≤ j - a := by
      have := Finset.single_le_sum (fun k _ => Nat.zero_le (f k)) (Finset.mem_univ i)
      rw [hf.1] at this; exact this
    rw [Finset.mem_range]; show f i < j + 1; omega
  · intro r _; rfl
  · intro f _; rfl
  · intro r _; rfl

lemma DD_eq (p : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) :
    dividedDifference p a x = ∑ j ∈ p.support, if a ≤ j then p.coeff j * hh (j - a) x else 0 := by
  unfold dividedDifference
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs with h
  · rw [inner_eq a j h]
  · rfl

lemma DD_range (p : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) (N : ℕ) (hN : p.natDegree < N) :
    dividedDifference p a x = ∑ j ∈ Finset.range N, if a ≤ j then p.coeff j * hh (j - a) x else 0 := by
  rw [DD_eq]
  apply Finset.sum_subset
  · intro j hj; rw [Finset.mem_range]; exact lt_of_le_of_lt (le_natDegree_of_mem_supp j hj) hN
  · intro j _ hj
    rw [Polynomial.notMem_support_iff] at hj
    simp [hj]

lemma hh_zero {n : ℕ} (x : Fin n → ℝ) : hh 0 x = 1 := by
  simp [hh]

lemma hh_fin1 (m : ℕ) (x : Fin 1 → ℝ) : hh m x = x 0 ^ m := by
  unfold hh
  have : Finset.piAntidiag (Finset.univ : Finset (Fin 1)) m = {fun _ => m} := by
    ext f
    simp only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true,
      Finset.mem_singleton, Fin.sum_univ_one]
    constructor
    · intro h; funext i; fin_cases i; exact h
    · intro h; rw [h]
  rw [this, Finset.sum_singleton, Fin.prod_univ_one]

lemma hh_perm (m : ℕ) {n : ℕ} (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : hh m (x ∘ σ) = hh m x := by
  unfold hh
  refine Finset.sum_nbij' (fun f => f ∘ σ.symm) (fun f => f ∘ σ) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_piAntidiag] at hf ⊢
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    rw [← hf.1]; exact Equiv.sum_comp σ.symm f
  · intro f hf
    rw [Finset.mem_piAntidiag] at hf ⊢
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    rw [← hf.1]; exact Equiv.sum_comp σ f
  · intro f _; funext i; simp
  · intro f _; funext i; simp
  · intro f _
    rw [← Equiv.prod_comp σ (fun i => x i ^ (f ∘ σ.symm) i)]
    simp

lemma hh_succ (m : ℕ) {n : ℕ} (x : Fin (n+1) → ℝ) :
    hh (m+1) x = x 0 * hh m x + hh (m+1) (Fin.tail x) := by
  unfold hh
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun f : Fin (n+1) → ℕ => f 0 = 0), add_comm]
  congr 1
  · -- f 0 ≠ 0
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_nbij' (fun g => Fin.cons (g 0 + 1) (Fin.tail g))
      (fun f => Fin.cons (f 0 - 1) (Fin.tail f)) ?_ ?_ ?_ ?_ ?_
    · intro g hg
      rw [Finset.mem_piAntidiag] at hg
      rw [Finset.mem_filter, Finset.mem_piAntidiag]
      refine ⟨⟨?_, fun i _ => Finset.mem_univ i⟩, by simp⟩
      rw [Fin.sum_univ_succ, Fin.cons_zero] at *
      rw [← hg.1]; simp [Fin.tail]; ring
    · intro f hf
      rw [Finset.mem_filter, Finset.mem_piAntidiag] at hf
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      have h1 := hf.1.1
      rw [Fin.sum_univ_succ] at h1 ⊢
      simp only [Fin.cons_zero, Fin.cons_succ]
      simp only [Fin.tail] 
      omega
    · intro g _; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]
    · intro f hf
      rw [Finset.mem_filter] at hf
      ext i; refine Fin.cases ?_ (fun j => ?_) i
      · simp; omega
      · simp [Fin.tail]
    · intro g _
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp [Fin.tail, pow_succ]; ring
  · -- f 0 = 0
    symm
    refine Finset.sum_nbij' (fun g => Fin.cons 0 g) (fun f => Fin.tail f) ?_ ?_ ?_ ?_ ?_
    · intro g hg
      rw [Finset.mem_piAntidiag] at hg
      rw [Finset.mem_filter, Finset.mem_piAntidiag]
      refine ⟨⟨?_, fun i _ => Finset.mem_univ i⟩, by simp⟩
      rw [Fin.sum_univ_succ]; simpa using hg.1
    · intro f hf
      rw [Finset.mem_filter, Finset.mem_piAntidiag] at hf
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      have h1 := hf.1.1
      rw [Fin.sum_univ_succ, hf.2, zero_add] at h1
      exact h1
    · intro g _; rfl
    · intro f hf
      rw [Finset.mem_filter] at hf
      ext i; refine Fin.cases ?_ (fun j => ?_) i
      · simp [hf.2]
      · simp [Fin.tail]
    · intro g _
      rw [Fin.prod_univ_succ]; simp [Fin.tail]


lemma DD_add (p q : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) :
    dividedDifference (p + q) a x = dividedDifference p a x + dividedDifference q a x := by
  set N := p.natDegree + q.natDegree + 1
  rw [DD_range (p + q) a x N (lt_of_le_of_lt (natDegree_add_le _ _) (by omega)),
    DD_range p a x N (by omega), DD_range q a x N (by omega), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp [coeff_add, add_mul]

lemma DD_smul (c : ℝ) (p : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) :
    dividedDifference (C c * p) a x = c * dividedDifference p a x := by
  set N := p.natDegree + 1
  rw [DD_range (C c * p) a x N (lt_of_le_of_lt (natDegree_C_mul_le _ _) (by omega)),
    DD_range p a x N (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp [coeff_C_mul, mul_assoc]

lemma DD_sub (p q : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) :
    dividedDifference (p - q) a x = dividedDifference p a x - dividedDifference q a x := by
  have h := DD_add (p - q) q a x
  rw [sub_add_cancel] at h; linarith

lemma DD_zero_order (p : Polynomial ℝ) (x : Fin 1 → ℝ) : dividedDifference p 0 x = p.eval (x 0) := by
  rw [DD_range p 0 x (p.natDegree + 1) (by omega), eval_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [hh_fin1]

lemma DD_X_mul (p : Polynomial ℝ) (b : ℕ) (x : Fin (b+2) → ℝ) :
    dividedDifference (X * p) (b+1) x =
      x 0 * dividedDifference p (b+1) x + dividedDifference p b (Fin.tail x) := by
  set N := p.natDegree + 1
  rw [DD_range (X * p) (b+1) x (N+1) (lt_of_le_of_lt (natDegree_mul_le) (by
      simp only [natDegree_X]; omega)),
    DD_range p (b+1) x N (by omega), DD_range p b (Fin.tail x) N (by omega),
    Finset.sum_range_succ', Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [Nat.le_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, add_zero, coeff_X_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hbj : b + 1 ≤ j
  · rw [if_pos (show b + 1 ≤ j + 1 by omega), if_pos hbj, if_pos (show b ≤ j by omega)]
    rw [show j + 1 - (b + 1) = (j - (b+1)) + 1 by omega, hh_succ,
      show j - (b+1) + 1 = j - b by omega]
    ring
  · by_cases hb : b = j
    · subst hb
      rw [if_pos (show b + 1 ≤ b + 1 by omega), if_neg hbj, if_pos le_rfl]
      simp [hh_zero]
    · rw [if_neg (show ¬ (b + 1 ≤ j + 1) by omega), if_neg hbj, if_neg (show ¬ (b ≤ j) by omega)]; ring

lemma DD_lin_mul (c s : ℝ) (p : Polynomial ℝ) (b : ℕ) (x : Fin (b+2) → ℝ) :
    dividedDifference ((C c + C s * X) * p) (b+1) x =
      (c + s * x 0) * dividedDifference p (b+1) x + s * dividedDifference p b (Fin.tail x) := by
  rw [add_mul, DD_add, mul_assoc, DD_smul, DD_smul, DD_X_mul]; ring

lemma DD_perm (p : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) (σ : Equiv.Perm (Fin (a+1))) :
    dividedDifference p a (x ∘ σ) = dividedDifference p a x := by
  rw [DD_eq, DD_eq]; simp only [hh_perm]

lemma DD_low (p : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) (h : p.natDegree < a) :
    dividedDifference p a x = 0 := by
  rw [DD_range p a x a h]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  simp at hj; rw [if_neg (by omega)]


/-! ### recursive representation -/

def Rf : (k a : ℕ) → (Fin (a+1) → ℝ) → ℝ
  | k, 0, y => if k = 0 then 1/2 else (Chebyshev.T ℝ k).eval (y 0)
  | k, a+1, y => 2 * ∑ m ∈ Finset.range k,
      (Chebyshev.U ℝ m).eval (y 0) * Rf (k - 1 - m) a (Fin.tail y)

lemma U_rec (m : ℕ) (t : ℝ) :
    (Chebyshev.U ℝ ((m+2 : ℕ) : ℤ)).eval t =
      2 * t * (Chebyshev.U ℝ ((m+1 : ℕ) : ℤ)).eval t - (Chebyshev.U ℝ (m : ℤ)).eval t := by
  have := Chebyshev.U_add_two ℝ (m : ℤ)
  push_cast
  rw [this]; simp

lemma Rf_rec (k b : ℕ) (y : Fin (b+2) → ℝ) :
    Rf (k+2) (b+1) y = 2 * y 0 * Rf (k+1) (b+1) y + 2 * Rf (k+1) b (Fin.tail y) - Rf k (b+1) y := by
  simp only [Rf]
  set r : ℕ → ℝ := fun j => Rf j b (Fin.tail y) with hr
  set u : ℕ → ℝ := fun m => (Chebyshev.U ℝ (m : ℤ)).eval (y 0) with hu
  have hu0 : u 0 = 1 := by simp [hu]
  have hu1 : u 1 = 2 * y 0 := by simp [hu]
  have hu2 : ∀ m, u (m+2) = 2 * y 0 * u (m+1) - u m := fun m => U_rec m (y 0)
  show 2 * ∑ m ∈ Finset.range (k+2), u m * r (k + 2 - 1 - m) =
    2 * y 0 * (2 * ∑ m ∈ Finset.range (k+1), u m * r (k + 1 - 1 - m)) + 2 * r (k+1) -
      2 * ∑ m ∈ Finset.range k, u m * r (k - 1 - m)
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ' _ k]
  simp only [hu0, hu1, hu2]
  have e1 : ∀ m ∈ Finset.range k, (2 * y 0 * u (m+1) - u m) * r (k + 2 - 1 - (m + 1 + 1)) =
      2 * y 0 * (u (m+1) * r (k + 1 - 1 - (m+1))) - u m * r (k - 1 - m) := by
    intro m hm; simp at hm
    rw [show k + 2 - 1 - (m + 1 + 1) = k - 1 - m by omega,
      show k + 1 - 1 - (m + 1) = k - 1 - m by omega]; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [show k + 2 - 1 - (0 + 1) = k by omega, show k + 2 - 1 - 0 = k + 1 by omega,
    show k + 1 - 1 - 0 = k by omega]
  ring

lemma T_comp_rec (k : ℕ) (L : Polynomial ℝ) :
    (Chebyshev.T ℝ ((k+2 : ℕ) : ℤ)).comp L =
      (C 0 + C 2 * L) * (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)).comp L - (Chebyshev.T ℝ (k : ℤ)).comp L := by
  have h1 : ((k+2 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
  have h2 : ((k+1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  rw [h1, h2, Chebyshev.T_add_two, sub_comp, mul_comp, mul_comp, X_comp]
  have h3 : (2 : ℝ[X]).comp L = C 2 := by
    rw [show (2 : ℝ[X]) = C 2 from rfl, C_comp]
  rw [h3, C_0, zero_add]

lemma DD_identity (c s : ℝ) : ∀ (a k : ℕ) (x : Fin (a+1) → ℝ), (1 ≤ a ∨ 1 ≤ k) →
    dividedDifference ((Chebyshev.T ℝ (k : ℤ)).comp (C c + C s * X)) a x =
      s ^ a * Rf k a (fun i => c + s * x i) := by
  intro a
  induction a with
  | zero =>
    intro k x hk
    have hk' : k ≠ 0 := by omega
    rw [DD_zero_order, eval_comp]
    simp [Rf, hk']
  | succ b ih =>
    have key : ∀ k : ℕ, (∀ x : Fin (b+2) → ℝ, dividedDifference ((Chebyshev.T ℝ (k : ℤ)).comp
          (C c + C s * X)) (b+1) x = s ^ (b+1) * Rf k (b+1) (fun i => c + s * x i)) ∧
        (∀ x : Fin (b+2) → ℝ, dividedDifference ((Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)).comp
          (C c + C s * X)) (b+1) x = s ^ (b+1) * Rf (k+1) (b+1) (fun i => c + s * x i)) := by
      intro k
      induction k with
      | zero =>
        constructor
        · intro x
          rw [DD_low _ _ _ (by simp)]
          simp [Rf]
        · intro x
          have h1 : (Chebyshev.T ℝ ((0+1 : ℕ) : ℤ)).comp (C c + C s * X) = (C c + C s * X) * 1 := by
            simp
          rw [h1, DD_lin_mul, DD_low 1 (b+1) x (by simp), mul_zero, zero_add]
          simp only [Rf, Finset.sum_range_one, Nat.sub_self, zero_tsub]
          rcases b with _ | b'
          · rw [DD_zero_order]; simp [Rf]
          · rw [DD_low 1 _ _ (by simp)]; simp [Rf]
      | succ k ihk =>
        refine ⟨ihk.2, fun x => ?_⟩
        rw [show k + 1 + 1 = k + 2 by ring, T_comp_rec, DD_sub,
          show C 0 + C 2 * (C c + C s * X) = C (2 * c) + C (2 * s) * X by simp [C_mul]; ring,
          DD_lin_mul, ihk.2 x, ihk.1 x, ih (k+1) (Fin.tail x) (Or.inr (by omega)), Rf_rec,
          show (Fin.tail fun i => c + s * x i) = (fun i => c + s * Fin.tail x i) from rfl]
        ring
    intro k x _
    exact (key k).1 x


/-! ### separated representations: closure -/

lemma sep_mono {a : ℕ} {I : Set ℝ} {f : (Fin (a+1) → ℝ) → ℝ} {M M' : ℝ}
    (h : HasSeparatedBound a I f M) (hM : M ≤ M') : HasSeparatedBound a I f M' := by
  obtain ⟨L, c, g, B, hB, hrep, hs⟩ := h
  exact ⟨L, c, g, B, hB, hrep, hs.trans hM⟩

lemma sep_congr {a : ℕ} {I : Set ℝ} {f f' : (Fin (a+1) → ℝ) → ℝ} {M : ℝ}
    (h : HasSeparatedBound a I f M) (he : ∀ x, (∀ i, x i ∈ I) → f' x = f x) :
    HasSeparatedBound a I f' M := by
  obtain ⟨L, c, g, B, hB, hrep, hs⟩ := h
  exact ⟨L, c, g, B, hB, fun x hx => (he x hx).trans (hrep x hx), hs⟩

lemma sep_zero (a : ℕ) (I : Set ℝ) : HasSeparatedBound a I (fun _ => 0) 0 :=
  ⟨0, Fin.elim0, fun α => Fin.elim0 α, fun α => Fin.elim0 α, fun α => Fin.elim0 α,
    fun x _ => by simp, by simp⟩

lemma sep_base (I : Set ℝ) (φ : ℝ → ℝ) {Bφ : ℝ} (hB0 : 0 ≤ Bφ) (hB : ∀ t ∈ I, |φ t| ≤ Bφ) :
    HasSeparatedBound 0 I (fun x => φ (x 0)) Bφ :=
  ⟨1, fun _ => 1, fun _ _ => φ, fun _ _ => Bφ, fun _ _ => ⟨hB0, hB⟩,
    fun x _ => by simp, by simp⟩

lemma sep_add {a : ℕ} {I : Set ℝ} {f₁ f₂ : (Fin (a+1) → ℝ) → ℝ} {M₁ M₂ : ℝ}
    (h₁ : HasSeparatedBound a I f₁ M₁) (h₂ : HasSeparatedBound a I f₂ M₂) :
    HasSeparatedBound a I (fun x => f₁ x + f₂ x) (M₁ + M₂) := by
  obtain ⟨L₁, c₁, g₁, B₁, hB₁, hr₁, hs₁⟩ := h₁
  obtain ⟨L₂, c₂, g₂, B₂, hB₂, hr₂, hs₂⟩ := h₂
  refine ⟨L₁ + L₂, Fin.append c₁ c₂, Fin.append g₁ g₂, Fin.append B₁ B₂, ?_, ?_, ?_⟩
  · intro α i
    refine Fin.addCases (fun α => ?_) (fun α => ?_) α
    · simp only [Fin.append_left]; exact hB₁ α i
    · simp only [Fin.append_right]; exact hB₂ α i
  · intro x hx
    beta_reduce
    rw [Fin.sum_univ_add, hr₁ x hx, hr₂ x hx]
    simp [Fin.append_left, Fin.append_right]
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    linarith

lemma sep_smul {a : ℕ} {I : Set ℝ} {f : (Fin (a+1) → ℝ) → ℝ} {M : ℝ} (r : ℝ)
    (h : HasSeparatedBound a I f M) : HasSeparatedBound a I (fun x => r * f x) (|r| * M) := by
  obtain ⟨L, c, g, B, hB, hrep, hs⟩ := h
  refine ⟨L, fun α => r * c α, g, B, hB, fun x hx => ?_, ?_⟩
  · beta_reduce; rw [hrep x hx, Finset.mul_sum]; simp only [mul_assoc]
  · simp only [abs_mul, mul_assoc, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hs (abs_nonneg r)

lemma sep_sum {a : ℕ} {I : Set ℝ} (n : ℕ) {f : ℕ → (Fin (a+1) → ℝ) → ℝ} {M : ℕ → ℝ}
    (h : ∀ m < n, HasSeparatedBound a I (f m) (M m)) :
    HasSeparatedBound a I (fun x => ∑ m ∈ Finset.range n, f m x) (∑ m ∈ Finset.range n, M m) := by
  induction n with
  | zero => simpa using sep_zero a I
  | succ n ih =>
    have := sep_add (ih (fun m hm => h m (by omega))) (h n (by omega))
    simpa [Finset.sum_range_succ] using this

lemma sep_cons {a : ℕ} {I : Set ℝ} {g : (Fin (a+1) → ℝ) → ℝ} {M : ℝ} (φ : ℝ → ℝ) {Bφ : ℝ}
    (hB0 : 0 ≤ Bφ) (hB : ∀ t ∈ I, |φ t| ≤ Bφ) (h : HasSeparatedBound a I g M) :
    HasSeparatedBound (a+1) I (fun x => φ (x 0) * g (Fin.tail x)) (Bφ * M) := by
  obtain ⟨L, c, g', B, hB', hrep, hs⟩ := h
  refine ⟨L, c, fun α => Fin.cons φ (g' α), fun α => Fin.cons Bφ (B α), ?_, ?_, ?_⟩
  · intro α i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]; exact ⟨hB0, hB⟩
    · simp only [Fin.cons_succ]; exact hB' α j
  · intro x hx
    beta_reduce
    rw [hrep (Fin.tail x) (fun i => hx i.succ), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    conv_rhs => rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]; ring
  · have : ∑ α, |c α| * ∏ i, (Fin.cons Bφ (B α) : Fin (a+2) → ℝ) i =
        Bφ * ∑ α, |c α| * ∏ i, B α i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [Fin.prod_univ_succ]; simp; ring
    rw [this]; exact mul_le_mul_of_nonneg_left hs hB0

lemma sep_perm {a : ℕ} {I : Set ℝ} {f : (Fin (a+1) → ℝ) → ℝ} {M : ℝ}
    (h : HasSeparatedBound a I f M) (σ : Equiv.Perm (Fin (a+1))) :
    HasSeparatedBound a I (fun x => f (x ∘ σ)) M := by
  obtain ⟨L, c, g, B, hB, hrep, hs⟩ := h
  refine ⟨L, c, fun α i => g α (σ.symm i), fun α i => B α (σ.symm i), fun α i => hB α _, ?_, ?_⟩
  · intro x hx
    beta_reduce
    rw [hrep (x ∘ σ) (fun i => hx _)]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    congr 1
    rw [← Equiv.prod_comp σ (fun i => g α (σ.symm i) (x i))]
    simp
  · refine le_trans (le_of_eq ?_) hs
    refine Finset.sum_congr rfl (fun α _ => ?_)
    congr 1
    exact Equiv.prod_comp σ.symm (B α)

lemma sep_affine {a : ℕ} {I J : Set ℝ} {f : (Fin (a+1) → ℝ) → ℝ} {M : ℝ} (c s : ℝ)
    (h : HasSeparatedBound a J f M) (hIJ : ∀ t ∈ I, c + s * t ∈ J) :
    HasSeparatedBound a I (fun x => f (fun i => c + s * x i)) M := by
  obtain ⟨L, cc, g, B, hB, hrep, hs⟩ := h
  refine ⟨L, cc, fun α i t => g α i (c + s * t), B, fun α i => ⟨(hB α i).1,
    fun t ht => (hB α i).2 _ (hIJ t ht)⟩, fun x hx => hrep _ (fun i => hIJ _ (hx i)), hs⟩


/-! ### Chebyshev sup bounds -/

lemma abs_sin_nat_mul_le (u : ℝ) : ∀ n : ℕ, |Real.sin (n * u)| ≤ n * |Real.sin u|
  | 0 => by simp
  | n+1 => by
    have ih := abs_sin_nat_mul_le u n
    have : Real.sin ((n+1 : ℕ) * u) = Real.sin (n*u) * Real.cos u + Real.cos (n*u) * Real.sin u := by
      push_cast; rw [add_mul, one_mul, Real.sin_add]
    rw [this]
    calc |Real.sin (n*u) * Real.cos u + Real.cos (n*u) * Real.sin u|
        ≤ |Real.sin (n*u)| * |Real.cos u| + |Real.cos (n*u)| * |Real.sin u| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |Real.sin (n*u)| * 1 + 1 * |Real.sin u| := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ ≤ ((n+1 : ℕ) : ℝ) * |Real.sin u| := by push_cast; nlinarith

lemma T_abs_le (k : ℕ) {y : ℝ} (hy : y ∈ Set.Icc (-1:ℝ) 1) : |(Chebyshev.T ℝ (k:ℤ)).eval y| ≤ 1 := by
  rw [← Real.cos_arccos hy.1 hy.2, Chebyshev.T_real_cos]; exact Real.abs_cos_le_one _

lemma U_sin (m : ℕ) {y : ℝ} (hy : y ∈ Set.Icc (-1:ℝ) 1) :
    (Chebyshev.U ℝ (m:ℤ)).eval y * Real.sqrt (1 - y^2) = Real.sin ((m+1) * Real.arccos y) := by
  have h := Chebyshev.U_real_cos (Real.arccos y) (m : ℤ)
  rw [Real.cos_arccos hy.1 hy.2, Real.sin_arccos] at h
  rw [h]; push_cast; ring_nf

lemma U_sq_le (m : ℕ) {y : ℝ} (hy : y ∈ Set.Icc (-1:ℝ) 1) :
    (Chebyshev.U ℝ (m:ℤ)).eval y ^ 2 * (1 - y^2) ≤ 1 := by
  have h := U_sin m hy
  have h1 : 0 ≤ 1 - y^2 := by nlinarith [hy.1, hy.2]
  have h2 := Real.sq_sqrt h1
  calc (Chebyshev.U ℝ (m:ℤ)).eval y ^ 2 * (1 - y^2) =
      ((Chebyshev.U ℝ (m:ℤ)).eval y * Real.sqrt (1 - y^2))^2 := by rw [mul_pow, h2]
    _ = Real.sin ((m+1) * Real.arccos y) ^ 2 := by rw [h]
    _ ≤ 1 := Real.sin_sq_le_one _

lemma U_abs_le (m : ℕ) {y : ℝ} (hy : y ∈ Set.Icc (-1:ℝ) 1) :
    |(Chebyshev.U ℝ (m:ℤ)).eval y| ≤ m + 1 := by
  have h := U_sin m hy
  have hs : Real.sqrt (1 - y^2) = Real.sin (Real.arccos y) := (Real.sin_arccos y).symm
  have hsin := abs_sin_nat_mul_le (Real.arccos y) (m+1)
  have hsnn : 0 ≤ Real.sin (Real.arccos y) := by rw [← hs]; exact Real.sqrt_nonneg _
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (1-y^2)) with h0 | hpos
  · have hy2 : 1 - y^2 ≤ 0 := Real.sqrt_eq_zero'.mp h0.symm
    have : y = 1 ∨ y = -1 := by
      have h1 : y^2 = 1 := by nlinarith [hy.1, hy.2]
      have h2 : (y - 1) * (y + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp h2 with h | h
      · left; linarith
      · right; linarith
    rcases this with rfl | rfl
    · rw [Chebyshev.U_eval_one]; push_cast; rw [abs_of_nonneg (by positivity)]
    · rw [Chebyshev.U_eval_neg_one, abs_mul]
      simp [Int.cast_negOnePow, abs_of_nonneg (by positivity : (0:ℝ) ≤ m + 1)]
  · have h' : |(Chebyshev.U ℝ (m:ℤ)).eval y| * Real.sqrt (1 - y^2) ≤ (m + 1) * Real.sqrt (1 - y^2) := by
      rw [← abs_of_pos hpos, ← abs_mul, h, abs_of_pos hpos, hs]
      have : ((m + 1 : ℕ) : ℝ) * Real.arccos y = (m + 1) * Real.arccos y := by push_cast; ring
      rw [← this]; push_cast at hsin ⊢
      rw [abs_of_nonneg hsnn] at hsin; exact hsin
    exact le_of_mul_le_mul_right h' hpos


/-! ### representation of Rf -/

def Bnd (Usup : ℕ → ℝ) (Tsup : ℝ) : ℕ → ℕ → ℝ
  | k, 0 => if k = 0 then 1/2 else Tsup
  | k, a+1 => 2 * ∑ m ∈ Finset.range k, Usup m * Bnd Usup Tsup (k - 1 - m) a

lemma rep_Rf (J : Set ℝ) (Usup : ℕ → ℝ) (Tsup : ℝ) (hU0 : ∀ m, 0 ≤ Usup m) (hT0 : 0 ≤ Tsup)
    (hU : ∀ m : ℕ, ∀ t ∈ J, |(Chebyshev.U ℝ (m:ℤ)).eval t| ≤ Usup m)
    (hT : ∀ k : ℕ, 1 ≤ k → ∀ t ∈ J, |(Chebyshev.T ℝ (k:ℤ)).eval t| ≤ Tsup) :
    ∀ a k, HasSeparatedBound a J (Rf k a) (Bnd Usup Tsup k a) := by
  intro a
  induction a with
  | zero =>
    intro k
    by_cases hk : k = 0
    · subst hk
      have := sep_base J (fun _ => (1/2 : ℝ)) (Bφ := 1/2) (by norm_num) (fun t _ => by norm_num)
      refine sep_congr (sep_mono this (by simp [Bnd])) (fun x _ => by simp [Rf])
    · have := sep_base J (fun t => (Chebyshev.T ℝ (k:ℤ)).eval t) hT0 (hT k (by omega))
      refine sep_congr (sep_mono this (by simp [Bnd, hk])) (fun x _ => by simp [Rf, hk])
  | succ a ih =>
    intro k
    have hs := sep_sum k (fun m _ => sep_cons (fun t => 2 * (Chebyshev.U ℝ (m:ℤ)).eval t)
      (Bφ := 2 * Usup m) (by linarith [hU0 m])
      (fun t ht => by rw [abs_mul]; have := hU m t ht; norm_num; linarith) (ih (k - 1 - m)))
    refine sep_congr (sep_mono hs (le_of_eq ?_)) (fun x _ => ?_)
    · simp only [Bnd, Finset.mul_sum]; refine Finset.sum_congr rfl (fun m _ => by ring)
    · simp only [Rf, Finset.mul_sum]; refine Finset.sum_congr rfl (fun m _ => by ring)

lemma card_tuples (a m k : ℕ) (hmk : m ≤ k) :
    ((Finset.pi Finset.univ (fun _ : Fin (a+1) => Finset.range (k+1))).filter
      (fun r => (∑ i, r i (Finset.mem_univ i)) = m)).card = (a + m).choose m := by
  have h1 : ((Finset.pi Finset.univ (fun _ : Fin (a+1) => Finset.range (k+1))).filter
      (fun r => (∑ i, r i (Finset.mem_univ i)) = m)).card =
      (Finset.piAntidiag (Finset.univ : Finset (Fin (a+1))) m).card := by
    refine Finset.card_nbij' (fun r i => r i (Finset.mem_univ i)) (fun f i _ => f i) ?_ ?_ ?_ ?_
    · intro r hr
      rw [Finset.mem_coe, Finset.mem_filter] at hr
      rw [Finset.mem_coe, Finset.mem_piAntidiag]
      exact ⟨hr.2, fun i _ => Finset.mem_univ i⟩
    · intro f hf
      rw [Finset.mem_coe, Finset.mem_piAntidiag] at hf
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_pi]
      refine ⟨fun i _ => ?_, hf.1⟩
      have h3 : f i ≤ m := calc f i ≤ Finset.univ.sum f :=
            Finset.single_le_sum (f := f) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = m := hf.1
      rw [Finset.mem_range]; show f i < k + 1; omega
    · intro r _; rfl
    · intro f _; rfl
  rw [h1, ← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ, Finset.card_univ,
    Sym.card_sym_fin_eq_multichoose, Nat.multichoose_eq]
  congr 1; omega

lemma dd_repeated (p : Polynomial ℝ) (a : ℕ) (x : ℝ) :
    (a.factorial : ℝ) * dividedDifference p a (fun _ => x) = (derivative^[a] p).eval x := by
  conv_rhs => rw [p.as_sum_support_C_mul_X_pow]
  rw [Polynomial.iterate_derivative_sum, Polynomial.eval_finsetSum, dividedDifference,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_smul,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_smul, Polynomial.eval_pow,
    Polynomial.eval_X, smul_eq_mul]
  split_ifs with hk
  · have hprod : ∀ r ∈ (Finset.pi Finset.univ (fun _ : Fin (a+1) => Finset.range (k+1))).filter
        (fun r => (∑ i, r i (Finset.mem_univ i)) = k - a),
        ∏ i, x ^ (r i (Finset.mem_univ i)) = x ^ (k - a) := by
      intro r hr
      rw [Finset.prod_pow_eq_pow_sum, (Finset.mem_filter.mp hr).2]
    rw [Finset.sum_congr rfl hprod, Finset.sum_const, card_tuples a (k - a) k (by omega), nsmul_eq_mul,
      show a + (k - a) = k by omega, Nat.choose_symm hk, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; ring
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]; simp


/-! ### numeric bounds -/

lemma hockey (a : ℕ) : ∀ k, ∑ j ∈ Finset.range k, (j.choose a : ℝ) = (k.choose (a+1) : ℝ)
  | 0 => by simp
  | k+1 => by
    rw [Finset.sum_range_succ, hockey a k, Nat.choose_succ_succ' k a]; push_cast; ring

lemma bnd2_le : ∀ a k, Bnd (fun _ => 2) 1 k a ≤ 4^a * (k.choose a : ℝ) := by
  intro a
  induction a with
  | zero => intro k; simp only [Bnd]; split_ifs <;> simp; norm_num
  | succ a ih =>
    intro k
    simp only [Bnd]
    calc 2 * ∑ m ∈ Finset.range k, 2 * Bnd (fun _ => 2) 1 (k - 1 - m) a
        ≤ 2 * ∑ m ∈ Finset.range k, 2 * (4^a * ((k - 1 - m).choose a : ℝ)) := by
          gcongr with m hm; exact ih _
      _ = 4^(a+1) * ∑ j ∈ Finset.range k, (j.choose a : ℝ) := by
          simp only [Finset.mul_sum]
          rw [← Finset.sum_range_reflect (fun j => 4^(a+1) * (j.choose a : ℝ)) k]
          refine Finset.sum_congr rfl (fun m _ => ?_); ring
      _ = 4^(a+1) * ((k.choose (a+1)) : ℝ) := by rw [hockey]

lemma fact_two (a : ℕ) : (((2*a).factorial : ℕ) : ℝ) =
    2^a * (a.factorial : ℝ) * ∏ l ∈ Finset.range a, (2 * (l:ℝ) + 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show 2 * (a+1) = 2 * a + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    rw [ih, Finset.prod_range_succ]; ring

lemma bnd1_eq : ∀ a k, Bnd (fun m => (m:ℝ) + 1) 1 k a = Rf k a (fun _ => 1) := by
  intro a
  induction a with
  | zero => intro k; simp [Bnd, Rf]
  | succ a ih =>
    intro k
    simp only [Bnd, Rf]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [ih, Chebyshev.U_eval_one]; push_cast; rfl

lemma Rf_ones (a k : ℕ) (ha : 1 ≤ a) :
    Rf k a (fun _ => 1) = (derivative^[a] (Chebyshev.T ℝ (k:ℤ))).eval 1 / a.factorial := by
  have h := DD_identity 0 1 a k (fun _ => 1) (Or.inl ha)
  simp only [one_pow, one_mul, mul_one, zero_add, map_zero, map_one, one_mul] at h
  rw [comp_X] at h
  have hd := dd_repeated (Chebyshev.T ℝ (k:ℤ)) a 1
  rw [← h, ← hd]
  have : (0:ℝ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
  field_simp

lemma Tderiv_le (a k : ℕ) (hk : a ≤ k) :
    (derivative^[a] (Chebyshev.T ℝ (k:ℤ))).eval 1 / a.factorial ≤ (2 * (k:ℝ)^2)^a / ((2*a).factorial : ℝ) := by
  have h := Chebyshev.iterate_derivative_T_eval_one (R := ℝ) (k:ℤ) a
  have hP : 0 < ∏ l ∈ Finset.range a, (2 * (l:ℝ) + 1) := Finset.prod_pos (fun l _ => by positivity)
  have hf : (0:ℝ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
  have hD : (derivative^[a] (Chebyshev.T ℝ (k:ℤ))).eval 1 =
      (∏ l ∈ Finset.range a, ((k:ℝ)^2 - (l:ℝ)^2)) / ∏ l ∈ Finset.range a, (2 * (l:ℝ) + 1) := by
    rw [eq_div_iff hP.ne', mul_comm]; push_cast at h; exact h
  have hprod : ∏ l ∈ Finset.range a, ((k:ℝ)^2 - (l:ℝ)^2) ≤ ((k:ℝ)^2)^a := by
    calc ∏ l ∈ Finset.range a, ((k:ℝ)^2 - (l:ℝ)^2) ≤ ∏ _l ∈ Finset.range a, (k:ℝ)^2 := by
          apply Finset.prod_le_prod
          · intro l hl; simp at hl
            have : (l:ℝ) ≤ k := by exact_mod_cast (by omega : l ≤ k)
            nlinarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)]
          · intro l _; nlinarith [sq_nonneg (l:ℝ)]
      _ = _ := by simp
  rw [hD, fact_two, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (∏ l ∈ Finset.range a, ((k:ℝ)^2 - (l:ℝ)^2)) * (2^a * (a.factorial : ℝ) * ∏ l ∈ Finset.range a, (2 * (l:ℝ) + 1))
      ≤ ((k:ℝ)^2)^a * (2^a * (a.factorial : ℝ) * ∏ l ∈ Finset.range a, (2 * (l:ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = (2 * (k:ℝ)^2)^a * ((∏ l ∈ Finset.range a, (2 * (l:ℝ) + 1)) * (a.factorial : ℝ)) := by
        rw [mul_pow, ← pow_mul]; ring

lemma pow_sum_le (p : ℕ) : ∀ k : ℕ, (p+1) * ∑ j ∈ Finset.range k, (j:ℝ)^p ≤ (k:ℝ)^(p+1)
  | 0 => by simp
  | k+1 => by
    rw [Finset.sum_range_succ, mul_add]
    have ih := pow_sum_le p k
    have hb : (k:ℝ)^(p+1) + (p+1) * (k:ℝ)^p ≤ ((k:ℝ)+1)^(p+1) := by
      have h2 : (-2:ℝ) ≤ 1/k := by
        have : (0:ℝ) ≤ 1/k := by positivity
        linarith
      have := one_add_mul_le_pow h2 (p+1)
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rcases Nat.eq_zero_or_pos p with hp | hp
        · subst hp; simp
        · simp [zero_pow (by omega : p ≠ 0)]
      · have hk' : (0:ℝ) < k := by exact_mod_cast hk
        have e : ((k:ℝ)+1)^(p+1) = (k:ℝ)^(p+1) * (1 + 1/k)^(p+1) := by
          rw [← mul_pow]; congr 1; field_simp
        rw [e]
        have e2 : (k:ℝ)^(p+1) * (1 + ((p+1 : ℕ) : ℝ) * (1/k)) = (k:ℝ)^(p+1) + (p+1) * (k:ℝ)^p := by
          field_simp; push_cast; ring
        rw [← e2]; exact mul_le_mul_of_nonneg_left this (by positivity)
    push_cast; linarith


/-! ### the three parts -/

lemma DD_T_eq_Rf (k a : ℕ) (ha : 1 ≤ a) (x : Fin (a+1) → ℝ) :
    dividedDifference (Chebyshev.T ℝ (k:ℤ)) a x = Rf k a x := by
  have h := DD_identity 0 1 a k x (Or.inl ha)
  simp only [one_pow, one_mul, zero_add, map_zero, map_one] at h
  rwa [comp_X] at h

lemma U_le_two (m : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (-(1/2):ℝ) (1/2)) :
    |(Chebyshev.U ℝ (m:ℤ)).eval t| ≤ 2 := by
  have h := U_sq_le m (y := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h1 : (3:ℝ)/4 ≤ 1 - t^2 := by nlinarith [ht.1, ht.2]
  have h2 : (Chebyshev.U ℝ (m:ℤ)).eval t ^ 2 ≤ 4 := by nlinarith [sq_nonneg ((Chebyshev.U ℝ (m:ℤ)).eval t)]
  rw [abs_le]; constructor <;> nlinarith

lemma part2 (k a : ℕ) (ha : 1 ≤ a) :
    HasSeparatedBound a (Set.Icc (-(1/2)) (1/2)) (dividedDifference (Chebyshev.T ℝ (k:ℤ)) a)
      ((4*(k : ℝ))^a / (a.factorial : ℝ)) := by
  have rep := rep_Rf (Set.Icc (-(1/2)) (1/2)) (fun _ => 2) 1 (fun _ => by norm_num) (by norm_num)
    (fun m t ht => U_le_two m ht)
    (fun k _ t ht => T_abs_le k ⟨by linarith [ht.1], by linarith [ht.2]⟩) a k
  refine sep_congr (sep_mono rep ?_) (fun x _ => DD_T_eq_Rf k a ha x)
  refine (bnd2_le a k).trans ?_
  have := Nat.choose_le_pow_div (α := ℝ) a k
  calc 4^a * (k.choose a : ℝ) ≤ 4^a * ((k:ℝ)^a / a.factorial) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by positivity)
    _ = (4 * (k:ℝ))^a / a.factorial := by rw [mul_pow]; ring

lemma rep1 : ∀ b n, HasSeparatedBound b (Set.Icc (-1) 1) (Rf n b) (Rf n b (fun _ => 1)) := by
  intro b n
  have := rep_Rf (Set.Icc (-1) 1) (fun m => (m:ℝ) + 1) 1 (fun m => by positivity) (by norm_num)
    (fun m t ht => U_abs_le m ht) (fun k _ t ht => T_abs_le k ht) b n
  rwa [bnd1_eq] at this

lemma part1 (k a : ℕ) (ha : 1 ≤ a) (hk : a ≤ k) :
    HasSeparatedBound a (Set.Icc (-1) 1) (dividedDifference (Chebyshev.T ℝ (k:ℤ)) a)
      ((2*(k : ℝ)^2)^a / ((2*a).factorial : ℝ)) := by
  refine sep_congr (sep_mono (rep1 a k) ?_) (fun x _ => DD_T_eq_Rf k a ha x)
  rw [Rf_ones a k ha]; exact Tderiv_le a k hk

lemma Rf_ones_le (b n : ℕ) (hb : 1 ≤ b) : Rf n b (fun _ => 1) ≤ (2 * (n:ℝ)^2)^b / ((2*b).factorial : ℝ) := by
  by_cases h : b ≤ n
  · rw [Rf_ones b n hb]; exact Tderiv_le b n h
  · rw [Rf_ones b n hb]
    have : derivative^[b] (Chebyshev.T ℝ (n:ℤ)) = 0 := by
      apply iterate_derivative_eq_zero
      rw [Chebyshev.natDegree_T]; simp; omega
    rw [this]; simp; positivity

lemma Rf0_ones_le (n : ℕ) : Rf n 0 (fun _ => 1) ≤ 1 := by
  simp only [Rf]; split_ifs <;> simp; norm_num

lemma sqrtU_le (m : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |2 * (Real.sqrt t * (Chebyshev.U ℝ (m:ℤ)).eval (1 - t))| ≤ 2 := by
  have h := U_sq_le m (y := 1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have e : 1 - (1 - t)^2 = t * (2 - t) := by ring
  rw [e] at h
  have hU2 : t * (Chebyshev.U ℝ (m:ℤ)).eval (1 - t) ^ 2 ≤ 1 := by
    have hp : 0 ≤ t * (Chebyshev.U ℝ (m:ℤ)).eval (1 - t) ^ 2 := mul_nonneg ht.1 (sq_nonneg _)
    have : t * (Chebyshev.U ℝ (m:ℤ)).eval (1 - t) ^ 2 * 1 ≤
        t * (Chebyshev.U ℝ (m:ℤ)).eval (1 - t) ^ 2 * (2 - t) :=
      mul_le_mul_of_nonneg_left (by linarith [ht.2]) hp
    nlinarith
  have hsq : (Real.sqrt t * (Chebyshev.U ℝ (m:ℤ)).eval (1 - t))^2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt ht.1]; exact hU2
  have : |Real.sqrt t * (Chebyshev.U ℝ (m:ℤ)).eval (1 - t)| ≤ 1 := by
    rw [← abs_one, ← sq_le_sq]; simpa using hsq
  rw [abs_mul, abs_two]; linarith

lemma part3_first (k b : ℕ) :
    HasSeparatedBound (b+1) (Set.Icc 0 1)
      (fun y => Real.sqrt (y 0) * dividedDifference ((Chebyshev.T ℝ (k:ℤ)).comp (1 - X)) (b+1) y)
      ((2 : ℝ)^(b+1) * (k : ℝ)^(2*b+1) / ((2*b+1).factorial : ℝ)) := by
  have hsum := sep_sum k (fun m _ => sep_cons
    (fun t => 2 * (Real.sqrt t * (Chebyshev.U ℝ (m:ℤ)).eval (1 - t))) (Bφ := 2) (by norm_num)
    (fun t ht => sqrtU_le m ht)
    (sep_affine 1 (-1) (rep1 b (k - 1 - m)) (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)))
  have hs := sep_smul ((-1:ℝ)^(b+1)) hsum
  refine sep_congr (sep_mono hs ?_) (fun y _ => ?_)
  · rw [abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      have h1 : ∑ m ∈ Finset.range k, 2 * Rf (k - 1 - m) 0 (fun _ => 1) ≤ 2 * k := by
        calc ∑ m ∈ Finset.range k, 2 * Rf (k - 1 - m) 0 (fun _ => 1)
            ≤ ∑ m ∈ Finset.range k, (2:ℝ) * 1 := by gcongr with m; exact Rf0_ones_le _
          _ = 2 * k := by simp; ring
      norm_num; linarith
    · calc ∑ m ∈ Finset.range k, 2 * Rf (k - 1 - m) b (fun _ => 1)
          ≤ ∑ m ∈ Finset.range k, 2 * ((2 * ((k - 1 - m : ℕ):ℝ)^2)^b / ((2*b).factorial : ℝ)) := by
            gcongr with m; exact Rf_ones_le b _ hb
        _ = 2^(b+1) / ((2*b).factorial : ℝ) * ∑ j ∈ Finset.range k, (j:ℝ)^(2*b) := by
            rw [Finset.mul_sum,
              ← Finset.sum_range_reflect (fun j => 2^(b+1) / ((2*b).factorial : ℝ) * (j:ℝ)^(2*b)) k]
            refine Finset.sum_congr rfl (fun m _ => ?_)
            rw [mul_pow, ← pow_mul]; ring
        _ ≤ 2^(b+1) / ((2*b).factorial : ℝ) * ((k:ℝ)^(2*b+1) / (2*b+1)) := by
            gcongr
            have := pow_sum_le (2*b) k
            rw [le_div_iff₀ (by positivity)]; push_cast at this; linarith
        _ = (2 : ℝ)^(b+1) * (k : ℝ)^(2*b+1) / ((2*b+1).factorial : ℝ) := by
            rw [Nat.factorial_succ]; push_cast; field_simp
  · have hid := DD_identity 1 (-1) (b+1) k y (Or.inl (by omega))
    rw [show (1 - X : ℝ[X]) = C 1 + C (-1) * X by simp; ring, hid]
    simp only [Rf, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [show (Fin.tail fun i => (1:ℝ) + -1 * y i) = (fun i => 1 + -1 * y i.succ) from rfl,
      show (1:ℝ) + -1 * y 0 = 1 - y 0 by ring]
    simp only [Fin.tail]
    ring

lemma part3 (k a : ℕ) (ha : 1 ≤ a) (r : Fin (a+1)) :
    HasSeparatedBound a (Set.Icc 0 1)
      (fun x => Real.sqrt (x r) * dividedDifference ((Chebyshev.T ℝ (k:ℤ)).comp (1 - X)) a x)
      ((2 : ℝ)^a * (k : ℝ)^(2*a-1) / ((2*a-1).factorial : ℝ)) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have h0 := sep_perm (part3_first k b) (Equiv.swap 0 r)
  rw [show 2 * (b+1) - 1 = 2 * b + 1 by omega]
  refine sep_congr h0 (fun x _ => ?_)
  simp only [Function.comp_apply, Equiv.swap_apply_left]
  rw [DD_perm]

end OTDB1

open OptimalTraceDistance.Estimation OTDB1 in
theorem solution (k a : ℕ) (ha : 1 ≤ a) (hk : a ≤ k) :
  HasSeparatedBound a (Set.Icc (-1) 1)
    (dividedDifference (Polynomial.Chebyshev.T ℝ k) a)
    ((2*(k : ℝ)^2)^a / ((2*a).factorial : ℝ)) ∧
  HasSeparatedBound a (Set.Icc (-(1/2)) (1/2))
    (dividedDifference (Polynomial.Chebyshev.T ℝ k) a)
    ((4*(k : ℝ))^a / (a.factorial : ℝ)) ∧
  ∀ r : Fin (a+1), r.val = 0 ∨ r.val = a →
    HasSeparatedBound a (Set.Icc 0 1)
      (fun x => Real.sqrt (x r) * dividedDifference
        ((Polynomial.Chebyshev.T ℝ k).comp (1-Polynomial.X)) a x)
      ((2 : ℝ)^a * (k : ℝ)^(2*a-1) / ((2*a-1).factorial : ℝ)) :=
  ⟨part1 k a ha hk, part2 k a ha, fun r _ => part3 k a ha r⟩
