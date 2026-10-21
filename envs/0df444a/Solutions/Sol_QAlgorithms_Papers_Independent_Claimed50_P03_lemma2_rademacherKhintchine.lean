-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.lemma2_rademacherKhintchine
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:09:25.87817+00:00
-- url     : https://prove2.me/submissions/8eeb50a1-b8ba-48f3-b51d-fbbfbe623ad1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate Matrix

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace


def g59a_chi {n : ℕ} (A : Finset (Fin n)) (σ : Fin n → Bool) : ℝ := ∏ i ∈ A, rademacherValue (σ i)

def g59a_hat {n : ℕ} (f : (Fin n → Bool) → ℝ) (A : Finset (Fin n)) : ℝ :=
  (∑ σ, f σ * g59a_chi A σ) / 2 ^ n

lemma g59a_rr (b : Bool) : rademacherValue b * rademacherValue b = 1 := by
  cases b <;> simp [rademacherValue]

lemma g59a_rneg (b : Bool) : rademacherValue (!b) = - rademacherValue b := by
  cases b <;> simp [rademacherValue]

lemma g59a_compl {n : ℕ} (σ τ : Fin n → Bool) :
    ∑ A : Finset (Fin n), g59a_chi A σ * g59a_chi A τ = if σ = τ then 2 ^ n else 0 := by
  simp only [g59a_chi, ← Finset.prod_mul_distrib]
  rw [← Finset.powerset_univ, ← Finset.prod_one_add]
  by_cases h : σ = τ
  · subst h; simp [g59a_rr]; norm_num
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    revert hi; cases σ i <;> cases τ i <;> simp [rademacherValue]

lemma g59a_pars {n : ℕ} (f h : (Fin n → Bool) → ℝ) :
    ∑ σ, f σ * h σ = 2 ^ n * ∑ A, g59a_hat f A * g59a_hat h A := by
  unfold g59a_hat
  have e : ∀ A : Finset (Fin n), (∑ σ, f σ * g59a_chi A σ) / 2 ^ n * ((∑ τ, h τ * g59a_chi A τ) / 2 ^ n) =
      (∑ σ, ∑ τ, f σ * h τ * (g59a_chi A σ * g59a_chi A τ)) / (2 ^ n * 2 ^ n) := by
    intro A; rw [div_mul_div_comm, Finset.sum_mul_sum]
    congr 1; refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => by ring
  simp only [e, ← Finset.sum_div]
  rw [Finset.sum_comm]
  have e2 : ∀ σ, ∑ A : Finset (Fin n), ∑ τ, f σ * h τ * (g59a_chi A σ * g59a_chi A τ) =
      f σ * h σ * 2 ^ n := by
    intro σ
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, g59a_compl]
    simp
  simp only [e2, ← Finset.sum_mul]
  field_simp

def g59a_flip {n : ℕ} (i : Fin n) (σ : Fin n → Bool) : Fin n → Bool := Function.update σ i (!σ i)

lemma g59a_flip_inv {n : ℕ} (i : Fin n) : Function.Involutive (g59a_flip i) := by
  intro σ; funext j
  by_cases h : j = i
  · subst h; simp [g59a_flip]
  · simp [g59a_flip, Function.update_of_ne h]

lemma g59a_chi_flip {n : ℕ} (A : Finset (Fin n)) (i : Fin n) (σ : Fin n → Bool) :
    g59a_chi A (g59a_flip i σ) = (if i ∈ A then -1 else 1) * g59a_chi A σ := by
  unfold g59a_chi
  by_cases hi : i ∈ A
  · rw [if_pos hi, ← Finset.mul_prod_erase A _ hi, ← Finset.mul_prod_erase A _ hi]
    have : ∏ x ∈ A.erase i, rademacherValue (g59a_flip i σ x) = ∏ x ∈ A.erase i, rademacherValue (σ x) :=
      Finset.prod_congr rfl fun j hj => by
        rw [g59a_flip, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [this, g59a_flip, Function.update_self, g59a_rneg]; ring
  · rw [if_neg hi, one_mul]
    exact Finset.prod_congr rfl fun j hj => by
      rw [g59a_flip, Function.update_of_ne (fun h : j = i => hi (h ▸ hj))]

lemma g59a_hat_flip {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) (A : Finset (Fin n)) :
    g59a_hat (fun σ => f (g59a_flip i σ)) A = (if i ∈ A then -1 else 1) * g59a_hat f A := by
  unfold g59a_hat
  have : ∑ σ, f (g59a_flip i σ) * g59a_chi A σ = ∑ σ, f σ * g59a_chi A (g59a_flip i σ) :=
    Fintype.sum_equiv (g59a_flip_inv i).toPerm _ _ fun σ => by
      simp [Function.Involutive.coe_toPerm, g59a_flip_inv i σ]
  rw [this]
  simp only [g59a_chi_flip, mul_div_assoc', Finset.mul_sum]
  congr 1; exact Finset.sum_congr rfl fun σ _ => by ring

def g59a_neg {n : ℕ} (σ : Fin n → Bool) : Fin n → Bool := fun j => !σ j

lemma g59a_neg_inv {n : ℕ} : Function.Involutive (g59a_neg (n := n)) := by
  intro σ; funext j; simp [g59a_neg]

lemma g59a_card_sum {n : ℕ} (A : Finset (Fin n)) :
    ∑ i : Fin n, (if i ∈ A then (-1 : ℝ) else 1) = n - 2 * A.card := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  have hc : (Finset.univ.filter fun i => i ∉ A) = Aᶜ := by ext; simp
  rw [hc, Finset.card_compl, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  rw [Nat.cast_sub (by simpa using A.card_le_univ)]; ring

def g59a_S {n : ℕ} (a : Fin n → ℝ) (σ : Fin n → Bool) : ℝ := ∑ i, a i * rademacherValue (σ i)

lemma g59a_hat_single {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    g59a_hat (fun σ => |g59a_S a σ|) {i} = 0 := by
  unfold g59a_hat
  have hX : ∑ σ, |g59a_S a σ| * g59a_chi {i} σ = ∑ σ, |g59a_S a σ| * (- g59a_chi {i} σ) := by
    refine Fintype.sum_equiv (g59a_neg_inv (n := n)).toPerm _ _ fun σ => ?_
    simp only [Function.Involutive.coe_toPerm, g59a_chi, Finset.prod_singleton, g59a_S, g59a_neg,
      g59a_rneg]
    rw [show ∑ j, a j * -rademacherValue (σ j) = -∑ j, a j * rademacherValue (σ j) by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun j _ => by ring, abs_neg]
    simp only [neg_neg]
  have : ∑ σ, |g59a_S a σ| * g59a_chi {i} σ = 0 := by
    simp only [mul_neg, Finset.sum_neg_distrib] at hX; linarith
  rw [this, zero_div]

lemma g59a_rr_sum {n : ℕ} (i j : Fin n) :
    ∑ σ : Fin n → Bool, rademacherValue (σ i) * rademacherValue (σ j) = if i = j then 2 ^ n else 0 := by
  by_cases h : i = j
  · subst h; simp [g59a_rr]
  · rw [if_neg h]
    have hX : ∑ σ : Fin n → Bool, rademacherValue (σ i) * rademacherValue (σ j) =
        ∑ σ : Fin n → Bool, -(rademacherValue (σ i) * rademacherValue (σ j)) := by
      refine Fintype.sum_equiv (g59a_flip_inv i).toPerm _ _ fun σ => ?_
      simp only [Function.Involutive.coe_toPerm, g59a_flip, Function.update_self,
        Function.update_of_ne (Ne.symm h), g59a_rneg]
      ring
    rw [Finset.sum_neg_distrib] at hX; linarith

lemma g59a_sq_sum {n : ℕ} (a : Fin n → ℝ) :
    ∑ σ, |g59a_S a σ| * |g59a_S a σ| = 2 ^ n * ∑ i, a i ^ 2 := by
  simp only [← abs_mul, abs_mul_self]
  simp only [g59a_S, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  have : ∀ i j, ∑ σ : Fin n → Bool, a i * rademacherValue (σ i) * (a j * rademacherValue (σ j)) =
      a i * a j * (if i = j then 2 ^ n else 0) := by
    intro i j; rw [← g59a_rr_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [Finset.sum_congr rfl fun i _ => (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun j _ => this i j))]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma g59a_S_flip {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (σ : Fin n → Bool) :
    g59a_S a (g59a_flip i σ) = g59a_S a σ - 2 * a i * rademacherValue (σ i) := by
  unfold g59a_S
  have : ∀ j, a j * rademacherValue (g59a_flip i σ j) =
      a j * rademacherValue (σ j) - (if j = i then 2 * a i * rademacherValue (σ i) else 0) := by
    intro j
    by_cases h : j = i
    · subst h; simp [g59a_flip, g59a_rneg]; ring
    · simp [g59a_flip, Function.update_of_ne h, h]
  simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma g59a_tri {n : ℕ} (a : Fin n → ℝ) (σ : Fin n → Bool) :
    ((n : ℝ) - 2) * |g59a_S a σ| ≤ ∑ i, |g59a_S a (g59a_flip i σ)| := by
  have hs : ∑ i, g59a_S a (g59a_flip i σ) = ((n : ℝ) - 2) * g59a_S a σ := by
    simp only [g59a_S_flip, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [show ∑ i, 2 * a i * rademacherValue (σ i) = 2 * g59a_S a σ by
      rw [g59a_S, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
    ring
  calc ((n : ℝ) - 2) * |g59a_S a σ| ≤ |((n : ℝ) - 2)| * |g59a_S a σ| :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
    _ = |∑ i, g59a_S a (g59a_flip i σ)| := by rw [hs, abs_mul]
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _

theorem g59a_khintchine (n : ℕ) (a : Fin n → ℝ) :
    let rms := Real.sqrt (∑ i, a i ^ 2)
    let avg := signAverage n (fun sigma => |∑ i, a i * rademacherValue (sigma i)|)
    rms / Real.sqrt 2 ≤ avg ∧ avg ≤ rms := by
  intro rms avg
  set g : (Fin n → Bool) → ℝ := fun σ => |g59a_S a σ| with hg
  set w : Finset (Fin n) → ℝ := fun A => g59a_hat g A * g59a_hat g A with hw
  have hw0 : ∀ A, 0 ≤ w A := fun A => mul_self_nonneg _
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have havg : avg = g59a_hat g ∅ := by
    simp only [avg, signAverage, g59a_hat, g59a_chi, Finset.prod_empty, mul_one]; rfl
  have hsum : ∑ i, a i ^ 2 = ∑ A, w A := by
    have := g59a_pars g g
    rw [show (∑ σ, g σ * g σ) = 2 ^ n * ∑ i, a i ^ 2 from g59a_sq_sum a] at this
    exact mul_left_cancel₀ h2n.ne' this
  have hpar_i : ∀ i, ∑ σ, g σ * g (g59a_flip i σ) =
      2 ^ n * ∑ A, (if i ∈ A then -1 else 1) * w A := by
    intro i
    rw [g59a_pars g (fun σ => g (g59a_flip i σ))]
    simp only [g59a_hat_flip, hw]
    congr 1; exact Finset.sum_congr rfl fun A _ => by ring
  have htri : ((n : ℝ) - 2) * ∑ σ, g σ * g σ ≤ ∑ i, ∑ σ, g σ * g (g59a_flip i σ) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left (g59a_tri a σ) (abs_nonneg (g59a_S a σ))
    simp only [hg]; nlinarith
  simp only [hpar_i] at htri
  rw [g59a_pars g g] at htri
  rw [← Finset.mul_sum, Finset.sum_comm] at htri
  simp only [← Finset.sum_mul, g59a_card_sum] at htri
  have htri' : ((n : ℝ) - 2) * ∑ A, w A ≤ ∑ A, ((n : ℝ) - 2 * A.card) * w A := by
    have : 2 ^ n * (((n : ℝ) - 2) * ∑ A, w A) ≤ 2 ^ n * ∑ A, ((n : ℝ) - 2 * A.card) * w A := by
      simp only [hw]; linarith
    exact le_of_mul_le_mul_left this h2n
  have hterm : ∀ A : Finset (Fin n), (2 - (A.card : ℝ)) * w A ≤ if A = ∅ then 2 * w A else 0 := by
    intro A
    by_cases h0 : A = ∅
    · subst h0; simp
    · rw [if_neg h0]
      by_cases h1 : A.card = 1
      · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
        simp [hw, g59a_hat_single a i, hg]
      · have : 2 ≤ A.card := by
          have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0); omega
        have : (2 : ℝ) ≤ A.card := by exact_mod_cast this
        nlinarith [hw0 A]
  have hb : ∑ A : Finset (Fin n), (2 - (A.card : ℝ)) * w A ≤ 2 * w ∅ := by
    calc _ ≤ ∑ A : Finset (Fin n), (if A = ∅ then 2 * w A else 0) := Finset.sum_le_sum fun A _ => hterm A
      _ = 2 * w ∅ := by rw [Finset.sum_ite_eq']; simp
  have hkey : ∑ A, w A ≤ 2 * w ∅ := by
    have e : ∑ A : Finset (Fin n), w A = ∑ A : Finset (Fin n), (2 - (A.card : ℝ)) * w A -
        (1 / 2) * (∑ A, ((n : ℝ) - 2 * A.card) * w A - ((n : ℝ) - 2) * ∑ A, w A) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun A _ => by ring
    rw [e]; linarith
  have hsingle : w ∅ ≤ ∑ A, w A := Finset.single_le_sum (fun A _ => hw0 A) (Finset.mem_univ _)
  have havg0 : 0 ≤ avg := by
    simp only [avg, signAverage]; exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) h2n.le
  have hw_avg : w ∅ = avg ^ 2 := by rw [havg, sq]
  have hrms : rms = Real.sqrt (∑ A, w A) := by simp only [rms]; rw [hsum]
  constructor
  · rw [div_le_iff₀ (by positivity), hrms]
    calc Real.sqrt (∑ A, w A) ≤ Real.sqrt (2 * avg ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = avg * Real.sqrt 2 := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq havg0, mul_comm]
  · rw [hrms]; exact Real.le_sqrt_of_sq_le (by linarith)

theorem solution (n : ℕ) (a : Fin n → ℝ) :
    let rms := Real.sqrt (∑ i, a i ^ 2)
    let avg := signAverage n (fun sigma => |∑ i, a i * rademacherValue (sigma i)|)
    rms / Real.sqrt 2 ≤ avg ∧ avg ≤ rms := g59a_khintchine n a
