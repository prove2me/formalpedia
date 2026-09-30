-- Prove2me | solution 1 for TranscendenceTheory.small_values_of_bounded_bivariate_systems
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T09:31:46.279032+00:00
-- url     : https://prove2.me/submissions/ce7ba288-2045-403a-9b5b-54c7f6b6214b

import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_TranscendenceTheory_BoundedBivariateSystem

open Polynomial Matrix Finset Filter
open scoped Polynomial

noncomputable section

namespace TranscendenceTheory.BivariateSiegel

def ofBox (D E : ℕ) (v : Fin (E + 1) × Fin (D + 1) → ℤ) : ℤ[X][X] :=
  ofFn (E + 1) fun j => ofFn (D + 1) fun k => v (j, k)

lemma ofBox_coeff (D E : ℕ) (v : Fin (E + 1) × Fin (D + 1) → ℤ)
    (j : Fin (E + 1)) (k : Fin (D + 1)) :
    ((ofBox D E v).coeff j).coeff k = v (j, k) := by
  rw [ofBox, ofFn_coeff_eq_val_of_lt _ j.isLt, ofFn_coeff_eq_val_of_lt _ k.isLt]

lemma ofBox_degree (D E : ℕ) (v : Fin (E + 1) × Fin (D + 1) → ℤ) :
    (ofBox D E v).natDegree ≤ E ∧ ∀ j, ((ofBox D E v).coeff j).natDegree ≤ D := by
  refine ⟨Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _), ?_⟩
  intro j
  by_cases hj : j < E + 1
  · simp only [ofBox, ofFn_coeff_eq_val_of_lt _ hj]
    exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)
  · simp [ofBox, ofFn_coeff_eq_zero_of_ge _ (by omega : E + 1 ≤ j)]

lemma ofBox_eq_sum (D E : ℕ) (v : Fin (E + 1) × Fin (D + 1) → ℤ) :
    ofBox D E v = ∑ j : Fin (E + 1), ∑ k : Fin (D + 1),
      monomial j (monomial k (v (j, k))) := by
  simp only [ofBox, ofFn_eq_sum_monomial, map_sum]

lemma inner_degree_mul (p q : ℤ[X][X]) (D D' : ℕ)
    (hp : ∀ j, (p.coeff j).natDegree ≤ D)
    (hq : ∀ j, (q.coeff j).natDegree ≤ D') :
    ∀ j, ((p * q).coeff j).natDegree ≤ D + D' := by
  intro j
  rw [coeff_mul]
  exact natDegree_sum_le_of_forall_le _ _ fun a _ =>
    (natDegree_mul_le).trans (Nat.add_le_add (hp a.1) (hq a.2))

lemma inner_degree_sum {ι : Type*} (s : Finset ι) (p : ι → ℤ[X][X]) (D : ℕ)
    (hp : ∀ i ∈ s, ∀ j, ((p i).coeff j).natDegree ≤ D) :
    ∀ j, ((∑ i ∈ s, p i).coeff j).natDegree ≤ D := by
  intro j
  rw [finsetSum_coeff]
  exact natDegree_sum_le_of_forall_le _ _ fun i hi => hp i hi j

lemma coeff_mul_monomial' (p : ℤ[X]) (j k : ℕ) (a : ℤ) :
    (p * monomial j a).coeff k = if j ≤ k then p.coeff (k - j) * a else 0 := by
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]

lemma double_coeff_mul_monomial (p : ℤ[X][X]) (j k a b : ℕ) (v : ℤ) :
    ((p * monomial a (monomial b v)).coeff j).coeff k =
      (if a ≤ j ∧ b ≤ k then (p.coeff (j - a)).coeff (k - b) else 0) * v := by
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow']
  by_cases ha : a ≤ j
  · simp only [if_pos ha, coeff_mul_C]
    rw [coeff_mul_monomial']
    split <;> simp_all
  · simp [ha]

attribute [local instance] Matrix.seminormedAddCommGroup

lemma integer_kernel {α β : Type*} [Fintype α] [Fintype β]
    (B : Matrix α β ℤ) (hn : 0 < Fintype.card β)
    (hdim : 2 * Fintype.card α ≤ Fintype.card β)
    (H : ℝ) (hH : 1 ≤ H) (hB : ∀ i j, ‖B i j‖ ≤ H) :
    ∃ v : β → ℤ, v ≠ 0 ∧ B *ᵥ v = 0 ∧ ∀ j, ‖v j‖ ≤ Fintype.card β * H := by
  classical
  have hβ : (1 : ℝ) ≤ Fintype.card β := by exact_mod_cast hn
  have hbound : 1 ≤ (Fintype.card β : ℝ) * H := one_le_mul_of_one_le_of_one_le hβ hH
  by_cases hm : Fintype.card α = 0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hm
    obtain ⟨j⟩ := Fintype.card_pos_iff.mp hn
    refine ⟨fun _ => 1, ?_, by ext i; exact isEmptyElim i, ?_⟩
    · intro h
      have := congrFun h j
      norm_num at this
    · intro j
      simpa using hbound
  · have hmn : Fintype.card α < Fintype.card β := by omega
    have he0 : 0 ≤ (Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α) := by
      apply div_nonneg (Nat.cast_nonneg _)
      exact sub_nonneg.mpr (by exact_mod_cast hmn.le)
    have he1 : (Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α) ≤ 1 := by
      apply (div_le_one (sub_pos.mpr (by exact_mod_cast hmn))).mpr
      have : (2 : ℝ) * Fintype.card α ≤ Fintype.card β := by exact_mod_cast hdim
      linarith
    obtain ⟨v, hv, hvB, hvnorm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le B hmn (by omega)
    refine ⟨v, hv, hvB, fun j => (norm_le_pi_norm v j).trans (hvnorm.trans ?_)⟩
    have hmax : max 1 ‖B‖ ≤ H := max_le hH ((Matrix.norm_le_iff (by linarith)).mpr hB)
    exact (Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)) he0).trans
      (Real.rpow_le_self_of_one_le hbound he1)

theorem bivariate_siegel (m n D E : ℕ) (hn : 0 < n) (hdim : 8 * m ≤ n)
    (B : Matrix (Fin m) (Fin n) ℤ[X][X]) (H : ℝ) (hH : 1 ≤ H)
    (hBy : ∀ r i, (B r i).natDegree ≤ E)
    (hBx : ∀ r i j, ((B r i).coeff j).natDegree ≤ D)
    (hBH : ∀ r i j k, ‖((B r i).coeff j).coeff k‖ ≤ H) :
    ∃ p : Fin n → ℤ[X][X], p ≠ 0 ∧
      (∀ r, ∑ i, B r i * p i = 0) ∧
      (∀ i, (p i).natDegree ≤ E) ∧
      (∀ i j, ((p i).coeff j).natDegree ≤ D) ∧
      ∀ i j k, ‖((p i).coeff j).coeff k‖ ≤ (n : ℝ) * (E + 1) * (D + 1) * H := by
  classical
  let α := Fin m × Fin (2 * E + 1) × Fin (2 * D + 1)
  let β := Fin n × Fin (E + 1) × Fin (D + 1)
  let M : Matrix α β ℤ := fun r i =>
    if i.2.1.val ≤ r.2.1.val ∧ i.2.2.val ≤ r.2.2.val then
      ((B r.1 i.1).coeff (r.2.1.val - i.2.1.val)).coeff (r.2.2.val - i.2.2.val)
    else 0
  have hcardα : Fintype.card α = m * ((2 * E + 1) * (2 * D + 1)) := by simp [α]
  have hcardβ : Fintype.card β = n * ((E + 1) * (D + 1)) := by simp [β]
  have hcard : 2 * Fintype.card α ≤ Fintype.card β := by
    rw [hcardα, hcardβ]
    calc
      _ ≤ (8 * m) * ((E + 1) * (D + 1)) := by nlinarith [Nat.zero_le (m * E), Nat.zero_le (m * D)]
      _ ≤ _ := Nat.mul_le_mul_right _ hdim
  obtain ⟨v, hv, hvM, hvH⟩ := integer_kernel M
    (by rw [hcardβ]; positivity) hcard H hH (fun r i => by
      dsimp [M]
      split
      · exact hBH _ _ _ _
      · simpa using (show 0 ≤ H by linarith))
  let p : Fin n → ℤ[X][X] := fun i => ofBox D E (fun jk => v (i, jk))
  have hpdeg : ∀ i, (p i).natDegree ≤ E ∧ ∀ j, ((p i).coeff j).natDegree ≤ D :=
    fun i => ofBox_degree D E (fun jk => v (i, jk))
  refine ⟨p, ?_, ?_, fun i => (hpdeg i).1, fun i => (hpdeg i).2, ?_⟩
  · intro hp
    apply hv
    funext ⟨i, j, k⟩
    have he := congrArg (fun q : ℤ[X][X] => (q.coeff j).coeff k) (congrFun hp i)
    simpa only [p, ofBox_coeff, Pi.zero_apply, coeff_zero] using he
  · intro r
    have hy : (∑ i, B r i * p i).natDegree ≤ 2 * E :=
      natDegree_sum_le_of_forall_le _ _ fun i _ =>
        (natDegree_mul_le).trans (by have := hBy r i; have := (hpdeg i).1; omega)
    have hx : ∀ j, ((∑ i, B r i * p i).coeff j).natDegree ≤ 2 * D := by
      apply inner_degree_sum
      intro i _
      simpa [two_mul] using inner_degree_mul (B r i) (p i) D D (hBx r i) (hpdeg i).2
    apply Polynomial.ext
    intro j
    by_cases hj : j < 2 * E + 1
    · apply Polynomial.ext
      intro k
      by_cases hk : k < 2 * D + 1
      · have he := congrFun hvM (r, ⟨j, hj⟩, ⟨k, hk⟩)
        simpa only [Matrix.mulVec, dotProduct, β, Fintype.sum_prod_type,
          p, ofBox_eq_sum, Finset.mul_sum, finsetSum_coeff, double_coeff_mul_monomial,
          M, Pi.zero_apply, coeff_zero] using he
      · simp only [coeff_zero]
        exact coeff_eq_zero_of_natDegree_lt ((hx j).trans_lt (by omega))
    · simp only [coeff_zero]
      exact coeff_eq_zero_of_natDegree_lt (hy.trans_lt (by omega))
  · intro i j k
    by_cases hj : j < E + 1
    · by_cases hk : k < D + 1
      · have he := hvH (i, ⟨j, hj⟩, ⟨k, hk⟩)
        rw [hcardβ] at he
        simpa only [p, ofBox, ofFn_coeff_eq_val_of_lt _ hj,
          ofFn_coeff_eq_val_of_lt _ hk, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          mul_assoc] using he
      · rw [coeff_eq_zero_of_natDegree_lt ((hpdeg i).2 j |>.trans_lt (by omega)), norm_zero]
        positivity
    · rw [coeff_eq_zero_of_natDegree_lt ((hpdeg i).1.trans_lt (by omega)), coeff_zero, norm_zero]
      positivity


lemma eq_ofBox (p : ℤ[X][X]) (D E : ℕ) (hy : p.natDegree ≤ E)
    (hx : ∀ j, (p.coeff j).natDegree ≤ D) :
    ofBox D E (fun jk => (p.coeff jk.1).coeff jk.2) = p := by
  have hinner (j : Fin (E + 1)) :
      ofFn (D + 1) (fun k : Fin (D + 1) => (p.coeff j).coeff k) = p.coeff j :=
    ofFn_comp_toFn_eq_id_of_natDegree_lt (p := p.coeff j)
      ((hx j).trans_lt (Nat.lt_succ_self _))
  unfold ofBox
  simp_rw [hinner]
  exact ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)

lemma coeff_product_bound (p q : ℤ[X][X]) (D E : ℕ) (hpY : p.natDegree ≤ E)
    (hpX : ∀ j, (p.coeff j).natDegree ≤ D) (H K : ℝ) (_hH : 0 ≤ H) (hK : 0 ≤ K)
    (hpH : ∀ j k, ‖(p.coeff j).coeff k‖ ≤ H)
    (hqK : ∀ j k, ‖(q.coeff j).coeff k‖ ≤ K) (j k : ℕ) :
    ‖((q * p).coeff j).coeff k‖ ≤ (E + 1 : ℝ) * (D + 1) * K * H := by
  have he : p = ∑ a : Fin (E + 1), ∑ b : Fin (D + 1),
      monomial a (monomial b ((p.coeff a).coeff b)) := by
    exact (eq_ofBox p D E hpY hpX).symm.trans
      (ofBox_eq_sum D E (fun jk => (p.coeff jk.1).coeff jk.2))
  conv_lhs => rw [he]
  simp only [Finset.mul_sum, finsetSum_coeff, double_coeff_mul_monomial]
  calc
    _ ≤ ∑ a : Fin (E + 1), ∑ b : Fin (D + 1),
        ‖(if a.val ≤ j ∧ b.val ≤ k then (q.coeff (j - a)).coeff (k - b) else 0) *
          (p.coeff a).coeff b‖ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _a : Fin (E + 1), ∑ _b : Fin (D + 1), K * H := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      rw [norm_mul]
      apply mul_le_mul _ (hpH _ _) (norm_nonneg _) hK
      split
      · exact hqK _ _
      · simpa using hK
    _ = _ := by simp; ring

lemma sum_product_bounds (n D E : ℕ) (p q : Fin n → ℤ[X][X])
    (hpY : ∀ i, (p i).natDegree ≤ E) (hpX : ∀ i j, ((p i).coeff j).natDegree ≤ D)
    (hqY : ∀ i, (q i).natDegree ≤ E) (hqX : ∀ i j, ((q i).coeff j).natDegree ≤ D)
    (H K : ℝ) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hpH : ∀ i j k, ‖((p i).coeff j).coeff k‖ ≤ H)
    (hqK : ∀ i j k, ‖((q i).coeff j).coeff k‖ ≤ K) :
    (∑ i, q i * p i).natDegree ≤ 2 * E ∧
    (∀ j, ((∑ i, q i * p i).coeff j).natDegree ≤ 2 * D) ∧
    ∀ j k, ‖(((∑ i, q i * p i).coeff j).coeff k)‖ ≤
      (n : ℝ) * (E + 1) * (D + 1) * K * H := by
  refine ⟨?_, ?_, ?_⟩
  · exact natDegree_sum_le_of_forall_le _ _ fun i _ =>
      natDegree_mul_le.trans (by have := hpY i; have := hqY i; omega)
  · apply inner_degree_sum
    intro i _
    simpa [two_mul] using inner_degree_mul (q i) (p i) D D (hqX i) (hpX i)
  · intro j k
    simp only [finsetSum_coeff]
    calc
      _ ≤ ∑ i : Fin n, ‖((q i * p i).coeff j).coeff k‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, (E + 1 : ℝ) * (D + 1) * K * H :=
        Finset.sum_le_sum fun i _ => coeff_product_bound (p i) (q i) D E
          (hpY i) (hpX i) H K hH hK (hpH i) (hqK i) j k
      _ = _ := by simp; ring


end TranscendenceTheory.BivariateSiegel

open TranscendenceTheory TranscendenceTheory.BivariateSiegel

theorem solution (θ ν : ℂ)
    (h_systems : ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in atTop, Nonempty (BoundedBivariateSystem θ ν a c N)) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ᶠ N : ℕ in atTop, ∃ P : ℤ[X][X],
        (P.natDegree : ℝ) ≤ A * N ∧
        (∀ j, ((P.coeff j).natDegree : ℝ) ≤ A * N) ∧
        (∀ j k, |((P.coeff j).coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
        P.eval₂ (Polynomial.aeval θ).toRingHom ν ≠ 0 ∧
        ‖P.eval₂ (Polynomial.aeval θ).toRingHom ν‖ ≤
          Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by
  obtain ⟨a, c, ha, hc, hs⟩ := h_systems
  refine ⟨4 * a, c, by positivity, hc, ?_⟩
  filter_upwards [hs] with N ⟨S⟩
  have haN : 0 ≤ a * N := mul_nonneg ha.le (Nat.cast_nonneg _)
  obtain ⟨p, hp, hpeq, hpy, hpx, hph⟩ := bivariate_siegel S.rows S.cols S.xDegree S.yDegree
    S.cols_pos S.dimension_gap S.equations (Real.exp (a * N))
    (Real.one_le_exp_iff.mpr haN) S.equations_yDegree S.equations_xDegree S.equations_height
  have hpH : ∀ i j k, ‖((p i).coeff j).coeff k‖ ≤ Real.exp (2 * a * N) := by
    intro i j k
    calc
      _ ≤ (S.cols : ℝ) * (S.yDegree + 1) * (S.xDegree + 1) * Real.exp (a * N) := hph i j k
      _ ≤ Real.exp (a * N) * Real.exp (a * N) :=
        mul_le_mul_of_nonneg_right S.size_le (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨r, hr, hrsmall⟩ := S.small_nonzero p hp hpy hpx hpH hpeq
  let P : ℤ[X][X] := ∑ i, S.testForms r i * p i
  obtain ⟨hy, hx, hH⟩ := sum_product_bounds S.cols S.xDegree S.yDegree p (S.testForms r)
    hpy hpx (S.testForms_yDegree r) (S.testForms_xDegree r)
    (Real.exp (2 * a * N)) (Real.exp (a * N)) (Real.exp_nonneg _) (Real.exp_nonneg _)
    hpH (S.testForms_height r)
  refine ⟨P, ?_, ?_, ?_, hr, hrsmall⟩
  · have hy' : (P.natDegree : ℝ) ≤ 2 * S.yDegree := by exact_mod_cast hy
    nlinarith [S.yDegree_le]
  · intro j
    have hx' : ((P.coeff j).natDegree : ℝ) ≤ 2 * S.xDegree := by exact_mod_cast hx j
    nlinarith [S.xDegree_le]
  · intro j k
    rw [← Int.norm_eq_abs]
    calc
      _ ≤ (S.cols : ℝ) * (S.yDegree + 1) * (S.xDegree + 1) *
          Real.exp (a * N) * Real.exp (2 * a * N) := hH j k
      _ ≤ Real.exp (a * N) * Real.exp (a * N) * Real.exp (2 * a * N) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right S.size_le (Real.exp_nonneg _)) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

