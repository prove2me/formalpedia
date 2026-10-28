-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P40.shorLaflamme_relation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:14:41.883788+00:00
-- url     : https://prove2.me/submissions/a5be4880-c4ec-4144-a715-8493e4f8f61d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

lemma x5sl_tr1 (a b : Pauli) :
    (∑ u : Bool, ∑ v : Bool, a.mat u v * b.mat v u) = if a = b then 2 else 0 := by
  cases a <;> cases b <;>
    simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.one_apply, Matrix.diagonal_apply] <;> norm_num

lemma x5sl_tr {p : ℕ} (e e' : ErrorLabel p) :
    (pauliOps e' * pauliOps e).trace = if e' = e then (2 : ℂ) ^ p else 0 := by
  have h1 : (pauliOps e' * pauliOps e).trace =
      ∑ y : Qubits p, ∑ z : Qubits p, ∏ q, ((e' q).mat (y q) (z q) * (e q).mat (z q) (y q)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pauliOps, PauliString.toMatrix,
      Matrix.of_apply, ZMod.val_zero, pow_zero, one_mul, Finset.prod_mul_distrib]
  have h2 : (∑ y : Qubits p, ∑ z : Qubits p,
      ∏ q, ((e' q).mat (y q) (z q) * (e q).mat (z q) (y q))) =
      ∏ q, ∑ u : Bool, ∑ v : Bool, (e' q).mat u v * (e q).mat v u := by
    rw [← Fintype.sum_prod_type']
    have : ∀ q : Fin p, (∑ u : Bool, ∑ v : Bool, (e' q).mat u v * (e q).mat v u) =
        ∑ w : Bool × Bool, (e' q).mat w.1 w.2 * (e q).mat w.2 w.1 := fun q =>
      (Fintype.sum_prod_type' (fun u v => (e' q).mat u v * (e q).mat v u)).symm
    simp_rw [this]
    rw [Fintype.prod_sum]
    exact Fintype.sum_equiv
      (Equiv.arrowProdEquivProdArrow (Fin p) (fun _ => Bool) (fun _ => Bool)).symm _ _
      (fun x => rfl)
  rw [h1, h2]
  simp_rw [x5sl_tr1]
  by_cases h : e' = e
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨q, hq⟩ : ∃ q, e' q ≠ e q := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)

lemma x5sl_w {p : ℕ} (e : ErrorLabel p) (d : ℕ) :
    slWeight d (pauliOps e) (pauliOps e) = if opsWeight e = d then (4 : ℂ) ^ p else 0 := by
  unfold slWeight
  simp_rw [x5sl_tr]
  by_cases h : opsWeight e = d
  · rw [Finset.sum_eq_single e]
    · simp [h, ← mul_pow]; norm_num
    · intro b _ hb; simp [hb]
    · intro he; simp [h] at he
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun b hb => ?_)
    have hbe : b ≠ e := by
      rintro rfl; simp at hb; exact h hb
    simp [hbe]

lemma x5sl_wle {p : ℕ} (e : ErrorLabel p) : opsWeight e ≤ p := by
  unfold opsWeight
  exact (Finset.card_le_univ _).trans (by simp)

lemma x5sl_inner {p : ℕ} (e : ErrorLabel p) (F : ℕ → ℂ) :
    (∑ d ∈ Finset.range (p + 1), slWeight d (pauliOps e) (pauliOps e) * F d) =
      (4 : ℂ) ^ p * F (opsWeight e) := by
  simp_rw [x5sl_w]
  rw [Finset.sum_eq_single (opsWeight e)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exfalso; exact h (Finset.mem_range.2 (Nat.lt_succ_of_le (x5sl_wle e)))

end

end QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Papers.Independent.Support50.P40
open scoped ComplexConjugate Matrix

theorem solution (p : ℕ) (C : Finset (ErrorLabel p))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    (∀ (e : ErrorLabel p) (d : ℕ),
      slWeight d (pauliOps e) (pauliOps e) =
        if opsWeight e = d then (4 : ℂ) ^ p else 0) ∧
    ((weightPolynomial f C : ℂ) = ((4 : ℂ) ^ p)⁻¹ *
      ∑ e ∈ C, ∑ d ∈ Finset.range (p + 1),
        slWeight d (pauliOps e) (pauliOps e) * (f : ℂ) ^ (p - d) * (noiseG f : ℂ) ^ d) ∧
    (0 < f →
      (weightPolynomial f C : ℂ) = (f : ℂ) ^ p / (4 : ℂ) ^ p *
        ∑ e ∈ C, slEnumerator ((noiseG f : ℂ) / (f : ℂ)) (pauliOps e) (pauliOps e) ∧
      (weightPolynomial f C : ℂ) = ((f : ℂ) / 4) ^ p *
        ∑ e ∈ C, slEnumerator (((1 - f) / (3 * f) : ℝ) : ℂ) (pauliOps e) (pauliOps e)) := by
  have h4 : (4 : ℂ) ^ p ≠ 0 := pow_ne_zero _ (by norm_num)
  have hW : (weightPolynomial f C : ℂ) =
      ∑ e ∈ C, (f : ℂ) ^ (p - opsWeight e) * (noiseG f : ℂ) ^ opsWeight e := by
    simp [weightPolynomial]
  have hE : ∀ z : ℂ, ∀ e : ErrorLabel p,
      slEnumerator z (pauliOps e) (pauliOps e) = (4 : ℂ) ^ p * z ^ opsWeight e := by
    intro z e
    exact x5sl_inner e (fun d => z ^ d)
  have hR : ∀ e : ErrorLabel p, f ≠ 0 →
      (f : ℂ) ^ p / (4 : ℂ) ^ p * ((4 : ℂ) ^ p * ((noiseG f : ℂ) / (f : ℂ)) ^ opsWeight e) =
        (f : ℂ) ^ (p - opsWeight e) * (noiseG f : ℂ) ^ opsWeight e := by
    intro e hf
    have hfc : (f : ℂ) ≠ 0 := by exact_mod_cast hf
    have hle := x5sl_wle e
    rw [← pow_sub_mul_pow (f : ℂ) hle, div_pow]
    field_simp
  refine ⟨x5sl_w, ?_, ?_⟩
  · rw [hW, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [show (∑ d ∈ Finset.range (p + 1), slWeight d (pauliOps e) (pauliOps e) *
        (f : ℂ) ^ (p - d) * (noiseG f : ℂ) ^ d) =
        ∑ d ∈ Finset.range (p + 1), slWeight d (pauliOps e) (pauliOps e) *
        ((f : ℂ) ^ (p - d) * (noiseG f : ℂ) ^ d) from
      Finset.sum_congr rfl (fun d _ => by ring)]
    rw [x5sl_inner e (fun d => (f : ℂ) ^ (p - d) * (noiseG f : ℂ) ^ d)]
    field_simp
  · intro hf
    have hf' : f ≠ 0 := hf.ne'
    have hz : ((((1 - f) / (3 * f) : ℝ)) : ℂ) = (noiseG f : ℂ) / (f : ℂ) := by
      simp only [noiseG]; push_cast; field_simp
    refine ⟨?_, ?_⟩
    · rw [hW, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [hE, hR e hf']
    · rw [hW, hz, div_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [hE, hR e hf']

