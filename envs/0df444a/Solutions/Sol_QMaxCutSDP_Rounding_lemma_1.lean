-- Prove2me | solution 1 for QMaxCutSDP.Rounding.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:23:06.450084+00:00
-- url     : https://prove2.me/submissions/e091274d-cc4e-4e46-a4fb-cd538ef4cc93

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory

namespace Aux_QMaxCutSDP_Rounding_lemma_1

open QMaxCutSDP.Rounding

lemma pauli0 : pauli 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli]

lemma pauli_sq (a : Fin 4) : pauli a * pauli a = 1 := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]


lemma ps_mul {n : ℕ} (s t : Fin n → Fin 4) (x y : BitString n) :
    (pauliString s * pauliString t) x y = ∏ q, (pauli (s q) * pauli (t q)) (x q) (y q) := by
  rw [Matrix.mul_apply]
  simp only [pauliString, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.prod_mul_distrib]

lemma ps_smul_of {n : ℕ} (s t u v : Fin n → Fin 4) (c : Fin n → ℂ)
    (h : ∀ q, pauli (s q) * pauli (t q) = c q • (pauli (u q) * pauli (v q))) :
    pauliString s * pauliString t = (∏ q, c q) • (pauliString u * pauliString v) := by
  ext x y
  rw [Matrix.smul_apply, ps_mul, ps_mul, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [h q, Matrix.smul_apply, smul_eq_mul]

def zs (n : ℕ) : Fin n → Fin 4 := fun _ => 0

def e1 {n : ℕ} (i : Fin n) (a : Fin 4) : Fin n → Fin 4 := fun t => if t = i then a else 0

lemma zs_apply {n : ℕ} (q : Fin n) : zs n q = 0 := rfl

lemma e1_self {n : ℕ} (i : Fin n) (a : Fin 4) : e1 i a i = a := if_pos rfl

lemma e1_ne {n : ℕ} {i q : Fin n} (a : Fin 4) (h : q ≠ i) : e1 i a q = 0 := if_neg h

lemma pp_mem {n : ℕ} {i j q : Fin n} (a : Fin 4) (h : q = i ∨ q = j) :
    pauliPairString a i j q = a := if_pos h

lemma pp_ne {n : ℕ} {i j q : Fin n} (a : Fin 4) (h : q ≠ i) (h' : q ≠ j) :
    pauliPairString a i j q = 0 := if_neg (not_or.mpr ⟨h, h'⟩)


lemma weight_le {n : ℕ} (s : Fin n → Fin 4) (i j : Fin n) (h : ∀ t, s t ≠ 0 → t = i ∨ t = j) :
    weight s ≤ 2 := by
  unfold weight
  calc (Finset.univ.filter fun t => s t ≠ 0).card ≤ ({i, j} : Finset (Fin n)).card :=
        Finset.card_le_card (fun t ht => by
          rw [Finset.mem_filter] at ht
          rw [Finset.mem_insert, Finset.mem_singleton]
          exact h t ht.2)
    _ ≤ 2 := Finset.card_le_two

lemma weight_zs (n : ℕ) : weight (zs n) ≤ 2 := by
  unfold weight
  have : (Finset.univ.filter fun t => zs n t ≠ 0) = ∅ := by
    ext t
    simp [zs]
  rw [this, Finset.card_empty]
  norm_num


lemma pauli_herm (a : Fin 4) : (pauli a)ᴴ = pauli a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.conjTranspose_apply]

lemma ps_herm {n : ℕ} (s : Fin n → Fin 4) : (pauliString s)ᴴ = pauliString s := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  simp only [pauliString]
  rw [star_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  have h := congrFun (congrFun (pauli_herm (s q)) (x q)) (y q)
  rw [Matrix.conjTranspose_apply] at h
  exact h

lemma ps_zero {n : ℕ} : pauliString (fun _ : Fin n => (0 : Fin 4)) = 1 := by
  ext x y
  simp only [pauliString, pauli0, Matrix.one_apply]
  rw [Fintype.prod_boole]
  by_cases hxy : x = y
  · rw [if_pos (show ∀ q, x q = y q from fun q => by rw [hxy]), if_pos hxy]
  · rw [if_neg (show ¬ ∀ q, x q = y q from fun h => hxy (funext h)), if_neg hxy]

lemma ps_sq {n : ℕ} (s : Fin n → Fin 4) : pauliString s * pauliString s = 1 := by
  have key := ps_smul_of s s (fun _ => 0) (fun _ => 0) (fun _ => (1 : ℂ)) (by
    intro q
    try dsimp only
    rw [pauli_sq, pauli0, one_smul, one_mul])
  rw [Finset.prod_const_one, one_smul, ps_zero, one_mul] at key
  exact key

lemma inner_ps {n : ℕ} (φ : State n) (s t : Fin n → Fin 4) :
    star φ ⬝ᵥ ((pauliString s * pauliString t) *ᵥ φ) =
      star (pauliString s *ᵥ φ) ⬝ᵥ (pauliString t *ᵥ φ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, ps_herm]

lemma re_symm {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    (star u ⬝ᵥ v).re = (star v ⬝ᵥ u).re := by
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.mul_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.conj_re, Complex.conj_im]
  ring

end Aux_QMaxCutSDP_Rounding_lemma_1

open Aux_QMaxCutSDP_Rounding_lemma_1 in
open QMaxCutSDP.Rounding in
theorem solution {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → Fin n → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (φ : State n) (hφ : star φ ⬝ᵥ φ = 1) :
    ∃ M : Matrix (PIndex n k) (PIndex n k) ℝ,
      IsLasserreFeasible n k M ∧ energy G w φ ≤ lasserreObj G w hk M := by
  haveI : Fintype (PIndex n k) :=
    (inferInstance : Fintype {s : Fin n → Fin 4 // weight s ≤ k})
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (PIndex n k) (PIndex n k) ℝ,
      M = Matrix.of fun s t => (star φ ⬝ᵥ ((pauliString s.1 * pauliString t.1) *ᵥ φ)).re :=
    ⟨_, rfl⟩
  have hM : ∀ s t : PIndex n k,
      M s t = (star φ ⬝ᵥ ((pauliString s.1 * pauliString t.1) *ᵥ φ)).re := by
    intro s t
    rw [hMdef, Matrix.of_apply]
  have h0 : weight (fun _ : Fin n => (0 : Fin 4)) ≤ k := (weight_zs n).trans hk
  have hLE : ∀ (s : Fin n → Fin 4) (hs : weight s ≤ k),
      lasserreEntry M s (fun _ => 0) = (star φ ⬝ᵥ (pauliString s *ᵥ φ)).re := by
    intro s hs
    unfold lasserreEntry
    rw [dif_pos hs, dif_pos h0]
    refine (hM ⟨s, hs⟩ ⟨fun _ => 0, h0⟩).trans ?_
    show (star φ ⬝ᵥ ((pauliString s * pauliString (fun _ : Fin n => (0 : Fin 4))) *ᵥ φ)).re = _
    rw [ps_zero, mul_one]
  have hL0 : lasserreEntry M (fun _ => 0) (fun _ => 0) = 1 := by
    rw [hLE _ h0, ps_zero, Matrix.one_mulVec, hφ, Complex.one_re]
  refine ⟨M, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- positive semidefinite: a real Gram matrix
    let A : Matrix (BitString n × Fin 2) (PIndex n k) ℝ := Matrix.of fun p s =>
      ![((pauliString s.1 *ᵥ φ) p.1).re, ((pauliString s.1 *ᵥ φ) p.1).im] p.2
    have hMA : M = Aᴴ * A := by
      ext s t
      rw [hM, Matrix.mul_apply, Fintype.sum_prod_type, inner_ps]
      simp only [dotProduct, Complex.re_sum, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        star_trivial, A, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Pi.star_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    rw [hMA]
    exact Matrix.posSemidef_conjTranspose_mul_self A
  · intro s
    rw [hM, ps_sq, Matrix.one_mulVec, hφ, Complex.one_re]
  · intro s t h
    rw [hM]
    have h' : pauliString t.1 * pauliString s.1 = -(pauliString s.1 * pauliString t.1) := by
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
      exact h
    have hneg : (star φ ⬝ᵥ ((pauliString t.1 * pauliString s.1) *ᵥ φ)).re =
        -(star φ ⬝ᵥ ((pauliString s.1 * pauliString t.1) *ᵥ φ)).re := by
      rw [h', Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
    rw [inner_ps φ t.1 s.1, ← re_symm (pauliString s.1 *ᵥ φ) (pauliString t.1 *ᵥ φ),
      ← inner_ps φ s.1 t.1] at hneg
    linarith
  · intro s t u v h
    rw [hM, hM, h]
  · intro s t u v h
    rw [hM, hM, h, Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
  · -- energy equals the Lasserre objective
    unfold energy lasserreObj hamiltonian
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    apply le_of_eq
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : i < j ∧ G.Adj i j
    · rw [if_pos hc, if_pos hc]
      have wpp : ∀ a : Fin 4, weight (pauliPairString a i j) ≤ k := fun a =>
        (weight_le _ i j (fun t ht => by by_contra h; exact ht (if_neg h))).trans hk
      have h14 : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
      unfold hEdge
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, h14, Complex.re_ofReal_mul,
        Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_sub, dotProduct_sub, hφ, Complex.sub_re, Complex.sub_re,
        Complex.sub_re, Complex.one_re, hL0, hLE _ (wpp 1), hLE _ (wpp 2), hLE _ (wpp 3)]
      ring
    · rw [if_neg hc, if_neg hc, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
