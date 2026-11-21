-- Prove2me | solution 1 for QMaxCutSDP.Rounding.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:11:06.590472+00:00
-- url     : https://prove2.me/submissions/4a45ce93-eb05-4df2-a0be-768ddcd171c2

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory

namespace Aux_QMaxCutSDP_Rounding_lemma_2

open QMaxCutSDP.Rounding

/-! ### One-qubit Pauli algebra -/

lemma pauli0 : pauli 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli]

lemma pauli_sq (a : Fin 4) : pauli a * pauli a = 1 := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauli_anti (a b : Fin 3) (hab : a ≠ b) :
    pauli a.succ * pauli b.succ = (-1 : ℂ) • (pauli b.succ * pauli a.succ) := by
  fin_cases a <;> fin_cases b <;> simp at hab <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauli_eps (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    pauli a.succ * pauli b.succ =
      (if (b.val + 3 - a.val) % 3 = 1 then Complex.I else -Complex.I) • (pauli c.succ * pauli 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at hab hbc hac <;> ext i j <;>
    fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]

lemma eps_sq (p : Prop) [Decidable p] :
    (if p then Complex.I else -Complex.I) * (if p then Complex.I else -Complex.I) = -1 := by
  split_ifs <;> simp

/-! ### Pauli strings -/

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

lemma c3 {n : ℕ} (i : Fin n) (a b : Fin 3) (hab : a ≠ b) :
    pauliString (e1 i a.succ) * pauliString (e1 i b.succ) +
      pauliString (e1 i b.succ) * pauliString (e1 i a.succ) = 0 := by
  have key := ps_smul_of (e1 i a.succ) (e1 i b.succ) (e1 i b.succ) (e1 i a.succ)
    (fun q => if q = i then (-1 : ℂ) else 1) (by
      intro q
      try dsimp only
      by_cases hq : q = i
      · rw [if_pos hq, hq, e1_self, e1_self]
        exact pauli_anti a b hab
      · rw [if_neg hq, e1_ne _ hq, e1_ne _ hq, pauli0, one_smul])
  have hp : ∏ q : Fin n, (if q = i then (-1 : ℂ) else 1) = -1 := by simp
  rw [hp, neg_one_smul] at key
  rw [key, neg_add_cancel]

lemma c5 {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a : Fin 3) :
    pauliString (e1 i a.succ) * pauliString (e1 j a.succ) =
      pauliString (pauliPairString a.succ i j) * pauliString (zs n) := by
  have key := ps_smul_of (e1 i a.succ) (e1 j a.succ) (pauliPairString a.succ i j) (zs n)
    (fun _ => (1 : ℂ)) (by
      intro q
      try dsimp only
      by_cases hqi : q = i
      · rw [hqi, e1_self, e1_ne _ hij, pp_mem _ (Or.inl rfl), zs_apply, pauli0, one_smul]
      · by_cases hqj : q = j
        · rw [hqj, e1_ne _ (Ne.symm hij), e1_self, pp_mem _ (Or.inr rfl), zs_apply, pauli0,
            one_smul, one_mul, mul_one]
        · rw [e1_ne _ hqi, e1_ne _ hqj, pp_ne _ hqi hqj, zs_apply, pauli0, one_smul])
  rw [Finset.prod_const_one, one_smul] at key
  exact key

lemma c6 {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : Fin 3) :
    pauliString (pauliPairString a.succ i j) * pauliString (pauliPairString a.succ j k) =
      pauliString (pauliPairString a.succ i k) * pauliString (zs n) := by
  have key := ps_smul_of (pauliPairString a.succ i j) (pauliPairString a.succ j k)
    (pauliPairString a.succ i k) (zs n) (fun _ => (1 : ℂ)) (by
      intro q
      try dsimp only
      by_cases hqi : q = i
      · rw [hqi, pp_mem _ (Or.inl rfl), pp_ne _ hij hik, pp_mem _ (Or.inl rfl), zs_apply,
          pauli0, one_smul]
      · by_cases hqj : q = j
        · rw [hqj, pp_mem _ (Or.inr rfl), pp_mem _ (Or.inl rfl), pp_ne _ (Ne.symm hij) hjk,
            zs_apply, pauli_sq, pauli0, one_smul, mul_one]
        · by_cases hqk : q = k
          · rw [hqk, pp_ne _ (Ne.symm hik) (Ne.symm hjk), pp_mem _ (Or.inr rfl),
              pp_mem _ (Or.inr rfl), zs_apply, pauli0, one_smul, one_mul, mul_one]
          · rw [pp_ne _ hqi hqj, pp_ne _ hqj hqk, pp_ne _ hqi hqk, zs_apply, pauli0, one_smul])
  rw [Finset.prod_const_one, one_smul] at key
  exact key

lemma c7 {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : Fin 3)
    (hab : a ≠ b) :
    pauliString (pauliPairString a.succ i j) * pauliString (pauliPairString b.succ j k) +
      pauliString (pauliPairString b.succ j k) * pauliString (pauliPairString a.succ i j) = 0 := by
  have key := ps_smul_of (pauliPairString a.succ i j) (pauliPairString b.succ j k)
    (pauliPairString b.succ j k) (pauliPairString a.succ i j)
    (fun q => if q = j then (-1 : ℂ) else 1) (by
      intro q
      try dsimp only
      by_cases hqj : q = j
      · rw [if_pos hqj, hqj, pp_mem _ (Or.inr rfl), pp_mem _ (Or.inl rfl)]
        exact pauli_anti a b hab
      · rw [if_neg hqj]
        by_cases hqi : q = i
        · rw [hqi, pp_mem _ (Or.inl rfl), pp_ne _ hij hik, pauli0, one_smul, one_mul, mul_one]
        · by_cases hqk : q = k
          · rw [hqk, pp_ne _ (Ne.symm hik) (Ne.symm hjk), pp_mem _ (Or.inr rfl), pauli0,
              one_smul, one_mul, mul_one]
          · rw [pp_ne _ hqi hqj, pp_ne _ hqj hqk, pauli0, one_smul])
  have hp : ∏ q : Fin n, (if q = j then (-1 : ℂ) else 1) = -1 := by simp
  rw [hp, neg_one_smul] at key
  rw [key, neg_add_cancel]

lemma c8 {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) :
    pauliString (pauliPairString a.succ i j) * pauliString (pauliPairString b.succ i j) =
      -(pauliString (pauliPairString c.succ i j) * pauliString (zs n)) := by
  have key := ps_smul_of (pauliPairString a.succ i j) (pauliPairString b.succ i j)
    (pauliPairString c.succ i j) (zs n)
    (fun q => if q = i ∨ q = j then (if (b.val + 3 - a.val) % 3 = 1 then Complex.I else -Complex.I) else 1) (by
      intro q
      try dsimp only
      by_cases hq : q = i ∨ q = j
      · rw [if_pos hq, pp_mem _ hq, pp_mem _ hq, pp_mem _ hq, zs_apply]
        exact pauli_eps a b c hab hbc hac
      · rw [if_neg hq, pp_ne _ (fun h => hq (Or.inl h)) (fun h => hq (Or.inr h)),
          pp_ne _ (fun h => hq (Or.inl h)) (fun h => hq (Or.inr h)),
          pp_ne _ (fun h => hq (Or.inl h)) (fun h => hq (Or.inr h)), zs_apply, pauli0,
          one_smul])
  have hp : ∏ q : Fin n, (if q = i ∨ q = j then (if (b.val + 3 - a.val) % 3 = 1 then Complex.I else -Complex.I)
      else 1) = -1 := by
    rw [Fintype.prod_eq_mul i j hij, if_pos (Or.inl rfl), if_pos (Or.inr rfl), eps_sq]
    intro x hx
    exact if_neg (not_or.mpr hx)
  rw [hp, neg_one_smul] at key
  exact key

/-! ### Elements of the index set -/

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

def I0 (n : ℕ) : PIndex n 2 := ⟨zs n, weight_zs n⟩

def E1 {n : ℕ} (i : Fin n) (a : Fin 4) : PIndex n 2 :=
  ⟨e1 i a, weight_le _ i i (fun t ht => Or.inl (by by_contra h; exact ht (if_neg h)))⟩

def E2 {n : ℕ} (i j : Fin n) (a : Fin 4) : PIndex n 2 :=
  ⟨pauliPairString a i j, weight_le _ i j (fun t ht => by by_contra h; exact ht (if_neg h))⟩

lemma E2_comm {n : ℕ} (i j : Fin n) (a : Fin 4) : E2 i j a = E2 j i a := by
  apply Subtype.ext
  show pauliPairString a i j = pauliPairString a j i
  funext t
  by_cases h : t = i ∨ t = j
  · rw [pp_mem _ h, pp_mem _ h.symm]
  · rw [pp_ne _ (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h')),
      pp_ne _ (fun h' => h (Or.inr h')) (fun h' => h (Or.inl h'))]

/-! ### Gram vectors of a PSD matrix -/

lemma gram {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : M.PosSemidef) :
    ∃ (N : ℕ) (col : ι → Fin N → ℝ), ∀ s t, col s ⬝ᵥ col t = M s t := by
  obtain ⟨U, hU⟩ : ∃ U : Matrix ι ι ℝ, U = (hM.1.eigenvectorUnitary : Matrix ι ι ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ι → ℝ, d = RCLike.ofReal ∘ hM.1.eigenvalues := ⟨_, rfl⟩
  have hspec : M = U * Matrix.diagonal d * star U := by
    rw [hU, hd]
    exact hM.1.spectral_theorem
  have hd0 : ∀ r, 0 ≤ d r := by
    intro r
    rw [hd]
    exact hM.eigenvalues_nonneg r
  have hent : ∀ s t, M s t = ∑ r, U s r * (d r * U t r) := by
    intro s t
    rw [congrFun (congrFun hspec s) t, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Matrix.mul_diagonal, Matrix.star_apply, star_trivial]
    ring
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun s r => Real.sqrt (d (e.symm r)) * U s (e.symm r), ?_⟩
  intro s t
  rw [hent s t]
  simp only [dotProduct]
  refine (Equiv.sum_comp e.symm
    (fun r => Real.sqrt (d r) * U s r * (Real.sqrt (d r) * U t r))).trans ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  have h1 : Real.sqrt (d r) * U s r * (Real.sqrt (d r) * U t r) =
      (Real.sqrt (d r) * Real.sqrt (d r)) * U s r * U t r := by ring
  rw [h1, Real.mul_self_sqrt (hd0 r)]
  ring

end Aux_QMaxCutSDP_Rounding_lemma_2

open Aux_QMaxCutSDP_Rounding_lemma_2 in
open QMaxCutSDP.Rounding in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → Fin n → ℝ) (M : Matrix (PIndex n 2) (PIndex n 2) ℝ)
    (hM : IsLasserreFeasible n 2 M) :
    ∃ (N : ℕ) (v : SDPVec n N),
      IsSFeasible v ∧ lasserreObj G w (by decide) M ≤ sObj G w v := by
  haveI : Fintype (PIndex n 2) :=
    (inferInstance : Fintype {s : Fin n → Fin 4 // weight s ≤ 2})
  haveI : DecidableEq (PIndex n 2) :=
    (inferInstance : DecidableEq {s : Fin n → Fin 4 // weight s ≤ 2})
  obtain ⟨hpsd, hdiag, hanti, hprod, hneg⟩ := hM
  obtain ⟨N, col, hgram⟩ := gram M hpsd
  refine ⟨N, ⟨col (I0 n), fun i a => col (E1 i a.succ), fun i j a => col (E2 i j a.succ)⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show col (I0 n) ⬝ᵥ col (I0 n) = 1
    rw [hgram, hdiag]
  · intro i a
    show col (E1 i a.succ) ⬝ᵥ col (E1 i a.succ) = 1
    rw [hgram, hdiag]
  · intro i a b hab
    show col (E1 i a.succ) ⬝ᵥ col (E1 i b.succ) = 0
    rw [hgram]
    exact hanti _ _ (c3 i a b hab)
  · intro i j a _
    show col (E2 i j a.succ) ⬝ᵥ col (E2 i j a.succ) = 1
    rw [hgram, hdiag]
  · intro i j a hij
    show col (E1 i a.succ) ⬝ᵥ col (E1 j a.succ) = col (E2 i j a.succ) ⬝ᵥ col (I0 n)
    rw [hgram, hgram]
    exact hprod _ _ _ _ (c5 i j hij a)
  · intro i j k a hij hjk hik
    show col (E2 i j a.succ) ⬝ᵥ col (E2 j k a.succ) = col (E2 i k a.succ) ⬝ᵥ col (I0 n)
    rw [hgram, hgram]
    exact hprod _ _ _ _ (c6 i j k hij hjk hik a)
  · intro i j k a b hij hjk hik hab
    show col (E2 i j a.succ) ⬝ᵥ col (E2 j k b.succ) = 0
    rw [hgram]
    exact hanti _ _ (c7 i j k hij hjk hik a b hab)
  · intro i j a b c hij hab hbc hac
    show col (E2 i j a.succ) ⬝ᵥ col (E2 i j b.succ) = -(col (E2 i j c.succ) ⬝ᵥ col (I0 n))
    rw [hgram, hgram]
    exact hneg _ _ _ _ (c8 i j hij a b c hab hbc hac)
  · intro i j a _
    show col (E2 i j a.succ) = col (E2 j i a.succ)
    rw [E2_comm]
  · unfold lasserreObj sObj
    apply le_of_eq
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : i < j ∧ G.Adj i j
    · rw [if_pos hc, if_pos hc]
      have h0 : weight (fun _ : Fin n => (0 : Fin 4)) ≤ 2 := weight_zs n
      have hL0 : lasserreEntry M (fun _ => 0) (fun _ => 0) = M (I0 n) (I0 n) := by
        unfold lasserreEntry
        rw [dif_pos h0, dif_pos h0]
        rfl
      have hL2 : ∀ a : Fin 4,
          lasserreEntry M (pauliPairString a i j) (fun _ => 0) = M (E2 i j a) (I0 n) := by
        intro a
        unfold lasserreEntry
        rw [dif_pos (show weight (pauliPairString a i j) ≤ 2 from (E2 i j a).2), dif_pos h0]
        rfl
      have hs1 : (Fin.succ (0 : Fin 3) : Fin 4) = 1 := rfl
      have hs2 : (Fin.succ (1 : Fin 3) : Fin 4) = 2 := rfl
      have hs3 : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := rfl
      show 1 / 4 * w i j * (lasserreEntry M (fun _ => 0) (fun _ => 0) -
          lasserreEntry M (pauliPairString 1 i j) (fun _ => 0) -
          lasserreEntry M (pauliPairString 2 i j) (fun _ => 0) -
          lasserreEntry M (pauliPairString 3 i j) (fun _ => 0)) =
        1 / 4 * w i j * ((col (I0 n) - ∑ a : Fin 3, col (E2 i j a.succ)) ⬝ᵥ col (I0 n))
      rw [hL0, hL2 1, hL2 2, hL2 3, sub_dotProduct, _root_.sum_dotProduct, Fin.sum_univ_three,
        hgram, hgram, hgram, hgram, hs1, hs2, hs3]
      ring
    · rw [if_neg hc, if_neg hc]
