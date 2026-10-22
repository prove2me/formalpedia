-- Prove2me | solution 1 for TuranMatching.Clique.case_2_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:01:00.477086+00:00
-- url     : https://prove2.me/submissions/e9a2d354-6083-411f-8c2f-fcb7863f2810

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

set_option autoImplicit false
open Finset SimpleGraph
open TuranMatching.Clique

theorem tmk_two_choose (m : ℕ) : 2 * m.choose 2 + m = m * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

theorem tmk_formula (k' q r : ℕ) (hr : r < k' + 1) :
    2 * turanNum ((k' + 1) * q + r) (k' + 1) + r = k' * q * (q * (k' + 1) + 2 * r) + r * r := by
  unfold turanNum
  rw [SimpleGraph.card_edgeFinset_turanGraph]
  have hmod : ((k' + 1) * q + r) % (k' + 1) = r := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hr
  rw [hmod]
  have h1 : ((k' + 1) * q + r) ^ 2 - r ^ 2 = (k' + 1) * (q * (q * (k' + 1) + 2 * r)) := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [h1]
  have h2 : (k' + 1) * (q * (q * (k' + 1) + 2 * r)) * (k' + 1 - 1) / (2 * (k' + 1)) =
      (q * (q * (k' + 1) + 2 * r) * k') / 2 := by
    have : (k' + 1) * (q * (q * (k' + 1) + 2 * r)) * (k' + 1 - 1) =
        (q * (q * (k' + 1) + 2 * r) * k') * (k' + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [this, Nat.mul_div_mul_right _ _ (by omega : 0 < k' + 1)]
  rw [h2]
  have heven : Even (q * (q * (k' + 1) + 2 * r) * k') := by
    have : q * (q * (k' + 1) + 2 * r) * k' = q * q * (k' * (k' + 1)) + 2 * (q * r * k') := by ring
    rw [this]
    exact Even.add (Even.mul_left (Nat.even_mul_succ_self k') _) (even_two_mul _)
  have h3 := Nat.two_mul_div_two_of_even heven
  have h4 := tmk_two_choose r
  have h5 : q * (q * (k' + 1) + 2 * r) * k' = k' * q * (q * (k' + 1) + 2 * r) := by ring
  rw [h5] at h3 ⊢
  nlinarith

theorem tmk_incr (k' N : ℕ) :
    (turanNum (N + 1) (k' + 1) : ℤ) - turanNum N (k' + 1) = (N : ℤ) - ((N / (k' + 1) : ℕ) : ℤ) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < k' + 1 ∧ N = (k' + 1) * q + r :=
    ⟨N / (k' + 1), N % (k' + 1), Nat.mod_lt _ (by omega), (Nat.div_add_mod _ _).symm⟩
  have hq : ((k' + 1) * q + r) / (k' + 1) = q := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, add_zero]
  rw [hq]
  have e1 := tmk_formula k' q r hr
  have e1' : (2 * (turanNum ((k' + 1) * q + r) (k' + 1) : ℤ) + r) =
      k' * q * (q * (k' + 1) + 2 * r) + r * r := by exact_mod_cast e1
  rcases Nat.lt_or_ge r k' with h | h
  · have e2 := tmk_formula k' q (r + 1) (by omega)
    have e2' : (2 * (turanNum ((k' + 1) * q + (r + 1)) (k' + 1) : ℤ) + (r + 1 : ℕ)) =
        k' * q * (q * (k' + 1) + 2 * (r + 1 : ℕ)) + (r + 1 : ℕ) * (r + 1 : ℕ) := by exact_mod_cast e2
    have : (k' + 1) * q + r + 1 = (k' + 1) * q + (r + 1) := by ring
    rw [this]
    push_cast at e2' ⊢
    nlinarith
  · have hrk : r = k' := by omega
    subst hrk
    have e2 := tmk_formula r (q + 1) 0 (by omega)
    have e2' : (2 * (turanNum ((r + 1) * (q + 1) + 0) (r + 1) : ℤ) + (0 : ℕ)) =
        r * (q + 1 : ℕ) * ((q + 1 : ℕ) * (r + 1) + 2 * (0 : ℕ)) + (0 : ℕ) * (0 : ℕ) := by exact_mod_cast e2
    have : (r + 1) * q + r + 1 = (r + 1) * (q + 1) + 0 := by ring
    rw [this]
    push_cast at e2' ⊢
    nlinarith

theorem tmk_div_le (k' N : ℕ) : N / (k' + 1) ≤ (N + 1) / (k' + 1) ∧ (N + 1) / (k' + 1) ≤ N / (k' + 1) + 1 := by
  constructor
  · exact Nat.div_le_div_right (by omega)
  · have : (N + 1) / (k' + 1) ≤ (N + (k' + 1)) / (k' + 1) := Nat.div_le_div_right (by omega)
    rw [Nat.add_div_right _ (by omega)] at this
    exact this

theorem tmk_turan_increment (k : ℕ) (hk : 1 ≤ k) (N : ℕ) :
    ((turanNum (N + 1) k : ℤ) - turanNum N k = (N : ℤ) - (N / k : ℕ)) ∧
    ((turanNum (N + 1) k : ℤ) - turanNum N k ≤ (turanNum (N + 2) k : ℤ) - turanNum (N + 1) k) ∧
    ((turanNum (N + 2) k : ℤ) - turanNum (N + 1) k ≤ (turanNum (N + 1) k : ℤ) - turanNum N k + 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have e0 := tmk_incr k' N
  have e1 := tmk_incr k' (N + 1)
  obtain ⟨d1, d2⟩ := tmk_div_le k' N
  have d1' : ((N / (k' + 1) : ℕ) : ℤ) ≤ (((N + 1) / (k' + 1) : ℕ) : ℤ) := by exact_mod_cast d1
  have d2' : (((N + 1) / (k' + 1) : ℕ) : ℤ) ≤ ((N / (k' + 1) : ℕ) : ℤ) + 1 := by exact_mod_cast d2
  have h3 : N + 1 + 1 = N + 2 := rfl
  rw [h3] at e1
  refine ⟨e0, ?_, ?_⟩
  · rw [Nat.cast_succ] at e1; linarith
  · rw [Nat.cast_succ] at e1; linarith

theorem tmk_f_discrete_convex (n k s b : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n)
    (hb : b + 2 ≤ s - s / (k - 1)) :
    fCase4 n k s (b + 1) - fCase4 n k s b < fCase4 n k s (b + 2) - fCase4 n k s (b + 1) := by
  have hbs : b + 2 ≤ s := le_trans hb (Nat.sub_le _ _)
  obtain ⟨N, hN⟩ : ∃ N, 2 * s = b + 2 + N := ⟨2 * s - (b + 2), by omega⟩
  have e1 : 2 * s - b + 1 = N + 3 := by omega
  have e2 : 2 * s - (b + 1) + 1 = N + 2 := by omega
  have e3 : 2 * s - (b + 2) + 1 = N + 1 := by omega
  have hmono := (tmk_turan_increment k (by omega) (N + 1)).2.1
  have hN' : (2 * s : ℤ) = b + 2 + N := by exact_mod_cast hN
  unfold fCase4
  rw [e1, e2, e3]
  have h2 : N + 1 + 2 = N + 3 := rfl
  have h3 : N + 1 + 1 = N + 2 := rfl
  rw [h2, h3] at hmono
  push_cast
  nlinarith

theorem tmk_degsum (n k s : ℕ) :
    ∑ v : Fin n, #{w : Fin n | (bigGraph n k s).Adj v w} = 2 * gNum n k s := by
  unfold gNum
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  apply Finset.sum_congr rfl
  intro v _
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]

theorem tmk_bigClass_lt (k s : ℕ) (hk : 2 ≤ k) {n : ℕ} (v : Fin n) (hv : (v : ℕ) < s) :
    bigClass k s v < k - 1 := by
  unfold bigClass
  rw [if_pos hv]
  exact Nat.mod_lt _ (by omega)

theorem tmk_adj_last (n k s : ℕ) (hk : 2 ≤ k) (hsn : s ≤ n) (v : Fin n) :
    (bigGraph (n + 1) k s).Adj v.castSucc (Fin.last n) ↔ (v : ℕ) < s := by
  show bigClass k s v.castSucc ≠ bigClass k s (Fin.last n) ↔ _
  have hl : bigClass k s (Fin.last n) = k - 1 := by
    unfold bigClass
    rw [if_neg (by simp; omega)]
  rw [hl]
  by_cases hv : (v : ℕ) < s
  · have := tmk_bigClass_lt k s hk (v.castSucc) (by simpa using hv)
    simp only [hv, iff_true]; omega
  · have : bigClass k s v.castSucc = k - 1 := by
      unfold bigClass
      rw [if_neg (by simpa using hv)]
    simp [this, hv]

theorem tmk_card_lt (n s : ℕ) (hsn : s ≤ n) : #{v : Fin n | (v : ℕ) < s} = s := by
  have : (Finset.univ.filter (fun v : Fin n => (v : ℕ) < s)) =
      (Finset.univ : Finset (Fin s)).map (Fin.castLEEmb hsn) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.coe_castLEEmb]
    constructor
    · intro hv; exact ⟨⟨v, hv⟩, rfl⟩
    · rintro ⟨a, rfl⟩; exact a.2
  rw [this, Finset.card_map]; simp

theorem tmk_Dg_step (n k s : ℕ) (hk : 2 ≤ k) (hsn : s ≤ n) :
    ∑ v : Fin (n + 1), #{w : Fin (n + 1) | (bigGraph (n + 1) k s).Adj v w} =
      ∑ v : Fin n, #{w : Fin n | (bigGraph n k s).Adj v w} + 2 * s := by
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ v : Fin n, #{w : Fin (n + 1) | (bigGraph (n + 1) k s).Adj v.castSucc w} =
      #{w : Fin n | (bigGraph n k s).Adj v w} + (if (v : ℕ) < s then 1 else 0) := by
    intro v
    rw [Finset.card_filter, Fin.sum_univ_castSucc, Finset.card_filter]
    have e2 : (if (bigGraph (n + 1) k s).Adj v.castSucc (Fin.last n) then 1 else 0) =
        (if (v : ℕ) < s then 1 else 0) := by
      simp only [tmk_adj_last n k s hk hsn v]
    rw [e2]
    rfl
  simp only [h1]
  rw [Finset.sum_add_distrib]
  have h2 : ∑ v : Fin n, (if (v : ℕ) < s then 1 else 0) = s := by
    rw [← Finset.card_filter]; exact tmk_card_lt n s hsn
  have h3 : #{w : Fin (n + 1) | (bigGraph (n + 1) k s).Adj (Fin.last n) w} = s := by
    rw [Finset.card_filter, Fin.sum_univ_castSucc]
    have : ∀ w : Fin n, ((bigGraph (n + 1) k s).Adj (Fin.last n) w.castSucc) ↔ (w : ℕ) < s := by
      intro w
      rw [SimpleGraph.adj_comm, tmk_adj_last n k s hk hsn]
    simp only [this]
    simp [h2]
  rw [h2, h3]
  ring

theorem tmk_gNum_s (s k : ℕ) : gNum s k s = turanNum s (k - 1) := by
  have h : bigGraph s k s = turanGraph s (k - 1) := by
    ext v w
    simp only [bigGraph, turanGraph, bigClass, v.2, w.2, if_true]
  have key : ∀ (G H : SimpleGraph (Fin s)) [DecidableRel G.Adj] [DecidableRel H.Adj], G = H →
      #G.edgeFinset = #H.edgeFinset := by
    intro G H i1 i2 h
    subst h
    have : i1 = i2 := Subsingleton.elim _ _
    subst this
    rfl
  exact key _ _ h

theorem tmk_gNum (n k s : ℕ) (hk : 2 ≤ k) (hsn : s ≤ n) :
    gNum n k s = turanNum s (k - 1) + (n - s) * s := by
  obtain ⟨d, rfl⟩ : ∃ d, n = s + d := ⟨n - s, by omega⟩
  induction d with
  | zero => simp [tmk_gNum_s]
  | succ d ih =>
    have h1 := tmk_degsum (s + d + 1) k s
    have h2 := tmk_degsum (s + d) k s
    have h3 := tmk_Dg_step (s + d) k s hk (by omega)
    have := ih (by omega)
    rw [h3, h2] at h1
    rw [show s + (d + 1) = s + d + 1 by ring]
    have e : s + d + 1 - s = (s + d - s) + 1 := by omega
    rw [e]
    nlinarith

theorem tmk_case_2 (n k s : ℕ) (hk : 2 ≤ k) (hn : s + s / (k - 1) ≤ n) :
    turanNum (s + s / (k - 1)) k + (n - s - s / (k - 1)) * s = gNum n k s := by
  rw [tmk_gNum n k s hk (le_trans (Nat.le_add_right _ _) hn)]
  obtain ⟨k'', rfl⟩ : ∃ k'', k = k'' + 2 := ⟨k - 2, by omega⟩
  have hK : k'' + 2 - 1 = k'' + 1 := by omega
  rw [hK] at hn ⊢
  obtain ⟨m, r, hr, hs⟩ : ∃ m r, r < k'' + 1 ∧ s = (k'' + 1) * m + r :=
    ⟨s / (k'' + 1), s % (k'' + 1), Nat.mod_lt _ (by omega), (Nat.div_add_mod _ _).symm⟩
  have hm : s / (k'' + 1) = m := by
    rw [hs, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, add_zero]
  rw [hm] at hn ⊢
  have A := tmk_formula (k'' + 1) m r (by omega)
  have B := tmk_formula k'' m r hr
  have hsm : s + m = (k'' + 1 + 1) * m + r := by rw [hs]; ring
  rw [hsm]
  have key : turanNum ((k'' + 1 + 1) * m + r) (k'' + 1 + 1) = turanNum ((k'' + 1) * m + r) (k'' + 1) + m * ((k'' + 1) * m + r) := by
    nlinarith
  rw [← hs] at key
  rw [key]
  obtain ⟨x, hx⟩ : ∃ x, n - s - m = x := ⟨_, rfl⟩
  have hx2 : n - s = m + x := by omega
  rw [hx, hx2]
  ring

theorem solution (n k s : ℕ) (hk : 2 ≤ k) (hn : s + s / (k - 1) ≤ n) :
    turanNum (s + s / (k - 1)) k + (n - s - s / (k - 1)) * s = gNum n k s :=
  tmk_case_2 n k s hk hn
