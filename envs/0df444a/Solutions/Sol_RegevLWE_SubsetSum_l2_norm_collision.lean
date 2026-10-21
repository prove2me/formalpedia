-- Prove2me | solution 1 for RegevLWE.SubsetSum.l2_norm_collision
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:49:28.817442+00:00
-- url     : https://prove2.me/submissions/940c39d6-367c-4327-a687-01d660a9870c

import Mathlib
import Definitions.Def_RegevLWE_SubsetSum_Basic

set_option autoImplicit false
open Finset hiding subsetSum
open RegevLWE.SubsetSum

lemma RLS_coll {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {l : ℕ}
    (b b' : Fin l → Bool) (hb : b ≠ b') :
    ((univ.filter fun g : Fin l → G => subsetSum g b = subsetSum g b').card : ℝ) /
        (Fintype.card G : ℝ) ^ l = 1 / (Fintype.card G : ℝ) := by
  let φ : (Fin l → G) →+ G :=
    { toFun := fun g => subsetSum g b - subsetSum g b'
      map_zero' := by simp [subsetSum]
      map_add' := by
        intro g g'
        simp only [subsetSum, Pi.add_apply]
        have h1 : ∀ c : Fin l → Bool, ∑ i, (if c i then g i + g' i else 0) =
            ∑ i, (if c i then g i else 0) + ∑ i, (if c i then g' i else 0) := by
          intro c
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs <;> simp
        rw [h1 b, h1 b']; abel }
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ b' i := by
    by_contra h
    push_neg at h
    exact hb (funext h)
  have key : ∀ (c : Fin l → Bool) (x : G),
      subsetSum (Pi.single i x : Fin l → G) c = if c i then x else 0 := by
    intro c x
    unfold subsetSum
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  have hsurj : ∀ h : G, ∃ g, φ g = h := by
    intro h
    cases hbi : b i <;> cases hbi' : b' i
    · exact absurd (hbi.trans hbi'.symm) hi
    · refine ⟨Pi.single i (-h), ?_⟩
      show subsetSum _ b - subsetSum _ b' = h
      rw [key, key, hbi, hbi']; simp
    · refine ⟨Pi.single i h, ?_⟩
      show subsetSum _ b - subsetSum _ b' = h
      rw [key, key, hbi, hbi']; simp
    · exact absurd (hbi.trans hbi'.symm) hi
  have hfib : ∀ h : G, (univ.filter fun g : Fin l → G => φ g = h).card =
      (univ.filter fun g : Fin l → G => φ g = 0).card := fun h =>
    AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj h) (hsurj 0)
  have htot : Fintype.card G * (univ.filter fun g : Fin l → G => φ g = 0).card =
      Fintype.card G ^ l := by
    have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin l → G)))
      (t := (univ : Finset G)) (f := φ) (by simp)
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at this
    rw [this, Finset.sum_congr rfl (fun h _ => hfib h)]
    simp
  have hset : (univ.filter fun g : Fin l → G => subsetSum g b = subsetSum g b') =
      (univ.filter fun g : Fin l → G => φ g = 0) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show _ ↔ subsetSum g b - subsetSum g b' = 0
    rw [sub_eq_zero]
  rw [hset]
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rw [div_eq_div_iff (pow_pos hG l).ne' hG.ne']
  have := congrArg (fun n : ℕ => (n : ℝ)) htot
  simp only [Nat.cast_mul, Nat.cast_pow] at this
  linarith

lemma RLS_P_sum {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {l : ℕ}
    (g : Fin l → G) : ∑ h, P g h = 1 := by
  unfold P
  rw [← Finset.sum_div]
  have : ∑ h : G, ((univ.filter fun b : Fin l → Bool => subsetSum g b = h).card : ℝ) = 2 ^ l := by
    have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin l → Bool)))
      (t := (univ : Finset G)) (f := fun b => subsetSum g b) (by simp)
    have h2 : ((univ : Finset (Fin l → Bool)).card : ℝ) = 2 ^ l := by simp
    rw [← h2, this]
    push_cast
    rfl
  rw [this]
  exact div_self (by positivity)

lemma RLS_P_sq {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {l : ℕ}
    (g : Fin l → G) : ∑ h, P g h ^ 2 =
      ((univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
            subsetSum g bb.1 = subsetSum g bb.2).card : ℝ) / ((2 : ℝ) ^ l) ^ 2 := by
  have hc : (univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
            subsetSum g bb.1 = subsetSum g bb.2).card =
      ∑ h : G, ((univ.filter fun b : Fin l → Bool => subsetSum g b = h).card) ^ 2 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun bb : (Fin l → Bool) × (Fin l → Bool) =>
      subsetSum g bb.1) (t := (univ : Finset G)) (by simp)]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [sq, ← Finset.card_product]
    congr 1
    ext ⟨b, b'⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1 ▸ h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.trans h2.symm, h1⟩
  rw [hc]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h _ => ?_
  unfold P
  rw [div_pow]

theorem solution {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {l : ℕ}
    (g : Fin l → G) :
    ∑ h, P g h ^ 2 =
        ((univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
            subsetSum g bb.1 = subsetSum g bb.2).card : ℝ) / ((2 : ℝ) ^ l) ^ 2 ∧
      ((univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
            subsetSum g bb.1 = subsetSum g bb.2).card : ℝ) / ((2 : ℝ) ^ l) ^ 2 ≤
        1 / (2 : ℝ) ^ l +
          ((univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
              bb.1 ≠ bb.2 ∧ subsetSum g bb.1 = subsetSum g bb.2).card : ℝ) /
            (((2 : ℝ) ^ l) ^ 2 - (2 : ℝ) ^ l) := by
  refine ⟨RLS_P_sq g, ?_⟩
  set c := (univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
            subsetSum g bb.1 = subsetSum g bb.2).card with hc
  set c' := (univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
              bb.1 ≠ bb.2 ∧ subsetSum g bb.1 = subsetSum g bb.2).card with hc'
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
            subsetSum g bb.1 = subsetSum g bb.2)) (fun bb => bb.1 = bb.2)
  have h1 : ((univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
            subsetSum g bb.1 = subsetSum g bb.2).filter (fun bb => bb.1 = bb.2)) =
      (univ : Finset (Fin l → Bool)).diag := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_diag]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; subst h; exact ⟨rfl, rfl⟩
  have h2 : ((univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
            subsetSum g bb.1 = subsetSum g bb.2).filter (fun bb => ¬ bb.1 = bb.2)) =
      (univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
              bb.1 ≠ bb.2 ∧ subsetSum g bb.1 = subsetSum g bb.2) := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [h1, h2, Finset.diag_card] at hsplit
  have hN : (univ : Finset (Fin l → Bool)).card = 2 ^ l := by simp
  rw [hN] at hsplit
  have hcle : c ≤ (2 ^ l) ^ 2 := by
    have := Finset.card_filter_le (univ : Finset ((Fin l → Bool) × (Fin l → Bool)))
      (fun bb => subsetSum g bb.1 = subsetSum g bb.2)
    have h3 : (univ : Finset ((Fin l → Bool) × (Fin l → Bool))).card = (2 ^ l) ^ 2 := by
      simp [Finset.card_univ, Fintype.card_prod, sq]
    omega
  have hcR : (c : ℝ) = (2 : ℝ) ^ l + c' := by exact_mod_cast hsplit.symm.trans (by rfl)
  have hcleR : (c : ℝ) ≤ ((2 : ℝ) ^ l) ^ 2 := by exact_mod_cast hcle
  set N : ℝ := (2 : ℝ) ^ l with hNdef
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hNpos : 0 < N := by linarith
  have hc'0 : (0 : ℝ) ≤ c' := Nat.cast_nonneg _
  rw [hcR]
  rcases (sub_nonneg.2 (by nlinarith : N ≤ N ^ 2)).eq_or_lt with hz | hpos
  · have hc'z : (c' : ℝ) = 0 := by linarith
    have hN1' : N = 1 := by nlinarith
    rw [← hz, hc'z, hN1']
    norm_num
  · calc (N + c') / N ^ 2 = 1 / N + c' / N ^ 2 := by field_simp
      _ ≤ 1 / N + c' / (N ^ 2 - N) := by
        gcongr
        linarith
