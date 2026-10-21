-- Prove2me | solution 1 for RegevLWE.SubsetSum.expected_l2_norm
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:03:44.660756+00:00
-- url     : https://prove2.me/submissions/e75e1378-e554-4c67-8c34-cc155fe88ba6

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

lemma RLS_cs {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {l : ℕ}
    (g : Fin l → G) :
    statDistUniform g ≤
        Real.sqrt (Fintype.card G) * Real.sqrt (∑ h, (P g h - 1 / (Fintype.card G : ℝ)) ^ 2) ∧
      ∑ h, (P g h - 1 / (Fintype.card G : ℝ)) ^ 2 = ∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ) := by
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  constructor
  · have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset G)
      (fun h => |P g h - 1 / (Fintype.card G : ℝ)|) (fun _ => (1 : ℝ))
    simp only [mul_one, sq_abs, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    unfold statDistUniform
    rw [mul_comm]
    exact this
  · have e : ∀ h, (P g h - 1 / (Fintype.card G : ℝ)) ^ 2 =
        P g h ^ 2 - 2 * (1 / (Fintype.card G : ℝ)) * P g h + (1 / (Fintype.card G : ℝ)) ^ 2 :=
      fun h => by ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, RLS_P_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring

lemma RLS_el2 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (l : ℕ) :
    expectG (fun g : Fin l → G => ∑ h, P g h ^ 2) ≤
      1 / (2 : ℝ) ^ l + 1 / (Fintype.card G : ℝ) := by
  unfold expectG
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) < (Fintype.card G : ℝ) ^ l := pow_pos hG l
  have hN : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have h1 : ∀ g : Fin l → G, ∑ h, P g h ^ 2 =
      (∑ bb : (Fin l → Bool) × (Fin l → Bool),
        if subsetSum g bb.1 = subsetSum g bb.2 then (1 : ℝ) else 0) / ((2 : ℝ) ^ l) ^ 2 := by
    intro g
    rw [RLS_P_sq, Finset.sum_boole]
  rw [Finset.sum_congr rfl (fun g _ => h1 g), ← Finset.sum_div, Finset.sum_comm]
  have hdiag : (∑ bb : (Fin l → Bool) × (Fin l → Bool), if bb.1 = bb.2 then (1 : ℝ) else 0) =
      (2 : ℝ) ^ l := by
    rw [Finset.sum_boole]
    have : (univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) => bb.1 = bb.2) =
        (univ : Finset (Fin l → Bool)).diag := by
      ext ⟨u, v⟩
      simp [Finset.mem_diag]
    rw [this, Finset.diag_card]
    simp
  have h2 : ∀ bb : (Fin l → Bool) × (Fin l → Bool),
      (∑ g : Fin l → G, if subsetSum g bb.1 = subsetSum g bb.2 then (1 : ℝ) else 0) /
          (Fintype.card G : ℝ) ^ l ≤
        (if bb.1 = bb.2 then (1 : ℝ) else 0) + 1 / (Fintype.card G : ℝ) := by
    intro bb
    rw [Finset.sum_boole]
    by_cases hbb : bb.1 = bb.2
    · have : (univ.filter fun g : Fin l → G => subsetSum g bb.1 = subsetSum g bb.2) = univ := by
        ext g; simp [hbb]
      rw [this, if_pos hbb]
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
      rw [div_self hM.ne']
      have : (0 : ℝ) ≤ 1 / (Fintype.card G : ℝ) := by positivity
      linarith
    · rw [RLS_coll bb.1 bb.2 hbb, if_neg hbb]
      simp
  have h3 : (∑ bb : (Fin l → Bool) × (Fin l → Bool),
      ∑ g : Fin l → G, if subsetSum g bb.1 = subsetSum g bb.2 then (1 : ℝ) else 0) /
        (Fintype.card G : ℝ) ^ l ≤ (2 : ℝ) ^ l + ((2 : ℝ) ^ l) ^ 2 / (Fintype.card G : ℝ) := by
    rw [Finset.sum_div]
    calc _ ≤ ∑ bb : (Fin l → Bool) × (Fin l → Bool),
          ((if bb.1 = bb.2 then (1 : ℝ) else 0) + 1 / (Fintype.card G : ℝ)) :=
          Finset.sum_le_sum fun bb _ => h2 bb
      _ = _ := by
        rw [Finset.sum_add_distrib, hdiag]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
          Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring
  rw [div_div, mul_comm, ← div_div]
  calc _ ≤ ((2 : ℝ) ^ l + ((2 : ℝ) ^ l) ^ 2 / (Fintype.card G : ℝ)) / ((2 : ℝ) ^ l) ^ 2 :=
        div_le_div_of_nonneg_right h3 (by positivity)
    _ = _ := by field_simp

theorem solution {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (l : ℕ) :
    expectG (fun g : Fin l → G => ∑ h, P g h ^ 2) ≤
      1 / (2 : ℝ) ^ l + 1 / (Fintype.card G : ℝ) := RLS_el2 l
