-- Prove2me | solution 1 for RegevLWE.SubsetSum.claim_5_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:03:45.75099+00:00
-- url     : https://prove2.me/submissions/453d4604-60d7-4a22-9c4a-6333bf02513f

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
    expectG (fun g : Fin l → G => statDistUniform g) ≤
        Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l) ∧
      ((univ.filter fun g : Fin l → G =>
            Real.sqrt (Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l)) < statDistUniform g).card : ℝ) /
          (Fintype.card G : ℝ) ^ l ≤
        Real.sqrt (Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l)) := by
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) < (Fintype.card G : ℝ) ^ l := pow_pos hN l
  have h2l : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have hx : ∀ g : Fin l → G, 0 ≤ ∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ) := fun g => by
    rw [← (RLS_cs g).2]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hΔ : ∀ g : Fin l → G, statDistUniform g ≤
      Real.sqrt (Fintype.card G) * Real.sqrt (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ)) :=
    fun g => by
      have := RLS_cs g
      rw [this.2] at this
      exact this.1
  have hΔ0 : ∀ g : Fin l → G, 0 ≤ statDistUniform g := fun g =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hEl := RLS_el2 (G := G) l
  unfold expectG at hEl ⊢
  have hsumS : ∑ g : Fin l → G, ∑ h, P g h ^ 2 ≤
      (Fintype.card G : ℝ) ^ l * (1 / (2 : ℝ) ^ l + 1 / (Fintype.card G : ℝ)) :=
    by rw [mul_comm]; exact (div_le_iff₀ hM).1 hEl
  have hcard : ((Finset.univ : Finset (Fin l → G)).card : ℝ) = (Fintype.card G : ℝ) ^ l := by
    simp
  have hsumx : ∑ g : Fin l → G, (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ)) ≤
      (Fintype.card G : ℝ) ^ l / (2 : ℝ) ^ l := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    have : (Fintype.card G : ℝ) ^ l / (2 : ℝ) ^ l =
        (Fintype.card G : ℝ) ^ l * (1 / (2 : ℝ) ^ l + 1 / (Fintype.card G : ℝ)) -
          (Fintype.card G : ℝ) ^ l * (1 / (Fintype.card G : ℝ)) := by ring
    rw [this]
    linarith
  have hsq : (∑ g : Fin l → G, statDistUniform g) ^ 2 ≤
      (Fintype.card G : ℝ) * (Fintype.card G : ℝ) ^ l * ((Fintype.card G : ℝ) ^ l / (2 : ℝ) ^ l) := by
    calc (∑ g : Fin l → G, statDistUniform g) ^ 2
        ≤ (∑ g : Fin l → G, Real.sqrt (Fintype.card G) *
            Real.sqrt (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun g _ => hΔ0 g)
            (Finset.sum_le_sum fun g _ => hΔ g) 2
      _ = (Fintype.card G : ℝ) *
            (∑ g : Fin l → G, Real.sqrt (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ))) ^ 2 := by
          rw [← Finset.mul_sum, mul_pow, Real.sq_sqrt hN.le]
      _ ≤ (Fintype.card G : ℝ) * ((∑ g : Fin l → G, (1 : ℝ) ^ 2) *
            ∑ g : Fin l → G, Real.sqrt (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ)) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hN.le
          have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin l → G))
            (fun _ => (1 : ℝ)) (fun g => Real.sqrt (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ)))
          simpa using this
      _ ≤ (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) ^ l *
            ((Fintype.card G : ℝ) ^ l / (2 : ℝ) ^ l)) := by
          apply mul_le_mul_of_nonneg_left _ hN.le
          have e1 : ∑ g : Fin l → G, (1 : ℝ) ^ 2 = (Fintype.card G : ℝ) ^ l := by simp
          have e2 : ∑ g : Fin l → G,
              Real.sqrt (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ)) ^ 2 =
              ∑ g : Fin l → G, (∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ)) :=
            Finset.sum_congr rfl fun g _ => Real.sq_sqrt (hx g)
          rw [e1, e2]
          exact mul_le_mul_of_nonneg_left hsumx hM.le
      _ = _ := by ring
  have hE : (∑ g : Fin l → G, statDistUniform g) ≤
      (Fintype.card G : ℝ) ^ l * Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l) := by
    have hnn : 0 ≤ (∑ g : Fin l → G, statDistUniform g) :=
      Finset.sum_nonneg fun g _ => hΔ0 g
    have : (∑ g : Fin l → G, statDistUniform g) ≤
        Real.sqrt (((Fintype.card G : ℝ) ^ l) ^ 2 * ((Fintype.card G : ℝ) / 2 ^ l)) := by
      apply le_trans (le_abs_self _) (Real.abs_le_sqrt _)
      calc _ ≤ _ := hsq
        _ = _ := by ring
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq hM.le] at this
  constructor
  · rw [div_le_iff₀ hM, mul_comm]
    exact hE
  · set t := Real.sqrt (Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l)) with ht
    have hq : 0 < (Fintype.card G : ℝ) / 2 ^ l := by positivity
    have htpos : 0 < t := Real.sqrt_pos.2 (Real.sqrt_pos.2 hq)
    have ht2 : t ^ 2 = Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have hcnt : ((univ.filter fun g : Fin l → G => t < statDistUniform g).card : ℝ) * t ≤
        ∑ g : Fin l → G, statDistUniform g := by
      have h1 := Finset.card_nsmul_le_sum (univ.filter fun g : Fin l → G => t < statDistUniform g)
        (fun g => statDistUniform g) t (fun g hg => (Finset.mem_filter.1 hg).2.le)
      rw [nsmul_eq_mul] at h1
      exact h1.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun g _ _ => hΔ0 g))
    rw [div_le_iff₀ hM]
    have : ((univ.filter fun g : Fin l → G => t < statDistUniform g).card : ℝ) * t ≤
        (Fintype.card G : ℝ) ^ l * t ^ 2 := by rw [ht2]; exact hcnt.trans hE
    have h3 : ((univ.filter fun g : Fin l → G => t < statDistUniform g).card : ℝ) * t ≤
        (t * (Fintype.card G : ℝ) ^ l) * t := by nlinarith [this]
    exact le_of_mul_le_mul_right h3 htpos
