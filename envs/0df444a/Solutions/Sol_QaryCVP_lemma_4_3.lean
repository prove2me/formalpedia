-- Prove2me | solution 1 for QaryCVP.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:20:03.58043+00:00
-- url     : https://prove2.me/submissions/928f24e1-1fa6-462f-90d5-fa0d8923b347

import Mathlib

open Finset

variable {G : Type} [AddCommGroup G] [Fintype G]

/-- autocorrelation -/
def Rc (Φ : G → ℝ) (t : G) : ℝ := ∑ s, Φ (s + t) * Φ s

lemma sum_Rc (Φ : G → ℝ) (hΦ : ∑ s, Φ s = 0) : ∑ t, Rc Φ t = 0 := by
  unfold Rc
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro s _
  rw [← Finset.sum_mul]
  have : ∑ t, Φ (s + t) = ∑ t, Φ t := Fintype.sum_equiv (Equiv.addLeft s) _ _ (fun _ => rfl)
  rw [this, hΦ, zero_mul]

lemma sum_Rc_shift (Φ : G → ℝ) (hΦ : ∑ s, Φ s = 0) (x : G) (b : Bool) :
    ∑ t, Rc Φ (x + (if b then t else -t)) = 0 := by
  cases b
  · simp only [Bool.false_eq_true, if_false]
    exact (Fintype.sum_equiv ((Equiv.neg G).trans (Equiv.addLeft x)) (fun t => Rc Φ (x + -t)) (Rc Φ)
      (fun t => rfl)).trans (sum_Rc Φ hΦ)
  · simp only [if_true]
    exact (Fintype.sum_equiv (Equiv.addLeft x) (fun t => Rc Φ (x + t)) (Rc Φ)
      (fun t => rfl)).trans (sum_Rc Φ hΦ)

def sel {ℓ : ℕ} (u : Fin ℓ → Bool) (C : Fin ℓ → G) : G := ∑ i, if u i then C i else 0

lemma sel_add_single {ℓ : ℕ} (u : Fin ℓ → Bool) (C : Fin ℓ → G) (i0 : Fin ℓ) (t : G) :
    sel u (C + (Pi.single i0 t : Fin ℓ → G)) = sel u C + (if u i0 then t else 0) := by
  unfold sel
  have : ∀ i, (if u i then ((C + (Pi.single i0 t : Fin ℓ → G) : Fin ℓ → G)) i else 0) =
      (if u i then C i else 0) + (if u i then (Pi.single i0 t : Fin ℓ → G) i else 0) := by
    intro i; split_ifs <;> simp
  simp_rw [this, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i0]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

lemma sum_shift {ℓ : ℕ} (F : (Fin ℓ → G) → ℝ) (x : Fin ℓ → G) :
    ∑ C, F C = ∑ C, F (C + x) :=
  (Equiv.sum_comp (Equiv.addRight x) F).symm

lemma cross_zero {ℓ : ℕ} (Φ : G → ℝ) (hΦ : ∑ s, Φ s = 0) (u v : Fin ℓ → Bool) (huv : u ≠ v) :
    ∑ C : Fin ℓ → G, Rc Φ (sel v C - sel u C) = 0 := by
  obtain ⟨i0, hi0⟩ : ∃ i, u i ≠ v i := by
    by_contra h; push Not at h; exact huv (funext h)
  obtain ⟨F, hF⟩ : ∃ F : (Fin ℓ → G) → ℝ, F = fun C => Rc Φ (sel v C - sel u C) := ⟨_, rfl⟩
  have hgoal : ∑ C : Fin ℓ → G, Rc Φ (sel v C - sel u C) = ∑ C, F C := by rw [hF]
  rw [hgoal]
  have hshift : ∀ t : G, ∑ C, F C = ∑ C, F (C + (Pi.single i0 t : Fin ℓ → G)) := fun t =>
    sum_shift F ((Pi.single i0 t : Fin ℓ → G))
  have hcard : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have key : (Fintype.card G : ℝ) * ∑ C, F C = 0 := by
    calc (Fintype.card G : ℝ) * ∑ C, F C = ∑ _t : G, ∑ C, F C := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ t : G, ∑ C, F (C + (Pi.single i0 t : Fin ℓ → G)) := Finset.sum_congr rfl (fun t _ => hshift t)
      _ = ∑ C, ∑ t : G, F (C + (Pi.single i0 t : Fin ℓ → G)) := Finset.sum_comm
      _ = ∑ C : Fin ℓ → G, (0:ℝ) := by
          apply Finset.sum_congr rfl; intro C _
          simp only [hF, sel_add_single]
          have : ∀ t : G, sel v C + (if v i0 then t else 0) - (sel u C + (if u i0 then t else 0)) =
              (sel v C - sel u C) + (if v i0 then t else -t) := by
            intro t
            rcases Bool.eq_false_or_eq_true (u i0) with h1 | h1 <;>
            rcases Bool.eq_false_or_eq_true (v i0) with h2 | h2 <;>
            simp only [h1, h2, ne_eq, not_true_eq_false, if_true, if_false,
              Bool.false_eq_true] at hi0 ⊢ <;> abel
          simp_rw [this]
          exact sum_Rc_shift Φ hΦ _ _
      _ = 0 := by simp
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hcard.ne'
  · exact h

theorem solution (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (Φ : G → ℝ)
    (hΦ : ∑ s, Φ s = 0) :
    (∑ C : Fin ℓ → G, ∑ s : G,
        ((∑ u : Fin ℓ → Bool, Φ (s - ∑ i, if u i then C i else 0)) / (2 : ℝ) ^ ℓ) ^ 2) /
      ((Fintype.card G : ℝ) ^ ℓ * Fintype.card G) =
    (1 / 2 : ℝ) ^ ℓ * ((∑ s, Φ s ^ 2) / Fintype.card G) := by
  have hN : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  -- expand
  have hexp : ∀ C : Fin ℓ → G, ∑ s : G, (∑ u : Fin ℓ → Bool, Φ (s - sel u C)) ^ 2 =
      ∑ u : Fin ℓ → Bool, ∑ v : Fin ℓ → Bool, Rc Φ (sel v C - sel u C) := by
    intro C
    simp_rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v _
    unfold Rc
    exact Fintype.sum_equiv (Equiv.subRight (sel v C)) _ _ (fun s => by
      simp only [Equiv.subRight_apply]; congr 2; abel)
  have hdiag : ∀ C : Fin ℓ → G, ∑ u : Fin ℓ → Bool, ∑ v : Fin ℓ → Bool,
      Rc Φ (sel v C - sel u C) = ∑ u : Fin ℓ → Bool, Rc Φ 0 +
        ∑ u : Fin ℓ → Bool, ∑ v ∈ Finset.univ.erase u, Rc Φ (sel v C - sel u C) := by
    intro C
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u), sub_self]
  have htot : ∑ C : Fin ℓ → G, ∑ s : G,
      ((∑ u : Fin ℓ → Bool, Φ (s - ∑ i, if u i then C i else 0)) / (2 : ℝ) ^ ℓ) ^ 2 =
      ((Fintype.card G : ℝ) ^ ℓ * (2 ^ ℓ * Rc Φ 0)) / (2 ^ ℓ) ^ 2 := by
    simp_rw [div_pow, ← Finset.sum_div]
    congr 1
    change ∑ C : Fin ℓ → G, ∑ s : G, (∑ u : Fin ℓ → Bool, Φ (s - sel u C)) ^ 2 = _
    simp_rw [hexp, hdiag]
    rw [Finset.sum_add_distrib]
    have hcross : ∑ C : Fin ℓ → G, ∑ u : Fin ℓ → Bool, ∑ v ∈ Finset.univ.erase u,
        Rc Φ (sel v C - sel u C) = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro u _
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro v hv
      exact cross_zero Φ hΦ u v (Finset.ne_of_mem_erase hv).symm
    rw [hcross, add_zero]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_bool]
  rw [htot]
  have hR : Rc Φ 0 = ∑ s, Φ s ^ 2 := by unfold Rc; simp [sq]
  rw [hR]
  rw [one_div, inv_pow]
  field_simp
