-- Prove2me | solution 1 for P2M_GlobalTheory_exists_eval__fraction_of_exists_mod_nilpotent_08ab835b4f0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:33:50.142371+00:00
-- url     : https://prove2.me/submissions/ce09a24e-82ad-4609-87fe-d6b3817ab03f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizedPresentationEvalQuotientFraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
namespace GlobalTheory
theorem _root_.solution : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (J : Ideal R) (n : ℕ), (∀ x ∈ J ^ n, c x = 0) → ∀ (m : ℕ) (r : Fin m → B), (∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q - MvPolynomial.eval₂ c r P ∈ Ideal.map c J) → ∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q = MvPolynomial.eval₂ c r P := by
  intro R B _ _ c J n hn m r hgen
  let S : Subring B :=
    { carrier := {g | ∃ P Q : MvPolynomial (Fin m) R, IsUnit (eval₂ c r Q) ∧ g * eval₂ c r Q = eval₂ c r P}
      mul_mem' := by
        rintro a b ⟨P₁, Q₁, hQ₁, h₁⟩ ⟨P₂, Q₂, hQ₂, h₂⟩
        refine ⟨P₁ * P₂, Q₁ * Q₂, ?_, ?_⟩
        · rw [eval₂_mul]; exact hQ₁.mul hQ₂
        · rw [eval₂_mul, eval₂_mul, ← h₁, ← h₂]; ring
      one_mem' := ⟨1, 1, by simp, by simp⟩
      add_mem' := by
        rintro a b ⟨P₁, Q₁, hQ₁, h₁⟩ ⟨P₂, Q₂, hQ₂, h₂⟩
        refine ⟨P₁ * Q₂ + P₂ * Q₁, Q₁ * Q₂, ?_, ?_⟩
        · rw [eval₂_mul]; exact hQ₁.mul hQ₂
        · rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, ← h₁, ← h₂]; ring
      zero_mem' := ⟨0, 1, by simp, by simp⟩
      neg_mem' := by
        rintro a ⟨P, Q, hQ, h⟩
        refine ⟨-P, Q, hQ, ?_⟩
        rw [eval₂_neg, ← h]; ring }
  have hS : ∀ g, g ∈ S ↔ ∃ P Q : MvPolynomial (Fin m) R,
      IsUnit (eval₂ c r Q) ∧ g * eval₂ c r Q = eval₂ c r P := fun g => Iff.rfl
  have hcS : ∀ a : R, c a ∈ S := fun a => (hS _).2 ⟨C a, 1, by simp, by simp⟩
  set I := Ideal.map c J with hI
  have hdec : ∀ b : B, ∃ s ∈ S, b - s ∈ I := by
    intro b
    obtain ⟨P, Q, hQ, hb⟩ := hgen b
    obtain ⟨u, hu⟩ := hQ
    refine ⟨eval₂ c r P * ↑u⁻¹, (hS _).2 ⟨P, Q, ⟨u, hu⟩, ?_⟩, ?_⟩
    · rw [← hu, mul_assoc, Units.inv_mul, mul_one]
    · have h1 : (↑u⁻¹ : B) * ↑u = 1 := Units.inv_mul u
      have : b - eval₂ c r P * ↑u⁻¹ = ↑u⁻¹ * (b * eval₂ c r Q - eval₂ c r P) := by
        rw [← hu]; linear_combination (-b) * h1
      rw [this]; exact I.mul_mem_left _ hb
  have hstep : ∀ k : ℕ, ∀ x ∈ I ^ k, ∃ s ∈ S, x - s ∈ I ^ (k + 1) := by
    intro k x hx
    have hIk : I ^ k = Ideal.span (c '' ↑(J ^ k)) := by rw [hI, ← Ideal.map_pow]; rfl
    rw [hIk] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, -, rfl⟩ := hy
      exact ⟨c j, hcS j, by simp⟩
    | zero => exact ⟨0, S.zero_mem, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, hys⟩ := hy
      obtain ⟨t, ht, hzt⟩ := hz
      refine ⟨s + t, S.add_mem hs ht, ?_⟩
      have := Ideal.add_mem _ hys hzt
      convert this using 1; ring
    | smul b y hy ih =>
      obtain ⟨s, hs, hys⟩ := ih
      obtain ⟨t, ht, hbt⟩ := hdec b
      refine ⟨t * s, S.mul_mem ht hs, ?_⟩
      have hy' : y ∈ I ^ k := hIk ▸ hy
      have h1 : (b - t) * y ∈ I ^ (k + 1) := by
        rw [pow_succ']; exact Ideal.mul_mem_mul hbt hy'
      have h2 : t * (y - s) ∈ I ^ (k + 1) := Ideal.mul_mem_left _ _ hys
      have := Ideal.add_mem _ h1 h2
      rw [smul_eq_mul]
      convert this using 1; ring
  have hall : ∀ k : ℕ, ∀ g : B, ∃ s ∈ S, g - s ∈ I ^ k := by
    intro k
    induction k with
    | zero => intro g; exact ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      intro g
      obtain ⟨s, hs, hgs⟩ := ih g
      obtain ⟨t, ht, hxt⟩ := hstep k _ hgs
      refine ⟨s + t, S.add_mem hs ht, ?_⟩
      convert hxt using 1; ring
  have hIn : I ^ n = ⊥ := by
    rw [hI, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker]
    exact hn x hx
  intro g
  obtain ⟨s, hs, hgs⟩ := hall n g
  rw [hIn, Ideal.mem_bot, sub_eq_zero] at hgs
  exact (hS g).1 (hgs ▸ hs)
end GlobalTheory
