-- Prove2me | solution 1 for RingHom.surjective_of_isAdicComplete_of_le_map_sup_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/77dfafe3-f781-5aac-8fb1-4800d6a8e355

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_surjective_of_isAdicComplete_of_le_map_sup_sq

set_option autoImplicit false

universe u

open IsLocalRing

theorem solution
    {P R : Type u} [CommRing P] [CommRing R] (J : Ideal P) [IsAdicComplete J P] (I : Ideal R) [IsHausdorff I R]
    (φ : P →+* R) (hJ : Ideal.map φ J ≤ I)
    (h0 : ∀ r : R, ∃ p : P, r - φ p ∈ I)
    (h1 : I ≤ Ideal.map φ J ⊔ I ^ 2) :
    Function.Surjective φ := by
  classical

  have hJn : ∀ n : ℕ, Ideal.map φ (J ^ n) ≤ I ^ n := fun n => by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono hJ n

  have hA : ∀ (n : ℕ) (y : R), y ∈ Ideal.map φ (J ^ n) → ∃ j ∈ J ^ n, y - φ j ∈ I ^ (n + 1) := by
    intro n y hy
    replace hy : y ∈ Submodule.span R (⇑φ '' ↑(J ^ n)) := hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact ⟨j, hj, by simp⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨j₁, hj₁, h₁⟩ := hx
      obtain ⟨j₂, hj₂, h₂⟩ := hy
      refine ⟨j₁ + j₂, add_mem hj₁ hj₂, ?_⟩
      have : x + y - φ (j₁ + j₂) = (x - φ j₁) + (y - φ j₂) := by rw [map_add]; ring
      rw [this]; exact add_mem h₁ h₂
    | smul a x _ hx =>
      obtain ⟨j, hj, h⟩ := hx
      obtain ⟨p, hp⟩ := h0 a
      refine ⟨p * j, Ideal.mul_mem_left _ _ hj, ?_⟩
      have : a • x - φ (p * j) = a * (x - φ j) + (a - φ p) * φ j := by
        rw [smul_eq_mul, map_mul]; ring
      rw [this]
      refine add_mem (Ideal.mul_mem_left _ _ h) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hp (hJn n (Ideal.mem_map_of_mem φ hj))

  have hA1 : ∀ a ∈ I, ∃ j ∈ J, a - φ j ∈ I ^ 2 := by
    intro a ha
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (h1 ha)
    obtain ⟨j, hj, h⟩ := hA 1 y (by simpa using hy)
    refine ⟨j, by simpa using hj, ?_⟩
    have : y + z - φ j = (y - φ j) + z := by ring
    rw [this]; exact add_mem (by simpa using h) hz

  have hB : ∀ (n : ℕ) (x : R), x ∈ I ^ n → ∃ j ∈ J ^ n, x - φ j ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro x _
      obtain ⟨p, hp⟩ := h0 x
      exact ⟨p, by simp, by simpa using hp⟩
    | succ n ih =>
      intro x hx
      rw [pow_succ'] at hx
      induction hx using Submodule.mul_induction_on' with
      | mem_mul_mem a ha x hx =>
        obtain ⟨j₁, hj₁, h₁⟩ := hA1 a ha
        obtain ⟨j, hj, h⟩ := ih x hx
        refine ⟨j₁ * j, ?_, ?_⟩
        · rw [pow_succ']; exact Ideal.mul_mem_mul hj₁ hj
        have : a * x - φ (j₁ * j) = a * (x - φ j) + (a - φ j₁) * φ j := by rw [map_mul]; ring
        rw [this]
        refine add_mem ?_ ?_
        · rw [pow_succ']; exact Ideal.mul_mem_mul ha h
        · rw [show n + 1 + 1 = 2 + n by ring, pow_add]
          exact Ideal.mul_mem_mul h₁ (hJn n (Ideal.mem_map_of_mem φ hj))
      | add x _ y _ hx hy =>
        obtain ⟨j₁, hj₁, h₁⟩ := hx
        obtain ⟨j₂, hj₂, h₂⟩ := hy
        refine ⟨j₁ + j₂, add_mem hj₁ hj₂, ?_⟩
        have : x + y - φ (j₁ + j₂) = (x - φ j₁) + (y - φ j₂) := by rw [map_add]; ring
        rw [this]; exact add_mem h₁ h₂

  have eP : ∀ n : ℕ, (J ^ n • ⊤ : Submodule P P) = J ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  have eR : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]

  intro r
  have hnext : ∀ (n : ℕ) (p : P), r - φ p ∈ I ^ (n + 1) →
      ∃ p' : P, p' - p ∈ J ^ (n + 1) ∧ r - φ p' ∈ I ^ (n + 1 + 1) := by
    intro n p hp
    obtain ⟨j, hj, h⟩ := hB (n + 1) _ hp
    refine ⟨p + j, by simpa using hj, ?_⟩
    have : r - φ (p + j) = r - φ p - φ j := by rw [map_add]; ring
    rwa [this]
  choose nxt hnxt using hnext
  obtain ⟨p₀, hp₀⟩ := h0 r
  let q : (n : ℕ) → {p : P // r - φ p ∈ I ^ (n + 1)} := fun n =>
    Nat.rec (motive := fun n => {p : P // r - φ p ∈ I ^ (n + 1)}) ⟨p₀, by simpa using hp₀⟩
      (fun n qn => ⟨nxt n qn.1 qn.2, (hnxt n qn.1 qn.2).2⟩) n
  have hq_succ : ∀ n, (q (n + 1)).1 - (q n).1 ∈ J ^ (n + 1) := fun n => (hnxt n (q n).1 (q n).2).1
  let f : ℕ → P := fun n => (q n).1
  have hf_succ : ∀ n, f n ≡ f (n + 1) [SMOD (J ^ (n + 1) • ⊤ : Submodule P P)] := fun n => by
    rw [SModEq.sub_mem, eP, ← neg_mem_iff, neg_sub]; exact hq_succ n
  have hf : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (J ^ m • ⊤ : Submodule P P)] := by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    induction k with
    | zero => exact SModEq.rfl
    | succ k ih =>
      refine (ih (Nat.le_add_right m k)).trans ?_
      rw [← add_assoc]
      exact (hf_succ (m + k)).mono
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)))
  obtain ⟨L, hL⟩ := (IsAdicComplete.toIsPrecomplete (I := J) (M := P)).prec hf
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine (‹IsHausdorff I R›).haus _ fun n => ?_
  rw [SModEq.zero, eR]
  have h₁ : f n - L ∈ J ^ n := by rw [← eP, ← SModEq.sub_mem]; exact hL n
  have h₂ : r - φ (f n) ∈ I ^ n := Ideal.pow_le_pow_right (Nat.le_succ n) (q n).2
  have : φ L - r = -(φ (f n - L) + (r - φ (f n))) := by rw [map_sub]; ring
  rw [this]
  exact neg_mem (add_mem (hJn n (Ideal.mem_map_of_mem φ h₁)) h₂)

end S_RingHom_surjective_of_isAdicComplete_of_le_map_sup_sq
end P2MW
export P2MW.S_RingHom_surjective_of_isAdicComplete_of_le_map_sup_sq (solution)
