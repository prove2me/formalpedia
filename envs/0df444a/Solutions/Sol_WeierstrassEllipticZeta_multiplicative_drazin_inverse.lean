-- Prove2me | solution 1 for WeierstrassEllipticZeta.multiplicative_drazin_inverse
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T02:38:05.45498+00:00
-- url     : https://prove2.me/submissions/0f47eac3-28e0-4d5b-83d4-d960821ed28c

import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic.Ring



theorem solution
    (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) (d : ℕ)
    (h : ∀ a : A, ∃ b : B,
      f a * b * b = b ∧ (f a) ^ (d + 1) * b = (f a) ^ d) :
    ∃! G : A →*₀ B, ∀ a : A,
      f a * G a * G a = G a ∧ (f a) ^ (d + 1) * G a = (f a) ^ d := by
  classical
  have huniq (a b c : B)
      (hb : a * b * b = b ∧ a ^ (d + 1) * b = a ^ d)
      (hc : a * c * c = c ∧ a ^ (d + 1) * c = a ^ d) : b = c := by
    have hp (x : B) (hx : a * x * x = x) (n : ℕ) : (a * x) ^ n * x = x := by
      induction n with
      | zero => simp only [pow_zero, one_mul]
      | succ n ih => rw [pow_succ, mul_assoc, hx, ih]
    have hf (x y : B) (hx : a * x * x = x)
        (hy : a ^ (d + 1) * y = a ^ d) : x = a * x * y := by
      have hxpow : a ^ d * x ^ (d + 1) = x := by
        rw [pow_succ, ← mul_assoc, ← mul_pow]
        exact hp x hx d
      calc
        x = a ^ d * x ^ (d + 1) := hxpow.symm
        _ = (a ^ (d + 1) * y) * x ^ (d + 1) := by rw [hy]
        _ = a * (a ^ d * x ^ (d + 1)) * y := by rw [pow_succ a]; ring
        _ = a * x * y := by rw [hxpow]
    calc
      b = a * b * c := hf b c hb.1 hc.2
      _ = a * c * b := by ring
      _ = c := (hf c b hc.1 hb.2).symm
  have h' (a : A) : ∃! b : B,
      f a * b * b = b ∧ (f a) ^ (d + 1) * b = (f a) ^ d := by
    obtain ⟨b, hb⟩ := h a
    exact ⟨b, hb, fun c hc => huniq (f a) c b hc hb⟩
  let g : A → B := fun a => (h' a).choose
  have hg (a : A) : f a * g a * g a = g a ∧
      (f a) ^ (d + 1) * g a = (f a) ^ d := (h' a).choose_spec.1
  let G : A →*₀ B := {
    toFun := g
    map_zero' := by
      simpa only [map_zero, zero_mul] using (hg 0).1.symm
    map_one' := by
      simpa only [map_one, one_pow, one_mul] using (hg 1).2
    map_mul' := by
      intro x y
      apply Eq.symm
      apply (h' (x * y)).choose_spec.2 (g x * g y)
      constructor
      · rw [map_mul]
        calc
          (f x * f y) * (g x * g y) * (g x * g y) =
              (f x * g x * g x) * (f y * g y * g y) := by ring
          _ = g x * g y := by rw [(hg x).1, (hg y).1]
      · rw [map_mul, mul_pow, mul_pow]
        calc
          (f x ^ (d + 1) * f y ^ (d + 1)) * (g x * g y) =
              (f x ^ (d + 1) * g x) * (f y ^ (d + 1) * g y) := by ring
          _ = f x ^ d * f y ^ d := by rw [(hg x).2, (hg y).2] }
  refine ⟨G, hg, ?_⟩
  intro H hH
  apply MonoidWithZeroHom.ext
  intro a
  exact (h' a).choose_spec.2 (H a) (hH a)

