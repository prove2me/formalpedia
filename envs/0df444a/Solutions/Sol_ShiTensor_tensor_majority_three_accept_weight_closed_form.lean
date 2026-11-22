-- Prove2me | solution 1 for ShiTensor.tensor_majority_three_accept_weight_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T08:03:52.128696+00:00
-- url     : https://prove2.me/submissions/f6df295e-7008-49e5-b199-096bfece28a6

import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

open ShiShallow ShiTensor

private theorem shiMjp_ite_mul (c : Prop) [Decidable c] (W : ℝ) :
    (if c then W else 0) = (if c then (1 : ℝ) else 0) * W := by
  by_cases hc : c <;> simp [hc]

private theorem shiMjp_sum_true {n : ℕ} (ζ : QState n)
    (hζ : ∑ a : Bits n, ‖ζ a‖ ^ 2 = 1) :
    (∑ a : Bits n, (if (true : Bool) then ‖ζ a‖ ^ 2 else 0)) = 1 :=
  calc (∑ a : Bits n, (if (true : Bool) then ‖ζ a‖ ^ 2 else 0))
      = ∑ a : Bits n, ‖ζ a‖ ^ 2 := Finset.sum_congr rfl (fun a _ => by simp)
    _ = 1 := hζ

theorem solution (M P Q : ℕ) (p : ℝ)
    (ψ : QState M) (φ : QState P) (χ : QState Q)
    (f : Bits M → Bool) (g : Bits P → Bool) (h : Bits Q → Bool)
    (hJoint : ∀ (m n : ℕ) (a : QState m) (b : QState n)
      (u : Bits m → Bool) (v : Bits n → Bool),
      ∑ y : Bits (m + n), (if u (leftBits y) && v (rightBits y)
          then ‖tensor a b y‖ ^ 2 else 0)
        = (∑ s : Bits m, (if u s then ‖a s‖ ^ 2 else 0))
          * ∑ t : Bits n, (if v t then ‖b t‖ ^ 2 else 0))
    (hIE : ∀ b1 b2 b3 : Bool,
      (if 2 ≤ (if b1 then (1 : ℕ) else 0) + (if b2 then (1 : ℕ) else 0)
            + (if b3 then (1 : ℕ) else 0) then (1 : ℝ) else 0)
        = (if b1 then (1 : ℝ) else 0) * (if b2 then (1 : ℝ) else 0)
          + (if b2 then (1 : ℝ) else 0) * (if b3 then (1 : ℝ) else 0)
          + (if b3 then (1 : ℝ) else 0) * (if b1 then (1 : ℝ) else 0)
          - 2 * ((if b1 then (1 : ℝ) else 0) * (if b2 then (1 : ℝ) else 0)
              * (if b3 then (1 : ℝ) else 0)))
    (hfp : ∑ a : Bits M, (if f a then ‖ψ a‖ ^ 2 else 0) = p)
    (hgp : ∑ b : Bits P, (if g b then ‖φ b‖ ^ 2 else 0) = p)
    (hhp : ∑ c : Bits Q, (if h c then ‖χ c‖ ^ 2 else 0) = p)
    (hψ1 : ∑ a : Bits M, ‖ψ a‖ ^ 2 = 1)
    (hφ1 : ∑ b : Bits P, ‖φ b‖ ^ 2 = 1)
    (hχ1 : ∑ c : Bits Q, ‖χ c‖ ^ 2 = 1) :
    ∑ y : Bits (M + (P + Q)),
      (if 2 ≤ (if f (leftBits y) then (1 : ℕ) else 0)
            + (if g (leftBits (rightBits y)) then (1 : ℕ) else 0)
            + (if h (rightBits (rightBits y)) then (1 : ℕ) else 0)
        then ‖tensor ψ (tensor φ χ) y‖ ^ 2 else 0)
      = 3 * p ^ 2 - 2 * p ^ 3 := by
  have factor3 : ∀ (u : Bits M → Bool) (v : Bits P → Bool) (w : Bits Q → Bool),
      (∑ y : Bits (M + (P + Q)),
        (if u (leftBits y) && (v (leftBits (rightBits y)) && w (rightBits (rightBits y)))
          then ‖tensor ψ (tensor φ χ) y‖ ^ 2 else 0))
        = (∑ s : Bits M, (if u s then ‖ψ s‖ ^ 2 else 0))
          * ((∑ t : Bits P, (if v t then ‖φ t‖ ^ 2 else 0))
            * ∑ r : Bits Q, (if w r then ‖χ r‖ ^ 2 else 0)) := by
    intro u v w
    have s1 := hJoint M (P + Q) ψ (tensor φ χ) u
      (fun z => v (leftBits z) && w (rightBits z))
    have s2 := hJoint P Q φ χ v w
    first
      | (rw [s2] at s1; exact s1)
      | (rw [s1, s2]; done)
      | (simp only [s1, s2]; done)
  have key : ∀ y : Bits (M + (P + Q)),
      (if 2 ≤ (if f (leftBits y) then (1 : ℕ) else 0)
            + (if g (leftBits (rightBits y)) then (1 : ℕ) else 0)
            + (if h (rightBits (rightBits y)) then (1 : ℕ) else 0)
        then ‖tensor ψ (tensor φ χ) y‖ ^ 2 else 0)
        = (if f (leftBits y) && (g (leftBits (rightBits y)) && true)
              then ‖tensor ψ (tensor φ χ) y‖ ^ 2 else 0)
          + (if true && (g (leftBits (rightBits y)) && h (rightBits (rightBits y)))
              then ‖tensor ψ (tensor φ χ) y‖ ^ 2 else 0)
          + (if f (leftBits y) && (true && h (rightBits (rightBits y)))
              then ‖tensor ψ (tensor φ χ) y‖ ^ 2 else 0)
          - 2 * (if f (leftBits y) && (g (leftBits (rightBits y))
                  && h (rightBits (rightBits y)))
              then ‖tensor ψ (tensor φ χ) y‖ ^ 2 else 0) := by
    intro y
    have hmul := shiMjp_ite_mul
      (2 ≤ (if f (leftBits y) then (1 : ℕ) else 0)
          + (if g (leftBits (rightBits y)) then (1 : ℕ) else 0)
          + (if h (rightBits (rightBits y)) then (1 : ℕ) else 0))
      (‖tensor ψ (tensor φ χ) y‖ ^ 2)
    have hie := hIE (f (leftBits y)) (g (leftBits (rightBits y)))
      (h (rightBits (rightBits y)))
    rw [hmul, hie]
    first
      | (generalize f (leftBits y) = b1
         generalize g (leftBits (rightBits y)) = b2
         generalize h (rightBits (rightBits y)) = b3
         cases b1 <;> cases b2 <;> cases b3 <;> norm_num <;> ring
         done)
      | (generalize f (leftBits y) = b1
         generalize g (leftBits (rightBits y)) = b2
         generalize h (rightBits (rightBits y)) = b3
         cases b1 <;> cases b2 <;> cases b3 <;> simp <;> ring
         done)
      | (cases hb1 : f (leftBits y) <;> cases hb2 : g (leftBits (rightBits y)) <;>
          cases hb3 : h (rightBits (rightBits y)) <;> simp [hb1, hb2, hb3] <;> ring
         done)
  simp only [key]
  first
    | rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]
    | simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [factor3 f g (fun _ => true), factor3 (fun _ => true) g h,
    factor3 f (fun _ => true) h, factor3 f g h]
  rw [hfp, hgp, hhp, shiMjp_sum_true ψ hψ1, shiMjp_sum_true φ hφ1, shiMjp_sum_true χ hχ1]
  ring
